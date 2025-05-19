// Copyright 2022 Charles Lohr, you may use this file or any portions herein under any of the BSD, MIT, or CC0 licenses.

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <windows.h>
#include <ctype.h>
#include <winuser.h>

#include "default64mbdtc.h"

// Just default RAM amount is 64MB.
uint32_t ram_amt = 64*1024*1024;
int fail_on_all_faults = 0;

static BOOL IsHover();
static int64_t SimpleReadNumberInt( const char * number, int64_t defaultNumber );
static uint64_t GetTimeMicroseconds();
static void ResetKeyboardInput();
static void CaptureKeyboardInput();
static uint32_t HandleException( uint32_t ir, uint32_t retval );
static uint32_t HandleControlStore( uint32_t addy, uint32_t val );
static uint32_t HandleControlLoad( uint32_t addy );
static void HandleOtherCSRWrite( uint8_t * image, uint16_t csrno, uint32_t value );
static int32_t HandleOtherCSRRead( uint8_t * image, uint16_t csrno );
static void MiniSleep();
static int IsKBHit();
static int ReadKBByte();

// This is the functionality we want to override in the emulator.
//  think of this as the way the emulator's processor is connected to the outside world.
#define MINIRV32WARN( x... ) printf( x );
#define MINIRV32_DECORATE  static
#define MINI_RV32_RAM_SIZE ram_amt
#define MINIRV32_IMPLEMENTATION
#define MINIRV32_POSTEXEC( pc, ir, retval ) { if( retval > 0 ) { if( fail_on_all_faults ) { printf( "FAULT\n" ); return 3; } else retval = HandleException( ir, retval ); } }
#define MINIRV32_HANDLE_MEM_STORE_CONTROL( addy, val ) if( HandleControlStore( addy, val ) ) return val;
#define MINIRV32_HANDLE_MEM_LOAD_CONTROL( addy, rval ) rval = HandleControlLoad( addy );
#define MINIRV32_OTHERCSR_WRITE( csrno, value ) HandleOtherCSRWrite( image, csrno, value );
#define MINIRV32_OTHERCSR_READ( csrno, value ) value = HandleOtherCSRRead( image, csrno );

#include "mini-rv32ima.h"

uint8_t * ram_image = 0;
struct MiniRV32IMAState * core;
static HDC g_hdc;
static int g_line;
static int g_column;
static int g_char_width, g_char_height;
static HFONT g_font;
static POINT g_cursor;
// Back-buffer DC and bitmap for fast redraw
static HDC     g_memdc;
static HBITMAP g_membmp;
static int g_screen_width;
static int g_screen_height;
static int g_display_width;
static int g_display_height;
static int g_max_lines;
// Overlay text buffer and dimensions
static char *screen_buf = NULL;
static int   g_max_cols = 0;
const char * kernel_command_line = 0;

static void DumpState( struct MiniRV32IMAState * core, uint8_t * ram_image );

void print_text_gdi(const char *s) {
    static int ansi_state = 0; // 0=normal,1=seen ESC,2=in CSI
    for (const char *p = s; *p; p++) {
        unsigned char c = *p;
        if (ansi_state == 0) {
            if (c == '\x1b') { ansi_state = 1; continue; }
        } else if (ansi_state == 1) {
            if (c == '[') { ansi_state = 2; continue; }
            ansi_state = 0;
            // fallthrough to normal handling of c
        } else if (ansi_state == 2) {
            if (c >= 0x40 && c <= 0x7E) ansi_state = 0;
            continue;
        }
        // Skip stray CSI sequences like "[1;30m" when ESC was lost
        if (ansi_state == 0 && c == '[') {
            const char *q = p + 1;
            // scan digits and semicolons
            while (*q && (isdigit((unsigned char)*q) || *q == ';')) {
                q++;
            }
            // if we find a final byte (0x40–0x7E), skip the whole sequence
            if (*q && ((unsigned char)*q >= 0x40 && (unsigned char)*q <= 0x7E)) {
                p = q;
                continue;
            }
        }
        // Handle backspace
        if (c == '\b') {
            if (g_column > 0) {
                g_column--;
                // Clear the character cell in back-buffer
                RECT r = {
                    g_column * g_char_width,
                    g_line   * g_char_height,
                    (g_column + 1) * g_char_width,
                    (g_line   + 1) * g_char_height
                };
                HBRUSH hbr = (HBRUSH)GetStockObject(BLACK_BRUSH);
                FillRect(g_memdc, &r, hbr);
                // Clear overlay buffer entry
                screen_buf[g_line * g_max_cols + g_column] = 0;
            }
            continue;
        }
        // Normal character handling
        if (c == '\r') {
            g_column = 0;
            continue;
        } else if (c == '\n') {
            g_line++;
            g_column = 0;
            if (g_line >= g_max_lines) {
                int sh = g_char_height;
                BitBlt(g_memdc, 0, 0, g_screen_width, g_screen_height - sh, g_memdc, 0, sh, SRCCOPY);
                RECT r = {0, g_screen_height - sh, g_screen_width, g_screen_height};
                HBRUSH hbr = (HBRUSH)GetStockObject(BLACK_BRUSH);
                FillRect(g_memdc, &r, hbr);
                g_line = g_max_lines - 1;
            }
        } else {
            // Wrap on width overflow
            int max_cols = g_screen_width / g_char_width;
            if (g_column >= max_cols) {
                g_line++;
                g_column = 0;
                if (g_line >= g_max_lines) {
                    int sh = g_char_height;
                    BitBlt(g_memdc, 0, 0, g_screen_width, g_screen_height - sh,
                           g_memdc, 0, sh, SRCCOPY);
                    RECT r = {0, g_screen_height - sh, g_screen_width, g_screen_height};
                    HBRUSH hbr = (HBRUSH)GetStockObject(BLACK_BRUSH);
                    FillRect(g_memdc, &r, hbr);
                    g_line = g_max_lines - 1;
                }
            }
            // Draw character
            // Record character in overlay buffer
            screen_buf[g_line * g_max_cols + g_column] = c;
            TextOutA(g_memdc,
                     g_column * g_char_width,
                     g_line * g_char_height,
                     (LPCSTR)&c, 1);
            g_column++;
        }
    }
}

int main( int argc, char ** argv )
{
    g_hdc = GetDC(NULL);
    // Select the system OEM fixed-pitch font
    g_font = CreateFont(12, 6, 0, 0, FW_DONTCARE, FALSE, FALSE, FALSE, DEFAULT_CHARSET, OUT_OUTLINE_PRECIS,
                CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY, VARIABLE_PITCH, TEXT("SimSun"));
    SelectObject(g_hdc, g_font);
    SetBkMode(g_hdc, TRANSPARENT);
    SetTextColor(g_hdc, RGB(255,255,255));
    // Clear entire screen to black
    SetBkColor(g_hdc, RGB(0,0,0));
    // Text background remains black
    SetBkMode(g_hdc, OPAQUE);
    // Query actual character cell size
    {
        TEXTMETRICA tm;
        GetTextMetricsA(g_hdc, &tm);
        g_char_width  = tm.tmAveCharWidth;
        g_char_height = tm.tmHeight - tm.tmInternalLeading;
    }
    g_display_width  = GetDeviceCaps(g_hdc, HORZRES);
    g_display_height = GetDeviceCaps(g_hdc, VERTRES);
    g_screen_width = g_display_width / 3;
    g_screen_height = g_display_height / 3;
    g_max_lines     = g_screen_height / g_char_height;
    // Initialize overlay buffer
    g_max_cols  = g_screen_width / g_char_width;
    screen_buf  = calloc(g_max_lines * g_max_cols, 1);
    // Create back-buffer DC and bitmap
    g_memdc  = CreateCompatibleDC(g_hdc);
    g_membmp = CreateCompatibleBitmap(g_hdc, g_screen_width, g_screen_height);
    SelectObject(g_memdc, g_membmp);
    // Mirror text settings into back-buffer DC
    SelectObject(g_memdc, g_font);
    SetBkMode(g_memdc, OPAQUE);
    SetTextColor(g_memdc, RGB(255,255,255));
    SetBkColor(g_memdc, RGB(0,0,0));
    // Clear back-buffer to black
    PatBlt(g_memdc, 0, 0, g_screen_width, g_screen_height, BLACKNESS);
    g_line = 0;
    g_column = 0;
	int i;
	long long instct = -1;
	int show_help = 0;
	int time_divisor = 1;
	int fixed_update = 0;
	int do_sleep = 1;
	int single_step = 0;
	int dtb_ptr = 0;
	const char * image_file_name = 0;
	const char * dtb_file_name = 0;
	for( i = 1; i < argc; i++ )
	{
		const char * param = argv[i];
		int param_continue = 0; // Can combine parameters, like -lpt x
		do
		{
			if( param[0] == '-' || param_continue )
			{
				switch( param[1] )
				{
				case 'm': if( ++i < argc ) ram_amt = SimpleReadNumberInt( argv[i], ram_amt ); break;
				case 'c': if( ++i < argc ) instct = SimpleReadNumberInt( argv[i], -1 ); break;
				case 'k': if( ++i < argc ) kernel_command_line = argv[i]; break;
				case 'f': image_file_name = (++i<argc)?argv[i]:0; break;
				case 'b': dtb_file_name = (++i<argc)?argv[i]:0; break;
				case 'l': param_continue = 1; fixed_update = 1; break;
				case 'p': param_continue = 1; do_sleep = 0; break;
				case 's': param_continue = 1; single_step = 1; break;
				case 'd': param_continue = 1; fail_on_all_faults = 1; break; 
				case 't': if( ++i < argc ) time_divisor = SimpleReadNumberInt( argv[i], 1 ); break;
				default:
					if( param_continue )
						param_continue = 0;
					else
						show_help = 1;
					break;
				}
			}
			else
			{
				show_help = 1;
				break;
			}
			param++;
		} while( param_continue );
	}
	if( show_help || image_file_name == 0 || time_divisor <= 0 )
	{
		fprintf( stderr, "./mini-rv32imaf [parameters]\n\t-m [ram amount]\n\t-f [running image]\n\t-k [kernel command line]\n\t-b [dtb file, or 'disable']\n\t-c instruction count\n\t-s single step with full processor state\n\t-t time divion base\n\t-l lock time base to instruction count\n\t-p disable sleep when wfi\n\t-d fail out immediately on all faults\n" );
		return 1;
	}

	ram_image = malloc( ram_amt );
	if( !ram_image )
	{
		fprintf( stderr, "Error: could not allocate system image.\n" );
		return -4;
	}

restart:
	{
		FILE * f = fopen( image_file_name, "rb" );
		if( !f || ferror( f ) )
		{
			fprintf( stderr, "Error: \"%s\" not found\n", image_file_name );
			return -5;
		}
		fseek( f, 0, SEEK_END );
		long flen = ftell( f );
		fseek( f, 0, SEEK_SET );
		if( flen > ram_amt )
		{
			fprintf( stderr, "Error: Could not fit RAM image (%ld bytes) into %d\n", flen, ram_amt );
			return -6;
		}

		memset( ram_image, 0, ram_amt );
		if( fread( ram_image, flen, 1, f ) != 1)
		{
			fprintf( stderr, "Error: Could not load image.\n" );
			return -7;
		}
		fclose( f );

		if( dtb_file_name )
		{
			if( strcmp( dtb_file_name, "disable" ) == 0 )
			{
				// No DTB reading.
			}
			else
			{
				f = fopen( dtb_file_name, "rb" );
				if( !f || ferror( f ) )
				{
					fprintf( stderr, "Error: \"%s\" not found\n", dtb_file_name );
					return -5;
				}
				fseek( f, 0, SEEK_END );
				long dtblen = ftell( f );
				fseek( f, 0, SEEK_SET );
				dtb_ptr = ram_amt - dtblen - sizeof( struct MiniRV32IMAState );
				if( fread( ram_image + dtb_ptr, dtblen, 1, f ) != 1 )
				{
					fprintf( stderr, "Error: Could not open dtb \"%s\"\n", dtb_file_name );
					return -9;
				}
				fclose( f );
			}
		}
		else
		{
			// Load a default dtb.
			dtb_ptr = ram_amt - sizeof(default64mbdtb) - sizeof( struct MiniRV32IMAState );
			memcpy( ram_image + dtb_ptr, default64mbdtb, sizeof( default64mbdtb ) );
			if( kernel_command_line )
			{
				strncpy( (char*)( ram_image + dtb_ptr + 0xc0 ), kernel_command_line, 54 );
			}
		}
	}

	CaptureKeyboardInput();

	// The core lives at the end of RAM.
	core = (struct MiniRV32IMAState *)(ram_image + ram_amt - sizeof( struct MiniRV32IMAState ));
	core->pc = MINIRV32_RAM_IMAGE_OFFSET;
	core->regs[10] = 0x00; //hart ID
	core->regs[11] = dtb_ptr?(dtb_ptr+MINIRV32_RAM_IMAGE_OFFSET):0; //dtb_pa (Must be valid pointer) (Should be pointer to dtb)
	core->extraflags |= 3; // Machine-mode.

	if( dtb_file_name == 0 )
	{
		// Update system ram size in DTB (but if and only if we're using the default DTB)
		// Warning - this will need to be updated if the skeleton DTB is ever modified.
		uint32_t * dtb = (uint32_t*)(ram_image + dtb_ptr);
		if( dtb[0x13c/4] == 0x00c0ff03 )
		{
			uint32_t validram = dtb_ptr;
			dtb[0x13c/4] = (validram>>24) | ((( validram >> 16 ) & 0xff) << 8 ) | (((validram>>8) & 0xff ) << 16 ) | ( ( validram & 0xff) << 24 );
		}
	}

	// Image is loaded.
	uint64_t rt;
	uint64_t lastTime = (fixed_update)?0:(GetTimeMicroseconds()/time_divisor);
	int instrs_per_flip = single_step?1:1024;
	for( rt = 0; rt < instct+1 || instct < 0; rt += instrs_per_flip )
	{
		uint64_t * this_ccount = ((uint64_t*)&core->cyclel);
		uint32_t elapsedUs = 0;
		if( fixed_update )
			elapsedUs = *this_ccount / time_divisor - lastTime;
		else
			elapsedUs = GetTimeMicroseconds()/time_divisor - lastTime;
		lastTime += elapsedUs;

		if( single_step )
			DumpState( core, ram_image);

		int ret = MiniRV32IMAStep( core, ram_image, 0, elapsedUs, instrs_per_flip ); // Execute upto 1024 cycles before breaking out.
		switch( ret )
		{
			case 0: break;
			case 1: if( do_sleep ) MiniSleep(); *this_ccount += instrs_per_flip; break;
			case 3: instct = 0; break;
			case 0x7777: goto restart;	//syscon code for restart
			case 0x5555: { char buf[64]; snprintf(buf, sizeof(buf), "POWEROFF@0x%08x%08x", core->cycleh, core->cyclel); print_text_gdi(buf); return 0; } //syscon code for power-off
            default: print_text_gdi( "Unknown failure\n" ); break;
		}

        while(!IsHover())
            Sleep(1);
    }

    DeleteObject(g_font);
    ReleaseDC(NULL, g_hdc);
    // Destroy back-buffer
    DeleteObject(g_membmp);
    DeleteDC(g_memdc);
    free(screen_buf);
    DumpState( core, ram_image);
}


//////////////////////////////////////////////////////////////////////////
// Platform-specific functionality
//////////////////////////////////////////////////////////////////////////


#if defined(WINDOWS) || defined(WIN32) || defined(_WIN32)
#include <string.h>
// Buffered GetAsyncKeyState for keyboard input
static int  g_kbPending = 0;
static int  g_kbValue   = -1;

static BOOL IsHover()
{
    POINT cursor_pos;
    GetCursorPos(&cursor_pos);
    if (cursor_pos.x > g_display_width - g_screen_width && cursor_pos.y < g_screen_height)
        return TRUE;
    else
        return FALSE;
}

static void CaptureKeyboardInput()
{
    // No initialization needed for polling
}

static void ResetKeyboardInput()
{
    // No cleanup needed
}

static void MiniSleep()
{
    // Idle sleep, drawing occurs in main loop via back-buffer blit
        // Blit back-buffer to desktop DC each iteration
    if (IsHover())
        BitBlt(g_hdc, g_display_width - g_screen_width, 0, g_screen_width, g_screen_height,
                g_memdc, 0, 0, SRCCOPY);
}

static uint64_t GetTimeMicroseconds()
{
    static LARGE_INTEGER lpf;
    LARGE_INTEGER li;
    if (!lpf.QuadPart)
        QueryPerformanceFrequency(&lpf);
    QueryPerformanceCounter(&li);
    return ((uint64_t)li.QuadPart * 1000000LL) / (uint64_t)lpf.QuadPart;
}

static int IsKBHit()
{
    if (g_kbPending)
        return 1;
    for (int vk = 8; vk < 256; vk++) {
        // Skip pure SHIFT keys so they don't register as input
        if (vk == VK_SHIFT || vk == VK_LSHIFT || vk == VK_RSHIFT)
            continue;
        if (GetAsyncKeyState(vk) & 1 && IsHover()) {
            // Handle '-'/'_' key explicitly
            if (vk == VK_OEM_MINUS) {
                g_kbValue = (GetAsyncKeyState(VK_SHIFT) & 0x8000) ? '_' : '-';
            } else {
                BYTE ks[256];
                GetKeyboardState(ks);
                // Mark SHIFT in key state
                if (GetAsyncKeyState(VK_SHIFT) & 0x8000)
                    ks[VK_SHIFT] |= 0x80;
                UINT scan = MapVirtualKeyA(vk, MAPVK_VK_TO_VSC);
                WCHAR bufUni[4];
                int len = ToUnicodeEx(
                    vk, scan, ks, bufUni, 4, 0, GetKeyboardLayout(0)
                );
                if (len > 0) {
                    g_kbValue = (int)bufUni[0];
                } else {
                    switch (vk) {
                        case VK_LEFT:  g_kbValue = '\b'; break;
                        case VK_RIGHT: g_kbValue = '\t'; break;
                        case VK_UP:    g_kbValue = '\x1B'; break;
                        case VK_DOWN:  g_kbValue = '\n'; break;
                        default:       g_kbValue = -1; break;
                    }
                }
            }
            g_kbPending = 1;
            return 1;
        }
        // Redraw overlay buffer to desktop DC each iteration
    }
    return 0;
}

static int ReadKBByte()
{
    if (!g_kbPending)
        return -1;
    int c = g_kbValue;
    g_kbPending = 0;
    return c;
}

#else

#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>
#include <signal.h>
#include <sys/time.h>

static void CtrlC()
{
	DumpState( core, ram_image);
	exit( 0 );
}

// Override keyboard, so we can capture all keyboard input for the VM.
static void CaptureKeyboardInput()
{
	// Hook exit, because we want to re-enable keyboard.
	atexit(ResetKeyboardInput);
	signal(SIGINT, CtrlC);

	struct termios term;
	tcgetattr(0, &term);
	term.c_lflag &= ~(ICANON | ECHO); // Disable echo as well
	tcsetattr(0, TCSANOW, &term);
}

static void ResetKeyboardInput()
{
	// Re-enable echo, etc. on keyboard.
	struct termios term;
	tcgetattr(0, &term);
	term.c_lflag |= ICANON | ECHO;
	tcsetattr(0, TCSANOW, &term);
}

static void MiniSleep()
{
	usleep(500);
}

static uint64_t GetTimeMicroseconds()
{
	struct timeval tv;
	gettimeofday( &tv, 0 );
	return tv.tv_usec + ((uint64_t)(tv.tv_sec)) * 1000000LL;
}

static int is_eofd;

static int ReadKBByte()
{
	if( is_eofd ) return 0xffffffff;
	char rxchar = 0;
	int rread = read(fileno(stdin), (char*)&rxchar, 1);

	if( rread > 0 ) // Tricky: getchar can't be used with arrow keys.
		return rxchar;
	else
		return -1;
}

static int IsKBHit()
{
	if( is_eofd ) return -1;
	int byteswaiting;
	ioctl(0, FIONREAD, &byteswaiting);
	if( !byteswaiting && write( fileno(stdin), 0, 0 ) != 0 ) { is_eofd = 1; return -1; } // Is end-of-file for 
	return !!byteswaiting;
}


#endif


//////////////////////////////////////////////////////////////////////////
// Rest of functions functionality
//////////////////////////////////////////////////////////////////////////

static uint32_t HandleException( uint32_t ir, uint32_t code )
{
	// Weird opcode emitted by duktape on exit.
	if( code == 3 )
	{
		// Could handle other opcodes here.
	}
	return code;
}

static uint32_t HandleControlStore( uint32_t addy, uint32_t val )
{
	if( addy == 0x10000000 ) //UART 8250 / 16550 Data Buffer
	{
        {
            char cbuf[2] = { (char)val, '\0' };
            print_text_gdi(cbuf);
        }
	}
	else if( addy == 0x11004004 ) //CLNT
		core->timermatchh = val;
	else if( addy == 0x11004000 ) //CLNT
		core->timermatchl = val;
	else if( addy == 0x11100000 ) //SYSCON (reboot, poweroff, etc.)
	{
		core->pc = core->pc + 4;
		return val; // NOTE: PC will be PC of Syscon.
	}
	return 0;
}


static uint32_t HandleControlLoad( uint32_t addy )
{
	// Emulating a 8250 / 16550 UART
	if( addy == 0x10000005 )
		return 0x60 | IsKBHit();
	else if( addy == 0x10000000 && IsKBHit() )
		return ReadKBByte();
	else if( addy == 0x1100bffc ) // https://chromitem-soc.readthedocs.io/en/latest/clint.html
		return core->timerh;
	else if( addy == 0x1100bff8 )
		return core->timerl;
	return 0;
}

static void HandleOtherCSRWrite(uint8_t *image, uint16_t csrno, uint32_t value)
{
    char buf[512];
    if (csrno == 0x136)
    {
        snprintf(buf, sizeof(buf), "%d", value);
        print_text_gdi(buf);
    }
    else if (csrno == 0x137)
    {
        snprintf(buf, sizeof(buf), "%08x", value);
        print_text_gdi(buf);
    }
    else if (csrno == 0x138)
    {
        uint32_t ptrstart = value - MINIRV32_RAM_IMAGE_OFFSET;
        uint32_t ptrend = ptrstart;
        if (ptrstart >= ram_amt)
        {
            print_text_gdi("DEBUG PASSED INVALID PTR");
        }
        else
        {
            while (ptrend < ram_amt && image[ptrend])
                ptrend++;
            size_t len = ptrend - ptrstart;
            if (len > 0)
            {
                size_t copylen = len < sizeof(buf) - 1 ? len : sizeof(buf) - 1;
                memcpy(buf, image + ptrstart, copylen);
                buf[copylen] = '\0';
                print_text_gdi(buf);
            }
        }
    }
    else if (csrno == 0x139)
    {
        buf[0] = (char)value;
        buf[1] = '\0';
        print_text_gdi(buf);
    }
}

static int32_t HandleOtherCSRRead( uint8_t * image, uint16_t csrno )
{
	if( csrno == 0x140 )
	{
		if( !IsKBHit() ) return -1;
		return ReadKBByte();
	}
	return 0;
}

static int64_t SimpleReadNumberInt( const char * number, int64_t defaultNumber )
{
	if( !number || !number[0] ) return defaultNumber;
	int radix = 10;
	if( number[0] == '0' )
	{
		char nc = number[1];
		number+=2;
		if( nc == 0 ) return 0;
		else if( nc == 'x' ) radix = 16;
		else if( nc == 'b' ) radix = 2;
		else { number--; radix = 8; }
	}
	char * endptr;
	uint64_t ret = strtoll( number, &endptr, radix );
	if( endptr == number )
	{
		return defaultNumber;
	}
	else
	{
		return ret;
	}
}

static void DumpState(struct MiniRV32IMAState *core, uint8_t *ram_image)
{
    char buf[1024];
    uint32_t pc = core->pc;
    uint32_t pc_offset = pc - MINIRV32_RAM_IMAGE_OFFSET;
    uint32_t ir = 0;
    if (pc_offset < ram_amt - 3)
        ir = *((uint32_t*)(&((uint8_t*)ram_image)[pc_offset]));
    snprintf(buf, sizeof(buf), "PC: %08x [%s] ", pc, (pc_offset < ram_amt - 3) ? "0x" : "xxxx", 0);
    if (pc_offset < ram_amt - 3)
        snprintf(buf + strlen(buf), sizeof(buf) - strlen(buf), "%08x", ir);
    else
        snprintf(buf + strlen(buf), sizeof(buf) - strlen(buf), "xxxxxxxxxx");
    print_text_gdi(buf);
    uint32_t *regs = core->regs;
    snprintf(buf, sizeof(buf),
        "Z:%08x ra:%08x sp:%08x gp:%08x tp:%08x t0:%08x t1:%08x t2:%08x s0:%08x s1:%08x a0:%08x a1:%08x a2:%08x a3:%08x a4:%08x a5:%08x",
        regs[0], regs[1], regs[2], regs[3], regs[4], regs[5], regs[6], regs[7],
        regs[8], regs[9], regs[10], regs[11], regs[12], regs[13], regs[14], regs[15]);
    print_text_gdi(buf);
    snprintf(buf, sizeof(buf),
        "a6:%08x a7:%08x s2:%08x s3:%08x s4:%08x s5:%08x s6:%08x s7:%08x s8:%08x s9:%08x s10:%08x s11:%08x t3:%08x t4:%08x t5:%08x t6:%08x",
        regs[16], regs[17], regs[18], regs[19], regs[20], regs[21], regs[22], regs[23],
        regs[24], regs[25], regs[26], regs[27], regs[28], regs[29], regs[30], regs[31]);
    print_text_gdi(buf);
}

