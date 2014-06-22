#ifndef COMMON_H_
#define COMMON_H_

#include <string>

#define MAXPC 18446744073709551615
#define MINPC 0
#define SS "ss.txt"
#define UU "uu.txt"
#define SU "su.txt"
#define US "us.txt"
#define SNK "sn.txt"
#define UNK "un.txt"
#define DBGLIB "libc-2.15.so"	//path of libc's debug info on :/usr/lib/debug/lib/i386-linux-gnu
									//should be avaliable by default
#define SLOG "struct.log"

typedef enum{
	DVAR_BASE = 0,
	DVAR_ARRAY,
	DVAR_STRUCT,
	DVAR_POINTER,
	DVAR_UN,
}DVAR_TYPE_T;

typedef enum{
	OFFSET_LOC = 0,
	ADDR_LOC,
	REG_LOC,
}LOC_TYPE_T;

typedef enum{
	YES = 99,
	NO,
}BOOL;

enum hardcode_func_t{
	IFUNC_STRCAT,
	IFUNC_INDEX,
	IFUNC_STRCMP,
	IFUNC_STRCPY,
	IFUNC_STRRCHR,
	IFUNC_STRCSPN,
	IFUNC_STRLEN,
	IFUNC_STRNLEN,
	IFUNC_STRNCAT,
	IFUNC_STRNCMP,
	IFUNC_STRNCPY,
	IFUNC_RINDEX,
	IFUNC_STRPBRK,
	IFUNC_STRSPN,
	IFUNC_MEMCHR,
	IFUNC_BCMP,
	IFUNC_MEMMOVE,
	IFUNC_MEMSET,
	IFUNC_MEMPCPY,
	IFUNC_BCOPY,
	IFUNC_BZERO,
	IFUNC_STPCPY,
	IFUNC_STPNCPY,
	IFUNC_STRCASECMP,
	IFUNC_STRNCASECMP,
	IFUNC_MEMCPY,
	IFUNC_RAWMEMCHR,
	IFUNC_MEMRCHR,
	IFUNC_STRSTR,
	IFUNC_STRCASESTR,
	IFUNC_WCSCHR,
	IFUNC_WCSCMP,
	IFUNC_WCSCPY,
	IFUNC_WCSLEN,
	IFUNC_WCSRCHR,
	IFUNC_WMEMCMP,
};

static std::string binop_label[] = {
		  "+",
		  "-",
		  "*",
		  "/",
		  "%",
		  "<<",
		  ">>",
		  "@>>",
		  "<<",
		  ">>",
		  "&&",
		  "||",
		  "&",
		  "|",
		  "XOR",
		  "EQ",
		  "!=",
		  ">",
		  "<",
		  ">=",
		  "<=",
		  "/$",
		  "%$"
};

static std::string indirect[] = {
		"strcat",
		"index",
		"strcmp",
		"strcpy",
		"strrchr",
		"strcspn",
		"strlen",
		"strnlen",
		"strncat",
		"strncmp",
		"strncpy",
		"rindex",
		"strpbrk",
		"strspn",
		"memchr",
		"bcmp",
		"memmove",
		"memset",
		"mempcpy",
		"bcopy",
		"bzero",
		"stpcpy",
		"stpncpy",
		"strcasecmp",
		"strncasecmp",
		"memcpy",
		"rawmemchr",
		"memrchr",
		"strstr",
		"strcasestr",
		"wcschr",
		"wcscmp",
		"wcscpy",
		"wcslen",
		"wcsrchr",
		"wmemcmp",
};

static std::string unop_label[] = {"NEG", "NOT"};

enum sign_type_t{
	SIGNED_T,
	UNSIGNED_T,
	UNKNOW_T,
};

#endif /* COMMON_H_ */
