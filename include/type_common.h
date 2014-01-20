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

static std::string unop_label[] = {"NEG", "NOT"};

enum sign_type_t{
	SIGNED_T,
	UNSIGNED_T,
	UNKNOW_T,
};

#endif /* COMMON_H_ */
