/-
Wenyan operator catalogue generated from `wenyan-operators.md` headings.
-/
import SSBX.Text.Glyph

namespace SSBX.Text.WenyanOperators

open SSBX.Text.Glyph

inductive OperatorGroup where
  | R | C | T | F | B | Q | K | M | N | I | S | H | P | G | A | D | E | L | Y | X | Z
  deriving DecidableEq, Repr

inductive SignatureStatus where
  | given
  | placeholder
  | pending
  deriving DecidableEq, Repr

inductive OperatorId where
  | R_1 | R_2 | R_3 | R_4 | R_5 | R_6 | R_7 | R_8
  | R_9 | R_10 | R_11 | R_12 | R_13 | R_14 | R_15 | C_1
  | C_2 | C_3 | C_4 | C_5 | C_6 | C_7 | C_8 | T_1
  | T_2 | T_3 | T_4 | T_5 | T_6 | T_7 | T_8 | T_9
  | T_10 | T_11 | T_12 | T_13 | T_14 | T_15 | F_1 | F_2
  | F_3 | F_4 | F_5 | F_6 | F_7 | F_8 | F_9 | F_10
  | F_11 | F_12 | B_1 | B_2 | B_3 | B_4 | B_5 | B_6
  | B_7 | B_8 | Q_1 | Q_2 | Q_3 | Q_4 | Q_5 | Q_6
  | Q_7 | Q_8 | K_1 | K_2 | K_3 | K_4 | K_5 | K_6
  | K_7 | K_8 | M_1 | M_2 | M_3 | M_4 | M_5 | M_6
  | M_7 | M_8 | N_1 | N_2 | N_3 | N_4 | N_5 | N_6
  | N_7 | N_8 | I_1 | I_2 | I_3 | I_4 | I_5 | I_6
    | I_7 | I_8 | I_9 | S_1 | S_2 | S_3 | S_4 | S_5 | S_6
    | S_7 | S_8 | S_9 | S_10 | S_11 | S_12 | S_13 | S_14
    | S_15 | S_16 | S_17 | S_18 | S_19 | S_20 | H_1 | H_2
  | H_3 | H_4 | H_5 | H_6 | H_7 | H_8 | P_1 | P_2
  | P_3 | P_4 | P_5 | P_6 | P_7 | P_8 | P_9 | P_10
  | P_11 | P_12 | P_13 | P_14 | P_15 | P_16 | P_17 | P_18
  | P_19 | P_20 | P_21 | P_22 | P_23 | P_24 | G_1 | G_2
  | G_3 | G_4 | G_5 | G_6 | G_7 | G_8 | G_9 | G_10
  | G_11 | A_1 | A_2 | A_3 | A_4
  | A_5 | A_6 | A_7 | A_8 | A_9 | A_10 | A_11 | A_12
  | A_13 | A_14 | A_15 | A_16 | A_17 | A_18 | A_19 | A_20
  | D_1 | D_2 | D_3 | D_4 | D_5 | D_6 | D_7 | D_8 | D_9
  | D_10 | E_1 | E_2 | E_3 | E_4 | E_5 | E_6 | E_7
  | E_8 | E_9 | L_1 | L_2 | L_3 | L_4
  | L_5 | L_6 | L_7 | L_8 | L_9 | L_10 | L_11 | L_12
  | L_13 | L_14 | L_15 | L_16 | Y_1 | Y_2 | Y_3 | Y_4
  | Y_5 | Y_6 | Y_7 | Y_8 | Y_9 | Y_10 | Y_11 | Y_12
  | Y_13 | Y_14 | Y_15 | Y_16 | Y_17 | Y_18 | Y_19 | Y_20
  | Y_21 | Y_22 | Y_23 | Y_24 | Y_25 | Y_26 | Y_27 | Y_28
  | X_1 | X_2 | X_3 | X_4 | X_5 | X_6 | X_7 | X_8
  | X_9 | X_10 | X_11 | X_12 | X_13 | X_14 | X_15 | X_16
  | Z_1 | Z_2 | Z_3 | Z_4 | Z_5
  | Z_6 | Z_7 | Z_8 | Z_9 | Z_10 | Z_11 | Z_12 | Z_13
  | Z_14 | Z_15 | Z_16 | Z_17 | Z_18 | Z_19 | Z_20 | Z_21
  | Z_22 | Z_23 | Z_24 | Z_25 | Z_26 | Z_27 | Z_28 | Z_29
  | Z_30 | Z_31 | Z_32 | Z_33 | Z_34 | Z_35 | Z_36 | Z_37
  | Z_38 | Z_39 | Z_40
  deriving DecidableEq, Repr

structure OperatorEntry where
  id : OperatorId
  code : String
  title : String
  group : OperatorGroup
  forms : List GlyphSense
  signature : SignatureStatus
  deriving Repr

def OperatorId.group : OperatorId -> OperatorGroup
  | .R_1 => .R
  | .R_2 => .R
  | .R_3 => .R
  | .R_4 => .R
  | .R_5 => .R
  | .R_6 => .R
  | .R_7 => .R
  | .R_8 => .R
  | .R_9 => .R
  | .R_10 => .R
  | .R_11 => .R
  | .R_12 => .R
  | .R_13 => .R
  | .R_14 => .R
  | .R_15 => .R
  | .C_1 => .C
  | .C_2 => .C
  | .C_3 => .C
  | .C_4 => .C
  | .C_5 => .C
  | .C_6 => .C
  | .C_7 => .C
  | .C_8 => .C
  | .T_1 => .T
  | .T_2 => .T
  | .T_3 => .T
  | .T_4 => .T
  | .T_5 => .T
  | .T_6 => .T
  | .T_7 => .T
  | .T_8 => .T
  | .T_9 => .T
  | .T_10 => .T
  | .T_11 => .T
  | .T_12 => .T
  | .T_13 => .T
  | .T_14 => .T
  | .T_15 => .T
  | .F_1 => .F
  | .F_2 => .F
  | .F_3 => .F
  | .F_4 => .F
  | .F_5 => .F
  | .F_6 => .F
  | .F_7 => .F
  | .F_8 => .F
  | .F_9 => .F
  | .F_10 => .F
  | .F_11 => .F
  | .F_12 => .F
  | .B_1 => .B
  | .B_2 => .B
  | .B_3 => .B
  | .B_4 => .B
  | .B_5 => .B
  | .B_6 => .B
  | .B_7 => .B
  | .B_8 => .B
  | .Q_1 => .Q
  | .Q_2 => .Q
  | .Q_3 => .Q
  | .Q_4 => .Q
  | .Q_5 => .Q
  | .Q_6 => .Q
  | .Q_7 => .Q
  | .Q_8 => .Q
  | .K_1 => .K
  | .K_2 => .K
  | .K_3 => .K
  | .K_4 => .K
  | .K_5 => .K
  | .K_6 => .K
  | .K_7 => .K
  | .K_8 => .K
  | .M_1 => .M
  | .M_2 => .M
  | .M_3 => .M
  | .M_4 => .M
  | .M_5 => .M
  | .M_6 => .M
  | .M_7 => .M
  | .M_8 => .M
  | .N_1 => .N
  | .N_2 => .N
  | .N_3 => .N
  | .N_4 => .N
  | .N_5 => .N
  | .N_6 => .N
  | .N_7 => .N
  | .N_8 => .N
  | .I_1 => .I
  | .I_2 => .I
  | .I_3 => .I
  | .I_4 => .I
  | .I_5 => .I
  | .I_6 => .I
  | .I_7 => .I
  | .I_8 => .I
  | .I_9 => .I
  | .S_1 => .S
  | .S_2 => .S
  | .S_3 => .S
  | .S_4 => .S
  | .S_5 => .S
  | .S_6 => .S
  | .S_7 => .S
  | .S_8 => .S
  | .S_9 => .S
  | .S_10 => .S
  | .S_11 => .S
  | .S_12 => .S
  | .S_13 => .S
  | .S_14 => .S
  | .S_15 => .S
  | .S_16 => .S
  | .S_17 => .S
  | .S_18 => .S
  | .S_19 => .S
  | .S_20 => .S
  | .H_1 => .H
  | .H_2 => .H
  | .H_3 => .H
  | .H_4 => .H
  | .H_5 => .H
  | .H_6 => .H
  | .H_7 => .H
  | .H_8 => .H
  | .P_1 => .P
  | .P_2 => .P
  | .P_3 => .P
  | .P_4 => .P
  | .P_5 => .P
  | .P_6 => .P
  | .P_7 => .P
  | .P_8 => .P
  | .P_9 => .P
  | .P_10 => .P
  | .P_11 => .P
  | .P_12 => .P
  | .P_13 => .P
  | .P_14 => .P
  | .P_15 => .P
  | .P_16 => .P
  | .P_17 => .P
  | .P_18 => .P
  | .P_19 => .P
  | .P_20 => .P
  | .P_21 => .P
  | .P_22 => .P
  | .P_23 => .P
  | .P_24 => .P
  | .G_1 => .G
  | .G_2 => .G
  | .G_3 => .G
  | .G_4 => .G
  | .G_5 => .G
  | .G_6 => .G
  | .G_7 => .G
  | .G_8 => .G
  | .G_9 => .G
  | .G_10 => .G
  | .G_11 => .G
  | .A_1 => .A
  | .A_2 => .A
  | .A_3 => .A
  | .A_4 => .A
  | .A_5 => .A
  | .A_6 => .A
  | .A_7 => .A
  | .A_8 => .A
  | .A_9 => .A
  | .A_10 => .A
  | .A_11 => .A
  | .A_12 => .A
  | .A_13 => .A
  | .A_14 => .A
  | .A_15 => .A
  | .A_16 => .A
  | .A_17 => .A
  | .A_18 => .A
  | .A_19 => .A
  | .A_20 => .A
  | .D_1 => .D
  | .D_2 => .D
  | .D_3 => .D
  | .D_4 => .D
  | .D_5 => .D
  | .D_6 => .D
  | .D_7 => .D
  | .D_8 => .D
  | .D_9 => .D
  | .D_10 => .D
  | .E_1 => .E
  | .E_2 => .E
  | .E_3 => .E
  | .E_4 => .E
  | .E_5 => .E
  | .E_6 => .E
  | .E_7 => .E
  | .E_8 => .E
  | .E_9 => .E
  | .L_1 => .L
  | .L_2 => .L
  | .L_3 => .L
  | .L_4 => .L
  | .L_5 => .L
  | .L_6 => .L
  | .L_7 => .L
  | .L_8 => .L
  | .L_9 => .L
  | .L_10 => .L
  | .L_11 => .L
  | .L_12 => .L
  | .L_13 => .L
  | .L_14 => .L
  | .L_15 => .L
  | .L_16 => .L
  | .Y_1 => .Y
  | .Y_2 => .Y
  | .Y_3 => .Y
  | .Y_4 => .Y
  | .Y_5 => .Y
  | .Y_6 => .Y
  | .Y_7 => .Y
  | .Y_8 => .Y
  | .Y_9 => .Y
  | .Y_10 => .Y
  | .Y_11 => .Y
  | .Y_12 => .Y
  | .Y_13 => .Y
  | .Y_14 => .Y
  | .Y_15 => .Y
  | .Y_16 => .Y
  | .Y_17 => .Y
  | .Y_18 => .Y
  | .Y_19 => .Y
  | .Y_20 => .Y
  | .Y_21 => .Y
  | .Y_22 => .Y
  | .Y_23 => .Y
  | .Y_24 => .Y
  | .Y_25 => .Y
  | .Y_26 => .Y
  | .Y_27 => .Y
  | .Y_28 => .Y
  | .X_1 => .X
  | .X_2 => .X
  | .X_3 => .X
  | .X_4 => .X
  | .X_5 => .X
  | .X_6 => .X
  | .X_7 => .X
  | .X_8 => .X
  | .X_9 => .X
  | .X_10 => .X
  | .X_11 => .X
  | .X_12 => .X
  | .X_13 => .X
  | .X_14 => .X
  | .X_15 => .X
  | .X_16 => .X
  | .Z_1 => .Z
  | .Z_2 => .Z
  | .Z_3 => .Z
  | .Z_4 => .Z
  | .Z_5 => .Z
  | .Z_6 => .Z
  | .Z_7 => .Z
  | .Z_8 => .Z
  | .Z_9 => .Z
  | .Z_10 => .Z
  | .Z_11 => .Z
  | .Z_12 => .Z
  | .Z_13 => .Z
  | .Z_14 => .Z
  | .Z_15 => .Z
  | .Z_16 => .Z
  | .Z_17 => .Z
  | .Z_18 => .Z
  | .Z_19 => .Z
  | .Z_20 => .Z
  | .Z_21 => .Z
  | .Z_22 => .Z
  | .Z_23 => .Z
  | .Z_24 => .Z
  | .Z_25 => .Z
  | .Z_26 => .Z
  | .Z_27 => .Z
  | .Z_28 => .Z
  | .Z_29 => .Z
  | .Z_30 => .Z
  | .Z_31 => .Z
  | .Z_32 => .Z
  | .Z_33 => .Z
  | .Z_34 => .Z
  | .Z_35 => .Z
  | .Z_36 => .Z
  | .Z_37 => .Z
  | .Z_38 => .Z
  | .Z_39 => .Z
  | .Z_40 => .Z

def OperatorId.code : OperatorId -> String
  | .R_1 => "R-1"
  | .R_2 => "R-2"
  | .R_3 => "R-3"
  | .R_4 => "R-4"
  | .R_5 => "R-5"
  | .R_6 => "R-6"
  | .R_7 => "R-7"
  | .R_8 => "R-8"
  | .R_9 => "R-9"
  | .R_10 => "R-10"
  | .R_11 => "R-11"
  | .R_12 => "R-12"
  | .R_13 => "R-13"
  | .R_14 => "R-14"
  | .R_15 => "R-15"
  | .C_1 => "C-1"
  | .C_2 => "C-2"
  | .C_3 => "C-3"
  | .C_4 => "C-4"
  | .C_5 => "C-5"
  | .C_6 => "C-6"
  | .C_7 => "C-7"
  | .C_8 => "C-8"
  | .T_1 => "T-1"
  | .T_2 => "T-2"
  | .T_3 => "T-3"
  | .T_4 => "T-4"
  | .T_5 => "T-5"
  | .T_6 => "T-6"
  | .T_7 => "T-7"
  | .T_8 => "T-8"
  | .T_9 => "T-9"
  | .T_10 => "T-10"
  | .T_11 => "T-11"
  | .T_12 => "T-12"
  | .T_13 => "T-13"
  | .T_14 => "T-14"
  | .T_15 => "T-15"
  | .F_1 => "F-1"
  | .F_2 => "F-2"
  | .F_3 => "F-3"
  | .F_4 => "F-4"
  | .F_5 => "F-5"
  | .F_6 => "F-6"
  | .F_7 => "F-7"
  | .F_8 => "F-8"
  | .F_9 => "F-9"
  | .F_10 => "F-10"
  | .F_11 => "F-11"
  | .F_12 => "F-12"
  | .B_1 => "B-1"
  | .B_2 => "B-2"
  | .B_3 => "B-3"
  | .B_4 => "B-4"
  | .B_5 => "B-5"
  | .B_6 => "B-6"
  | .B_7 => "B-7"
  | .B_8 => "B-8"
  | .Q_1 => "Q-1"
  | .Q_2 => "Q-2"
  | .Q_3 => "Q-3"
  | .Q_4 => "Q-4"
  | .Q_5 => "Q-5"
  | .Q_6 => "Q-6"
  | .Q_7 => "Q-7"
  | .Q_8 => "Q-8"
  | .K_1 => "K-1"
  | .K_2 => "K-2"
  | .K_3 => "K-3"
  | .K_4 => "K-4"
  | .K_5 => "K-5"
  | .K_6 => "K-6"
  | .K_7 => "K-7"
  | .K_8 => "K-8"
  | .M_1 => "M-1"
  | .M_2 => "M-2"
  | .M_3 => "M-3"
  | .M_4 => "M-4"
  | .M_5 => "M-5"
  | .M_6 => "M-6"
  | .M_7 => "M-7"
  | .M_8 => "M-8"
  | .N_1 => "N-1"
  | .N_2 => "N-2"
  | .N_3 => "N-3"
  | .N_4 => "N-4"
  | .N_5 => "N-5"
  | .N_6 => "N-6"
  | .N_7 => "N-7"
  | .N_8 => "N-8"
  | .I_1 => "I-1"
  | .I_2 => "I-2"
  | .I_3 => "I-3"
  | .I_4 => "I-4"
  | .I_5 => "I-5"
  | .I_6 => "I-6"
  | .I_7 => "I-7"
  | .I_8 => "I-8"
  | .I_9 => "I-9"
  | .S_1 => "S-1"
  | .S_2 => "S-2"
  | .S_3 => "S-3"
  | .S_4 => "S-4"
  | .S_5 => "S-5"
  | .S_6 => "S-6"
  | .S_7 => "S-7"
  | .S_8 => "S-8"
  | .S_9 => "S-9"
  | .S_10 => "S-10"
  | .S_11 => "S-11"
  | .S_12 => "S-12"
  | .S_13 => "S-13"
  | .S_14 => "S-14"
  | .S_15 => "S-15"
  | .S_16 => "S-16"
  | .S_17 => "S-17"
  | .S_18 => "S-18"
  | .S_19 => "S-19"
  | .S_20 => "S-20"
  | .H_1 => "H-1"
  | .H_2 => "H-2"
  | .H_3 => "H-3"
  | .H_4 => "H-4"
  | .H_5 => "H-5"
  | .H_6 => "H-6"
  | .H_7 => "H-7"
  | .H_8 => "H-8"
  | .P_1 => "P-1"
  | .P_2 => "P-2"
  | .P_3 => "P-3"
  | .P_4 => "P-4"
  | .P_5 => "P-5"
  | .P_6 => "P-6"
  | .P_7 => "P-7"
  | .P_8 => "P-8"
  | .P_9 => "P-9"
  | .P_10 => "P-10"
  | .P_11 => "P-11"
  | .P_12 => "P-12"
  | .P_13 => "P-13"
  | .P_14 => "P-14"
  | .P_15 => "P-15"
  | .P_16 => "P-16"
  | .P_17 => "P-17"
  | .P_18 => "P-18"
  | .P_19 => "P-19"
  | .P_20 => "P-20"
  | .P_21 => "P-21"
  | .P_22 => "P-22"
  | .P_23 => "P-23"
  | .P_24 => "P-24"
  | .G_1 => "G-1"
  | .G_2 => "G-2"
  | .G_3 => "G-3"
  | .G_4 => "G-4"
  | .G_5 => "G-5"
  | .G_6 => "G-6"
  | .G_7 => "G-7"
  | .G_8 => "G-8"
  | .G_9 => "G-9"
  | .G_10 => "G-10"
  | .G_11 => "G-11"
  | .A_1 => "A-1"
  | .A_2 => "A-2"
  | .A_3 => "A-3"
  | .A_4 => "A-4"
  | .A_5 => "A-5"
  | .A_6 => "A-6"
  | .A_7 => "A-7"
  | .A_8 => "A-8"
  | .A_9 => "A-9"
  | .A_10 => "A-10"
  | .A_11 => "A-11"
  | .A_12 => "A-12"
  | .A_13 => "A-13"
  | .A_14 => "A-14"
  | .A_15 => "A-15"
  | .A_16 => "A-16"
  | .A_17 => "A-17"
  | .A_18 => "A-18"
  | .A_19 => "A-19"
  | .A_20 => "A-20"
  | .D_1 => "D-1"
  | .D_2 => "D-2"
  | .D_3 => "D-3"
  | .D_4 => "D-4"
  | .D_5 => "D-5"
  | .D_6 => "D-6"
  | .D_7 => "D-7"
  | .D_8 => "D-8"
  | .D_9 => "D-9"
  | .D_10 => "D-10"
  | .E_1 => "E-1"
  | .E_2 => "E-2"
  | .E_3 => "E-3"
  | .E_4 => "E-4"
  | .E_5 => "E-5"
  | .E_6 => "E-6"
  | .E_7 => "E-7"
  | .E_8 => "E-8"
  | .E_9 => "E-9"
  | .L_1 => "L-1"
  | .L_2 => "L-2"
  | .L_3 => "L-3"
  | .L_4 => "L-4"
  | .L_5 => "L-5"
  | .L_6 => "L-6"
  | .L_7 => "L-7"
  | .L_8 => "L-8"
  | .L_9 => "L-9"
  | .L_10 => "L-10"
  | .L_11 => "L-11"
  | .L_12 => "L-12"
  | .L_13 => "L-13"
  | .L_14 => "L-14"
  | .L_15 => "L-15"
  | .L_16 => "L-16"
  | .Y_1 => "Y-1"
  | .Y_2 => "Y-2"
  | .Y_3 => "Y-3"
  | .Y_4 => "Y-4"
  | .Y_5 => "Y-5"
  | .Y_6 => "Y-6"
  | .Y_7 => "Y-7"
  | .Y_8 => "Y-8"
  | .Y_9 => "Y-9"
  | .Y_10 => "Y-10"
  | .Y_11 => "Y-11"
  | .Y_12 => "Y-12"
  | .Y_13 => "Y-13"
  | .Y_14 => "Y-14"
  | .Y_15 => "Y-15"
  | .Y_16 => "Y-16"
  | .Y_17 => "Y-17"
  | .Y_18 => "Y-18"
  | .Y_19 => "Y-19"
  | .Y_20 => "Y-20"
  | .Y_21 => "Y-21"
  | .Y_22 => "Y-22"
  | .Y_23 => "Y-23"
  | .Y_24 => "Y-24"
  | .Y_25 => "Y-25"
  | .Y_26 => "Y-26"
  | .Y_27 => "Y-27"
  | .Y_28 => "Y-28"
  | .X_1 => "X-1"
  | .X_2 => "X-2"
  | .X_3 => "X-3"
  | .X_4 => "X-4"
  | .X_5 => "X-5"
  | .X_6 => "X-6"
  | .X_7 => "X-7"
  | .X_8 => "X-8"
  | .X_9 => "X-9"
  | .X_10 => "X-10"
  | .X_11 => "X-11"
  | .X_12 => "X-12"
  | .X_13 => "X-13"
  | .X_14 => "X-14"
  | .X_15 => "X-15"
  | .X_16 => "X-16"
  | .Z_1 => "Z-1"
  | .Z_2 => "Z-2"
  | .Z_3 => "Z-3"
  | .Z_4 => "Z-4"
  | .Z_5 => "Z-5"
  | .Z_6 => "Z-6"
  | .Z_7 => "Z-7"
  | .Z_8 => "Z-8"
  | .Z_9 => "Z-9"
  | .Z_10 => "Z-10"
  | .Z_11 => "Z-11"
  | .Z_12 => "Z-12"
  | .Z_13 => "Z-13"
  | .Z_14 => "Z-14"
  | .Z_15 => "Z-15"
  | .Z_16 => "Z-16"
  | .Z_17 => "Z-17"
  | .Z_18 => "Z-18"
  | .Z_19 => "Z-19"
  | .Z_20 => "Z-20"
  | .Z_21 => "Z-21"
  | .Z_22 => "Z-22"
  | .Z_23 => "Z-23"
  | .Z_24 => "Z-24"
  | .Z_25 => "Z-25"
  | .Z_26 => "Z-26"
  | .Z_27 => "Z-27"
  | .Z_28 => "Z-28"
  | .Z_29 => "Z-29"
  | .Z_30 => "Z-30"
  | .Z_31 => "Z-31"
  | .Z_32 => "Z-32"
  | .Z_33 => "Z-33"
  | .Z_34 => "Z-34"
  | .Z_35 => "Z-35"
  | .Z_36 => "Z-36"
  | .Z_37 => "Z-37"
  | .Z_38 => "Z-38"
  | .Z_39 => "Z-39"
  | .Z_40 => "Z-40"

def OperatorId.title : OperatorId -> String
  | .R_1 => "在"
  | .R_2 => "屬 / 属"
  | .R_3 => "際 / 际"
  | .R_4 => "間 / 间"
  | .R_5 => "中"
  | .R_6 => "正"
  | .R_7 => "應 / 应"
  | .R_8 => "比"
  | .R_9 => "承"
  | .R_10 => "乘"
  | .R_11 => "對 / 对"
  | .R_12 => "偶 / 耦"
  | .R_13 => "並 / 并"
  | .R_14 => "與 / 与"
  | .R_15 => "偕"
  | .C_1 => "含"
  | .C_2 => "包"
  | .C_3 => "容"
  | .C_4 => "中 (用作 inside)"
  | .C_5 => "外"
  | .C_6 => "內 / 内"
  | .C_7 => "表"
  | .C_8 => "裡 / 里"
  | .T_1 => "化"
  | .T_2 => "變 / 变"
  | .T_3 => "易"
  | .T_4 => "革"
  | .T_5 => "改"
  | .T_6 => "反"
  | .T_7 => "復 / 复"
  | .T_8 => "還 / 还"
  | .T_9 => "轉 / 转"
  | .T_10 => "推"
  | .T_11 => "致"
  | .T_12 => "損 / 损"
  | .T_13 => "益"
  | .T_14 => "屈"
  | .T_15 => "伸"
  | .F_1 => "往"
  | .F_2 => "來 / 来"
  | .F_3 => "進 / 进"
  | .F_4 => "退"
  | .F_5 => "升"
  | .F_6 => "降"
  | .F_7 => "出"
  | .F_8 => "入"
  | .F_9 => "行"
  | .F_10 => "動 / 动"
  | .F_11 => "靜 / 静"
  | .F_12 => "通"
  | .B_1 => "始"
  | .B_2 => "終 / 终"
  | .B_3 => "起"
  | .B_4 => "止"
  | .B_5 => "立"
  | .B_6 => "成"
  | .B_7 => "極 / 极"
  | .B_8 => "節 / 节"
  | .Q_1 => "凡"
  | .Q_2 => "皆"
  | .Q_3 => "各"
  | .Q_4 => "莫"
  | .Q_5 => "或"
  | .Q_6 => "有"
  | .Q_7 => "無 / 无"
  | .Q_8 => "唯"
  | .K_1 => "故"
  | .K_2 => "由"
  | .K_3 => "自"
  | .K_4 => "至"
  | .K_5 => "致 (复用 T-11)"
  | .K_6 => "使"
  | .K_7 => "令"
  | .K_8 => "以"
  | .M_1 => "必"
  | .M_2 => "或 (复用 Q-5 的另一读法)"
  | .M_3 => "當 / 当"
  | .M_4 => "宜"
  | .M_5 => "可"
  | .M_6 => "能"
  | .M_7 => "得"
  | .M_8 => "應 / 应 (复用 R-7)"
  | .N_1 => "不"
  | .N_2 => "非"
  | .N_3 => "弗"
  | .N_4 => "勿"
  | .N_5 => "毋"
  | .N_6 => "反 (复用 T-6) — 在对偶层"
  | .N_7 => "異 / 异"
  | .N_8 => "別 / 别"
  | .I_1 => "同"
  | .I_2 => "一"
  | .I_3 => "即"
  | .I_4 => "是"
  | .I_5 => "為 / 为"
  | .I_6 => "分"
  | .I_7 => "合"
  | .I_8 => "別 (复用 N-8) — 在分异层"
  | .I_9 => "系"
  | .S_1 => "之"
  | .S_2 => "而"
  | .S_3 => "則 / 则"
  | .S_4 => "若"
  | .S_5 => "雖 / 虽"
  | .S_6 => "然"
  | .S_7 => "故 (复用 K-1)"
  | .S_8 => "乃"
  | .S_9 => "既"
  | .S_10 => "將 / 将"
  | .S_11 => "方"
  | .S_12 => "嘗 / 尝"
  | .S_13 => "者"
  | .S_14 => "也"
  | .S_15 => "于 / 於"
  | .S_16 => "所"
  | .S_17 => "未"
  | .S_18 => "已"
  | .S_19 => "的"
  | .S_20 => "地"
  | .H_1 => "道"
  | .H_2 => "理"
  | .H_3 => "勢 / 势"
  | .H_4 => "機 / 机"
  | .H_5 => "法"
  | .H_6 => "象"
  | .H_7 => "名"
  | .H_8 => "體 / 体 与 用"
  | .P_1 => "故 (墨经版)"
  | .P_2 => "體 / 体"
  | .P_3 => "兼"
  | .P_4 => "同 (墨经四类)"
  | .P_5 => "異 / 异 (墨经四类)"
  | .P_6 => "久"
  | .P_7 => "宇"
  | .P_8 => "動 (墨经版)"
  | .P_9 => "止 (墨经版)"
  | .P_10 => "端"
  | .P_11 => "尺"
  | .P_12 => "中 (墨经版)"
  | .P_13 => "圜 / 圆"
  | .P_14 => "平"
  | .P_15 => "攖 / 撄"
  | .P_16 => "仳"
  | .P_17 => "次"
  | .P_18 => "法"
  | .P_19 => "名 (墨经三类)"
  | .P_20 => "知 (墨经三类)"
  | .P_21 => "辭 / 辞"
  | .P_22 => "說 / 说"
  | .P_23 => "辯 / 辩"
  | .P_24 => "類 / 类"
  | .G_1 => "指"
  | .G_2 => "物"
  | .G_3 => "名 (名家版)"
  | .G_4 => "實 / 实"
  | .G_5 => "位"
  | .G_6 => "正 (名家版)"
  | .G_7 => "離 / 离 (坚白离)"
  | .G_8 => "兼 / 合 (名家版)"
  | .G_9 => "別 / 别 (名家版)"
  | .G_10 => "然"
  | .G_11 => "命"
  | .A_1 => "漸 / 渐"
  | .A_2 => "驟 / 骤"
  | .A_3 => "忽"
  | .A_4 => "遂"
  | .A_5 => "復 / 复 (副词层)"
  | .A_6 => "又"
  | .A_7 => "屢 / 屡"
  | .A_8 => "愈"
  | .A_9 => "益 (副词层)"
  | .A_10 => "寖 / 浸"
  | .A_11 => "既...又... / 一...且... (双重 marker)"
  | .A_12 => "且"
  | .A_13 => "但"
  | .A_14 => "唯 (副词层)"
  | .A_15 => "亦"
  | .A_16 => "已"
  | .A_17 => "未"
  | .A_18 => "將 / 将"
  | .A_19 => "方"
  | .A_20 => "嘗 / 尝"
  | .D_1 => "一 (作算子)"
  | .D_2 => "再"
  | .D_3 => "三 (作算子)"
  | .D_4 => "兩 / 两"
  | .D_5 => "倍"
  | .D_6 => "半"
  | .D_7 => "全"
  | .D_8 => "餘 / 余"
  | .D_9 => "終 / 终 (作量词层)"
  | .D_10 => "過半 / 大半"
  | .E_1 => "書 / 书"
  | .E_2 => "曰"
  | .E_3 => "稱 / 称"
  | .E_4 => "諱 / 讳"
  | .E_5 => "譏 / 讥"
  | .E_6 => "與 / 与 (春秋层)"
  | .E_7 => "削"
  | .E_8 => "筆 / 笔"
  | .E_9 => "褒 / 貶"
  | .L_1 => "法 (法家版)"
  | .L_2 => "術 / 术"
  | .L_3 => "勢 / 势 (法家版)"
  | .L_4 => "形名 (paired)"
  | .L_5 => "參同 / 参同 (参验)"
  | .L_6 => "二柄 (刑/德)"
  | .L_7 => "因 (法家版)"
  | .L_8 => "任"
  | .L_9 => "守"
  | .L_10 => "靜 / 静 (法家版)"
  | .L_11 => "無為 / 无为 (法家版)"
  | .L_12 => "利"
  | .L_13 => "一 (法家版: 法令统一)"
  | .L_14 => "制"
  | .L_15 => "度 (法家版)"
  | .L_16 => "罰 / 赏"
  | .Y_1 => "陰 / 阴 与 陽 / 阳"
  | .Y_2 => "五行 (木火土金水)"
  | .Y_3 => "相生"
  | .Y_4 => "相克 (相剋)"
  | .Y_5 => "相侮 / 反侮"
  | .Y_6 => "氣 / 气"
  | .Y_7 => "血"
  | .Y_8 => "精"
  | .Y_9 => "神"
  | .Y_10 => "升 / 降 (医家专版)"
  | .Y_11 => "開 / 闔 / 樞 (开/合/枢 三才)"
  | .Y_12 => "經 / 经 与 絡 / 络"
  | .Y_13 => "表 / 裡 (医家专版)"
  | .Y_14 => "寒 / 熱 (热)"
  | .Y_15 => "虛 / 實 (虚/实)"
  | .Y_16 => "補 / 瀉 (补/泻)"
  | .Y_17 => "平"
  | .Y_18 => "和"
  | .Y_19 => "調 / 调"
  | .Y_20 => "順 / 逆 (顺/逆)"
  | .Y_21 => "標 / 本 (标/本)"
  | .Y_22 => "營 / 营 与 衛 / 卫"
  | .Y_23 => "通 / 滯 (通/滞)"
  | .Y_24 => "五运六气"
  | .Y_25 => "上工 / 中工 / 下工"
  | .Y_26 => "出 / 入 (医家专版)"
  | .Y_27 => "候"
  | .Y_28 => "治"
  | .X_1 => "性"
  | .X_2 => "偽 / 伪"
  | .X_3 => "化性 (起伪)"
  | .X_4 => "群"
  | .X_5 => "分 (荀子社会版)"
  | .X_6 => "礼"
  | .X_7 => "義 / 义"
  | .X_8 => "別 / 别 (荀子版)"
  | .X_9 => "制 (荀子社会版)"
  | .X_10 => "隆 / 殺"
  | .X_11 => "化 (荀子版)"
  | .X_12 => "名分"
  | .X_13 => "解 (蔽)"
  | .X_14 => "積 / 积"
  | .X_15 => "學 / 学"
  | .X_16 => "教"
  | .Z_1 => "因 (一般)"
  | .Z_2 => "相 (mutuality prefix)"
  | .Z_3 => "互"
  | .Z_4 => "交"
  | .Z_5 => "錯 / 错"
  | .Z_6 => "綜 / 综"
  | .Z_7 => "雜 / 杂"
  | .Z_8 => "隱 / 隐"
  | .Z_9 => "顯 / 显 (見/见 - xiàn 读)"
  | .Z_10 => "藏"
  | .Z_11 => "露"
  | .Z_12 => "守"
  | .Z_13 => "持"
  | .Z_14 => "居"
  | .Z_15 => "處 / 处"
  | .Z_16 => "聚"
  | .Z_17 => "集"
  | .Z_18 => "散"
  | .Z_19 => "積 / 积"
  | .Z_20 => "引"
  | .Z_21 => "攝 / 摄"
  | .Z_22 => "蘊 / 蕴"
  | .Z_23 => "萌"
  | .Z_24 => "兆"
  | .Z_25 => "苗"
  | .Z_26 => "占"
  | .Z_27 => "卜"
  | .Z_28 => "演"
  | .Z_29 => "推 (复用 T-10) — 算子上的推"
  | .Z_30 => "譬 / 喻"
  | .Z_31 => "反 (作算子上的算子)"
  | .Z_32 => "自"
  | .Z_33 => "自反 / 反自 (合成)"
  | .Z_34 => "觀 / 观"
  | .Z_35 => "察"
  | .Z_36 => "明"
  | .Z_37 => "蔽"
  | .Z_38 => "悟"
  | .Z_39 => "識 / 识"
  | .Z_40 => "知 (作算子)"

def operatorForms : OperatorId -> List GlyphSense
  | .R_1 => textToSenses "在"
  | .R_2 => textToSenses "屬属"
  | .R_3 => textToSenses "際际"
  | .R_4 => textToSenses "間间"
  | .R_5 => textToSenses "中"
  | .R_6 => textToSenses "正"
  | .R_7 => textToSenses "應应"
  | .R_8 => textToSenses "比"
  | .R_9 => textToSenses "承"
  | .R_10 => textToSenses "乘"
  | .R_11 => textToSenses "對对"
  | .R_12 => textToSenses "偶耦"
  | .R_13 => textToSenses "並并"
  | .R_14 => textToSenses "與与"
  | .R_15 => textToSenses "偕"
  | .C_1 => textToSenses "含"
  | .C_2 => textToSenses "包"
  | .C_3 => textToSenses "容"
  | .C_4 => textToSenses "中"
  | .C_5 => textToSenses "外"
  | .C_6 => textToSenses "內内"
  | .C_7 => textToSenses "表"
  | .C_8 => textToSenses "裡里"
  | .T_1 => textToSenses "化"
  | .T_2 => textToSenses "變变"
  | .T_3 => textToSenses "易"
  | .T_4 => textToSenses "革"
  | .T_5 => textToSenses "改"
  | .T_6 => textToSenses "反"
  | .T_7 => textToSenses "復复"
  | .T_8 => textToSenses "還还"
  | .T_9 => textToSenses "轉转"
  | .T_10 => textToSenses "推"
  | .T_11 => textToSenses "致"
  | .T_12 => textToSenses "損损"
  | .T_13 => textToSenses "益"
  | .T_14 => textToSenses "屈"
  | .T_15 => textToSenses "伸"
  | .F_1 => textToSenses "往"
  | .F_2 => textToSenses "來来"
  | .F_3 => textToSenses "進进"
  | .F_4 => textToSenses "退"
  | .F_5 => textToSenses "升"
  | .F_6 => textToSenses "降"
  | .F_7 => textToSenses "出"
  | .F_8 => textToSenses "入"
  | .F_9 => [«行1»]
  | .F_10 => textToSenses "動动"
  | .F_11 => textToSenses "靜静"
  | .F_12 => textToSenses "通"
  | .B_1 => textToSenses "始"
  | .B_2 => textToSenses "終终"
  | .B_3 => textToSenses "起"
  | .B_4 => textToSenses "止"
  | .B_5 => textToSenses "立"
  | .B_6 => textToSenses "成"
  | .B_7 => textToSenses "極极"
  | .B_8 => textToSenses "節节"
  | .Q_1 => [«凡1»]
  | .Q_2 => [«皆1»]
  | .Q_3 => textToSenses "各"
  | .Q_4 => textToSenses "莫"
  | .Q_5 => [«或1»]
  | .Q_6 => [«有1»]
  | .Q_7 => [«無1», «无1»]
  | .Q_8 => textToSenses "唯"
  | .K_1 => [«故1»]
  | .K_2 => [«由1»]
  | .K_3 => [«自1»]
  | .K_4 => textToSenses "至"
  | .K_5 => textToSenses "致"
  | .K_6 => textToSenses "使"
  | .K_7 => textToSenses "令"
  | .K_8 => [«以1»]
  | .M_1 => textToSenses "必"
  | .M_2 => [«或1»]
  | .M_3 => [«當1», «当1»]
  | .M_4 => [«宜1»]
  | .M_5 => [«可1»]
  | .M_6 => [«能1»]
  | .M_7 => textToSenses "得"
  | .M_8 => textToSenses "應应"
  | .N_1 => [«不1»]
  | .N_2 => [«非1»]
  | .N_3 => textToSenses "弗"
  | .N_4 => textToSenses "勿"
  | .N_5 => textToSenses "毋"
  | .N_6 => textToSenses "反"
  | .N_7 => textToSenses "異异"
  | .N_8 => textToSenses "別别"
  | .I_1 => textToSenses "同"
  | .I_2 => textToSenses "一"
  | .I_3 => [«即1»]
  | .I_4 => [«是1»]
  | .I_5 => [«為1», «为1»]
  | .I_6 => textToSenses "分"
  | .I_7 => [«合1»]
  | .I_8 => textToSenses "別"
  | .I_9 => [«系1»]
  | .S_1 => [«之1»]
  | .S_2 => textToSenses "而"
  | .S_3 => [«則1», «则1»]
  | .S_4 => [«若1»]
  | .S_5 => textToSenses "雖虽"
  | .S_6 => textToSenses "然"
  | .S_7 => [«故1»]
  | .S_8 => [«乃1»]
  | .S_9 => textToSenses "既"
  | .S_10 => textToSenses "將将"
  | .S_11 => textToSenses "方"
  | .S_12 => textToSenses "嘗尝"
  | .S_13 => [«者1»]
  | .S_14 => [«也1»]
  | .S_15 => [«于1», «於1»]
  | .S_16 => [«所1»]
  | .S_17 => [«未1»]
  | .S_18 => [«已1»]
  | .S_19 => [«的1»]
  | .S_20 => [«地1»]
  | .H_1 => textToSenses "道"
  | .H_2 => textToSenses "理"
  | .H_3 => textToSenses "勢势"
  | .H_4 => textToSenses "機机"
  | .H_5 => [«法1»]
  | .H_6 => textToSenses "象"
  | .H_7 => textToSenses "名"
  | .H_8 => textToSenses "體体与用"
  | .P_1 => [«故1»]
  | .P_2 => textToSenses "體体"
  | .P_3 => textToSenses "兼"
  | .P_4 => textToSenses "同"
  | .P_5 => textToSenses "異异"
  | .P_6 => textToSenses "久"
  | .P_7 => textToSenses "宇"
  | .P_8 => textToSenses "動"
  | .P_9 => textToSenses "止"
  | .P_10 => textToSenses "端"
  | .P_11 => textToSenses "尺"
  | .P_12 => textToSenses "中"
  | .P_13 => textToSenses "圜圆"
  | .P_14 => textToSenses "平"
  | .P_15 => textToSenses "攖撄"
  | .P_16 => textToSenses "仳"
  | .P_17 => textToSenses "次"
  | .P_18 => [«法1»]
  | .P_19 => textToSenses "名"
  | .P_20 => textToSenses "知"
  | .P_21 => textToSenses "辭辞"
  | .P_22 => textToSenses "說说"
  | .P_23 => textToSenses "辯辩"
  | .P_24 => textToSenses "類类"
  | .G_1 => textToSenses "指"
  | .G_2 => textToSenses "物"
  | .G_3 => textToSenses "名"
  | .G_4 => textToSenses "實实"
  | .G_5 => textToSenses "位"
  | .G_6 => textToSenses "正"
  | .G_7 => textToSenses "離离"
  | .G_8 => textToSenses "兼合"
  | .G_9 => textToSenses "別别"
  | .G_10 => textToSenses "然"
  | .G_11 => textToSenses "命"
  | .A_1 => textToSenses "漸渐"
  | .A_2 => textToSenses "驟骤"
  | .A_3 => textToSenses "忽"
  | .A_4 => textToSenses "遂"
  | .A_5 => textToSenses "復复"
  | .A_6 => textToSenses "又"
  | .A_7 => textToSenses "屢屡"
  | .A_8 => textToSenses "愈"
  | .A_9 => textToSenses "益"
  | .A_10 => textToSenses "寖浸"
  | .A_11 => textToSenses "既又一且"
  | .A_12 => textToSenses "且"
  | .A_13 => textToSenses "但"
  | .A_14 => textToSenses "唯"
  | .A_15 => textToSenses "亦"
  | .A_16 => [«已1»]
  | .A_17 => [«未1»]
  | .A_18 => textToSenses "將将"
  | .A_19 => textToSenses "方"
  | .A_20 => textToSenses "嘗尝"
  | .D_1 => textToSenses "一"
  | .D_2 => textToSenses "再"
  | .D_3 => textToSenses "三"
  | .D_4 => textToSenses "兩两"
  | .D_5 => textToSenses "倍"
  | .D_6 => textToSenses "半"
  | .D_7 => textToSenses "全"
  | .D_8 => textToSenses "餘余"
  | .D_9 => textToSenses "終终"
  | .D_10 => textToSenses "過过半大"
  | .E_1 => textToSenses "書书"
  | .E_2 => textToSenses "曰"
  | .E_3 => textToSenses "稱称"
  | .E_4 => textToSenses "諱讳"
  | .E_5 => textToSenses "譏讥"
  | .E_6 => textToSenses "與与"
  | .E_7 => textToSenses "削"
  | .E_8 => textToSenses "筆笔"
  | .E_9 => textToSenses "褒貶贬"
  | .L_1 => [«法1»]
  | .L_2 => textToSenses "術术"
  | .L_3 => textToSenses "勢势"
  | .L_4 => textToSenses "形名"
  | .L_5 => textToSenses "參同参同"
  | .L_6 => textToSenses "二柄"
  | .L_7 => textToSenses "因"
  | .L_8 => textToSenses "任"
  | .L_9 => textToSenses "守"
  | .L_10 => textToSenses "靜静"
  | .L_11 => textToSenses "無為无为"
  | .L_12 => textToSenses "利"
  | .L_13 => textToSenses "一"
  | .L_14 => textToSenses "制"
  | .L_15 => textToSenses "度"
  | .L_16 => textToSenses "罰赏"
  | .Y_1 => textToSenses "陰阴与陽阳"
  | .Y_2 => textToSenses "五行"
  | .Y_3 => textToSenses "相生"
  | .Y_4 => textToSenses "相克"
  | .Y_5 => textToSenses "相侮反侮"
  | .Y_6 => textToSenses "氣气"
  | .Y_7 => textToSenses "血"
  | .Y_8 => textToSenses "精"
  | .Y_9 => textToSenses "神"
  | .Y_10 => textToSenses "升降"
  | .Y_11 => textToSenses "開闔樞"
  | .Y_12 => textToSenses "經经与絡络"
  | .Y_13 => textToSenses "表裡"
  | .Y_14 => textToSenses "寒熱"
  | .Y_15 => textToSenses "虛實"
  | .Y_16 => textToSenses "補补瀉泻"
  | .Y_17 => textToSenses "平"
  | .Y_18 => [«和1»]
  | .Y_19 => textToSenses "調调"
  | .Y_20 => textToSenses "順逆"
  | .Y_21 => textToSenses "標标本"
  | .Y_22 => textToSenses "營营与衛卫"
  | .Y_23 => textToSenses "通滯"
  | .Y_24 => textToSenses "五运六气"
  | .Y_25 => textToSenses "上工中工下工"
  | .Y_26 => textToSenses "出入"
  | .Y_27 => textToSenses "候"
  | .Y_28 => textToSenses "治"
  | .X_1 => textToSenses "性"
  | .X_2 => textToSenses "偽伪"
  | .X_3 => textToSenses "化性"
  | .X_4 => textToSenses "群"
  | .X_5 => textToSenses "分"
  | .X_6 => textToSenses "礼"
  | .X_7 => textToSenses "義义"
  | .X_8 => textToSenses "別别"
  | .X_9 => textToSenses "制"
  | .X_10 => textToSenses "隆殺"
  | .X_11 => textToSenses "化"
  | .X_12 => textToSenses "名分"
  | .X_13 => textToSenses "解"
  | .X_14 => textToSenses "積积"
  | .X_15 => textToSenses "學学"
  | .X_16 => textToSenses "教"
  | .Z_1 => textToSenses "因"
  | .Z_2 => textToSenses "相"
  | .Z_3 => textToSenses "互"
  | .Z_4 => textToSenses "交"
  | .Z_5 => textToSenses "錯错"
  | .Z_6 => textToSenses "綜综"
  | .Z_7 => textToSenses "雜杂"
  | .Z_8 => textToSenses "隱隐"
  | .Z_9 => textToSenses "顯显"
  | .Z_10 => textToSenses "藏"
  | .Z_11 => textToSenses "露"
  | .Z_12 => textToSenses "守"
  | .Z_13 => textToSenses "持"
  | .Z_14 => textToSenses "居"
  | .Z_15 => textToSenses "處处"
  | .Z_16 => textToSenses "聚"
  | .Z_17 => textToSenses "集"
  | .Z_18 => textToSenses "散"
  | .Z_19 => textToSenses "積积"
  | .Z_20 => textToSenses "引"
  | .Z_21 => textToSenses "攝摄"
  | .Z_22 => textToSenses "蘊蕴"
  | .Z_23 => textToSenses "萌"
  | .Z_24 => textToSenses "兆"
  | .Z_25 => textToSenses "苗"
  | .Z_26 => textToSenses "占"
  | .Z_27 => textToSenses "卜"
  | .Z_28 => textToSenses "演"
  | .Z_29 => textToSenses "推"
  | .Z_30 => textToSenses "譬喻"
  | .Z_31 => textToSenses "反"
  | .Z_32 => [«自1»]
  | .Z_33 => textToSenses "自反反自"
  | .Z_34 => textToSenses "觀观"
  | .Z_35 => textToSenses "察"
  | .Z_36 => textToSenses "明"
  | .Z_37 => textToSenses "蔽"
  | .Z_38 => textToSenses "悟"
  | .Z_39 => textToSenses "識识"
  | .Z_40 => textToSenses "知"

def operatorEntry (id : OperatorId) : OperatorEntry :=
  { id := id, code := id.code, title := id.title, group := id.group,
    forms := operatorForms id, signature := .placeholder }

def allOperatorIds : List OperatorId := [
  .R_1, .R_2, .R_3, .R_4, .R_5, .R_6, .R_7, .R_8,
  .R_9, .R_10, .R_11, .R_12, .R_13, .R_14, .R_15, .C_1,
  .C_2, .C_3, .C_4, .C_5, .C_6, .C_7, .C_8, .T_1,
  .T_2, .T_3, .T_4, .T_5, .T_6, .T_7, .T_8, .T_9,
  .T_10, .T_11, .T_12, .T_13, .T_14, .T_15, .F_1, .F_2,
  .F_3, .F_4, .F_5, .F_6, .F_7, .F_8, .F_9, .F_10,
  .F_11, .F_12, .B_1, .B_2, .B_3, .B_4, .B_5, .B_6,
  .B_7, .B_8, .Q_1, .Q_2, .Q_3, .Q_4, .Q_5, .Q_6,
  .Q_7, .Q_8, .K_1, .K_2, .K_3, .K_4, .K_5, .K_6,
  .K_7, .K_8, .M_1, .M_2, .M_3, .M_4, .M_5, .M_6,
  .M_7, .M_8, .N_1, .N_2, .N_3, .N_4, .N_5, .N_6,
  .N_7, .N_8, .I_1, .I_2, .I_3, .I_4, .I_5, .I_6,
  .I_7, .I_8, .I_9, .S_1, .S_2, .S_3, .S_4, .S_5, .S_6,
  .S_7, .S_8, .S_9, .S_10, .S_11, .S_12, .S_13, .S_14,
  .S_15, .S_16, .S_17, .S_18, .S_19, .S_20, .H_1, .H_2,
  .H_3, .H_4, .H_5, .H_6, .H_7, .H_8, .P_1, .P_2,
  .P_3, .P_4, .P_5, .P_6, .P_7, .P_8, .P_9, .P_10,
  .P_11, .P_12, .P_13, .P_14, .P_15, .P_16, .P_17, .P_18,
  .P_19, .P_20, .P_21, .P_22, .P_23, .P_24, .G_1, .G_2,
  .G_3, .G_4, .G_5, .G_6, .G_7, .G_8, .G_9, .G_10,
  .G_11, .A_1, .A_2, .A_3, .A_4, .A_5, .A_6, .A_7,
  .A_8, .A_9, .A_10, .A_11, .A_12, .A_13, .A_14, .A_15,
  .A_16, .A_17, .A_18, .A_19, .A_20, .D_1, .D_2, .D_3,
  .D_4, .D_5, .D_6, .D_7, .D_8, .D_9, .D_10, .E_1,
  .E_2, .E_3, .E_4, .E_5, .E_6, .E_7, .E_8, .E_9,
  .L_1, .L_2, .L_3, .L_4,
  .L_5, .L_6, .L_7, .L_8, .L_9, .L_10, .L_11, .L_12,
  .L_13, .L_14, .L_15, .L_16, .Y_1, .Y_2, .Y_3, .Y_4,
  .Y_5, .Y_6, .Y_7, .Y_8, .Y_9, .Y_10, .Y_11, .Y_12,
  .Y_13, .Y_14, .Y_15, .Y_16, .Y_17, .Y_18, .Y_19, .Y_20,
  .Y_21, .Y_22, .Y_23, .Y_24, .Y_25, .Y_26, .Y_27, .Y_28,
  .X_1, .X_2, .X_3, .X_4, .X_5, .X_6, .X_7, .X_8,
  .X_9, .X_10, .X_11, .X_12, .X_13, .X_14, .X_15, .X_16,
  .Z_1, .Z_2, .Z_3, .Z_4, .Z_5,
  .Z_6, .Z_7, .Z_8, .Z_9, .Z_10, .Z_11, .Z_12, .Z_13,
  .Z_14, .Z_15, .Z_16, .Z_17, .Z_18, .Z_19, .Z_20, .Z_21,
  .Z_22, .Z_23, .Z_24, .Z_25, .Z_26, .Z_27, .Z_28, .Z_29,
  .Z_30, .Z_31, .Z_32, .Z_33, .Z_34, .Z_35, .Z_36, .Z_37,
  .Z_38, .Z_39, .Z_40,
]

def SignatureStatus.admissible : SignatureStatus -> Prop
  | .given => True
  | .placeholder => True
  | .pending => True

instance signatureStatusAdmissibleDecidable (s : SignatureStatus) :
    Decidable (s.admissible) := by
  cases s <;> exact isTrue trivial

def CoveredOperator (id : OperatorId) : Prop :=
  let e := operatorEntry id
  e.id = id ∧ e.forms ≠ [] ∧ RegisteredForms e.forms ∧
    e.group = id.group ∧ e.signature.admissible

instance coveredOperatorDecidable (id : OperatorId) : Decidable (CoveredOperator id) := by
  unfold CoveredOperator
  infer_instance

theorem allOperatorIds_complete (id : OperatorId) : id ∈ allOperatorIds := by
  cases id <;> decide

theorem operator_table_complete (id : OperatorId) : CoveredOperator id := by
  cases id <;> native_decide

end SSBX.Text.WenyanOperators
