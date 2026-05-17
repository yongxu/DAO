import SSBX.Text.WenyanOperators.Group
import SSBX.Text.WenyanOperators.Code
import SSBX.Text.WenyanOperators.Title
import SSBX.Text.WenyanOperators.Forms

namespace SSBX.Text.WenyanOperators

open SSBX.Text.Glyph

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
  .S_15, .S_16, .S_17, .S_18, .S_19, .S_20,
  .S_21, .S_22, .S_23, .S_24, .H_1, .H_2,
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
  .Z_38, .Z_39, .Z_40, .ZHU_1, .ZHU_2, .ZHU_3, .ZHU_4,
  .ZHU_5, .ZHU_6, .ZHU_7, .ZHU_8, .ZHU_9, .ZHU_10, .ZHU_11,
  .ZHU_12, .SUN_1, .SUN_2, .SUN_3, .SUN_4, .SUN_5, .SUN_6,
  .SUN_7, .SUN_8, .SUN_9, .SUN_10, .SUN_11, .SUN_12, .SUN_13,
  .SUN_14, .CHU_1, .CHU_2, .CHU_3, .CHU_4, .CHU_5, .CHU_6,
  .CHU_7, .CHU_8, .CHU_9, .CHU_10, .LIJ_1, .LIJ_2, .LIJ_3,
  .LIJ_4, .LIJ_5, .LIJ_6, .LIJ_7, .LIJ_8, .LIJ_9, .LIJ_10,
  .LIJ_11, .LIJ_12, .LIJ_13, .LIJ_14, .ZA_1, .ZA_2, .ZA_3,
  .ZA_4, .ZA_5, .ZA_6, .ZA_7, .ZA_8, .ZA_9, .ZA_10, .ZA_11,
  .ZA_12, .ZA_13, .ZA_14, .ZA_15, .ZA_16, .ZA_17, .ZA_18,
  .ZA_19, .ZA_20,
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

end SSBX.Text.WenyanOperators
