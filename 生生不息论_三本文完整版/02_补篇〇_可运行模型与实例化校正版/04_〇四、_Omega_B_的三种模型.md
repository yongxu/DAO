## 〇四、$\Omega_B$ 的三种模型

设共同体 $B$ 中每个受者或聚焦的开度为：

$$
o_a:=\mathcal{O}_a(\Gamma;s,\omega),\qquad a\in B
$$

再设：

$$
O_F:=\mathcal{O}_F(\Gamma;s,\omega)
$$

$$
D_B:=\mathrm{存异度}(B,\Gamma;s,\omega)\in[0,1]
$$

$$
N_B:=1-\mathrm{夺度}(B,\Gamma;s,\omega)\in[0,1]
$$

其中 $D_B$ 防同化，$N_B$ 防夺。

### 一、共开短板模型 $\Omega_{B,\min}$

$$
\Omega_{B,\min}
:=
\min
\left(
O_F,\;
D_B,\;
N_B,\;
\min_{a\in B}o_a
\right)
$$

用处：权利、生命、不可逆伤害、高风险 AI 或制度场景。

### 二、共开 Nash 模型 $\Omega_{B,\mathrm{nash}}$

设：

$$
\sum_{a\in B}\nu_a+\beta_F+\beta_D+\beta_N=1
$$

且各权重皆为正。定义：

$$
\Omega_{B,\mathrm{nash}}
:=
O_F^{\beta_F}
D_B^{\beta_D}
N_B^{\beta_N}
\prod_{a\in B}o_a^{\nu_a}
$$

用处：多主体协作、市场制度、组织治理。  
其乘积结构保证任一重要受者被牺牲时，共开度下降。

### 三、分位模型 $\Omega_{B,q}$

设 $Q_q(\{o_a\}_{a\in B})$ 为 $q$ 分位数，常取：

$$
q\in[0.1,0.25]
$$

定义：

$$
\Omega_{B,q}
:=
\min
\left(
O_F,\;
D_B,\;
N_B,\;
Q_q(\{o_a\}_{a\in B})
\right)
$$

用处：群体很大时，避免单个极端值支配全局，同时仍关注低位群体。

### 共开选模律

$$
\mathcal{M}_{\Omega_B}\in
\{
\Omega_{B,\min},
\Omega_{B,\mathrm{nash}},
\Omega_{B,q}
\}
$$

若涉及基本权利、不可逆损害、儿童、医疗、司法、战争、高风险自动化，默认：

$$
\mathcal{M}_{\Omega_B}:=\Omega_{B,\min}
$$

