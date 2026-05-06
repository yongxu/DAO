## 〇五、$\Pi_{\mathrm{开}}$ 的场景化投影协议

$\Pi_{\mathrm{开}}$ 不直接给“真理”，而给可审校的投影包。

$$
\Pi_{\mathrm{开}}(\Gamma;s,\omega)
:=
\left(
U,A,R,T,
\mathcal{O}_F,
\mathsf{status},
\mathsf{evidence},
\mathsf{model}
\right)
$$

其中：

$$
\mathcal{O}_F
:=
\mathcal{M}_{\Omega}(U,A,R,T)
$$

状态判定采用双阈值：

$$
\mathsf{status}
=
\begin{cases}
\top, & \mathcal{O}_F\ge\theta_{\mathrm{开}}^+
\;\wedge\;
\min(U,A,R,T)\ge\theta_{\mathrm{维}}^+ \\
\bot, & \mathcal{O}_F<\theta_{\mathrm{开}}^-
\;\vee\;
\min(U,A,R,T)<\theta_{\mathrm{维}}^- \\
\mathsf{U}, & \text{otherwise}
\end{cases}
$$

投影步骤：

1. 从 $\mathcal{H}_t$ 与当前观测构造候间；
2. 用 $\mathrm{史法}_F,\mathrm{暂法}_F,\mathrm{开维法}_F$ 生成 $I_F(\Gamma;s,\omega)$；
3. 抽取 $U,A,R,T$；
4. 选 $\Omega$ 并求 $\mathcal{O}_F$；
5. 记录证据、模型、阈值、数据缺口；
6. 输出 $\top,\bot,\mathsf{U}$。

对行动 $i$，投影后场：

$$
\Gamma_i:=\Gamma\oplus_F i
$$

$$
\Pi_{\mathrm{开}}^i
:=
\Pi_{\mathrm{开}}(\Gamma_i;s,\omega)
$$

机判定可运行化为：

$$
\mathrm{机}(\Gamma;s,\omega)
\iff
\exists i\ne j\in I_F(\Gamma;s,\omega):
\Pi_{\mathrm{开}}^i.\mathsf{status}
\ne
\Pi_{\mathrm{开}}^j.\mathsf{status}
$$

或连续化为：

$$
\left|
\Pi_{\mathrm{开}}^i.\mathcal{O}_F
-
\Pi_{\mathrm{开}}^j.\mathcal{O}_F
\right|
\ge
\theta_{\mathrm{机差}}
$$

