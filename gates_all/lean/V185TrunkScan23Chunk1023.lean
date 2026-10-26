import V185TrunkScan23Chunk1022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6056357 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_6056357 : Nat := 118140960795 + 6056357 * 2 ^ 59
def prefixEnd_6056357 : Nat := 4983230072969 + 3 ^ 40 * 6056357 * 2
def baseEnd_6056357 : Nat := 3109822156222066209084827

theorem tailTrace_6056357 : CollatzResearch.WordTrace tailWord_6056357 prefixEnd_6056357 3109822156222066209084827 := by
  unfold tailWord_6056357
  simp only [CollatzResearch.WordTrace]
  refine ⟨220893486919860407272423325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147262324613240271514948883 220893486919860407272423325)
  ·
    refine ⟨82835057594947652727158747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220893486919860407272423325 82835057594947652727158747)
    ·
      refine ⟨124252586392421479090738121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82835057594947652727158747 124252586392421479090738121)
      ·
        refine ⟨93189439794316109318053591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124252586392421479090738121 93189439794316109318053591)
        ·
          refine ⟨139784159691474163977080387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93189439794316109318053591 139784159691474163977080387)
          ·
            refine ⟨209676239537211245965620581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139784159691474163977080387 209676239537211245965620581)
            ·
              refine ⟨39314294913227108618553859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209676239537211245965620581 39314294913227108618553859)
              ·
                refine ⟨58971442369840662927830789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39314294913227108618553859 58971442369840662927830789)
                ·
                  refine ⟨11057145444345124298968273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58971442369840662927830789 11057145444345124298968273)
                  ·
                    refine ⟨8292859083258843224226205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11057145444345124298968273 8292859083258843224226205)
                    ·
                      refine ⟨3109822156222066209084827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8292859083258843224226205 3109822156222066209084827)
                      ·
                        rfl

theorem cell23_6056357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_6056357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056357 prefixEnd_6056357 := by exact prefixLift 6056357
  have htrace : WordTrace (prefixWord ++ tailWord_6056357) baseStart_6056357 baseEnd_6056357 := by
    simpa [prefixWord, tailWord_6056357, baseEnd_6056357] using wordTrace_append hprefix tailTrace_6056357
  have hstable : (prefixWord ++ tailWord_6056357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056357).length < 2 ^ (prefixWord ++ tailWord_6056357).sum := by decide
  have hdescent : baseEnd_6056357 < baseStart_6056357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056400 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_6056400 : Nat := 118140960795 + 6056400 * 2 ^ 59
def prefixEnd_6056400 : Nat := 4983230072969 + 3 ^ 40 * 6056400 * 2
def baseEnd_6056400 : Nat := 3109844235890209540847129

theorem tailTrace_6056400 : CollatzResearch.WordTrace tailWord_6056400 prefixEnd_6056400 3109844235890209540847129 := by
  unfold tailWord_6056400
  simp only [CollatzResearch.WordTrace]
  refine ⟨110447527629352312808119327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147263370172469750410825769 110447527629352312808119327)
  ·
    refine ⟨165671291444028469212178991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110447527629352312808119327 165671291444028469212178991)
    ·
      refine ⟨248506937166042703818268487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165671291444028469212178991 248506937166042703818268487)
      ·
        refine ⟨372760405749064055727402731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248506937166042703818268487 372760405749064055727402731)
        ·
          refine ⟨559140608623596083591104097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372760405749064055727402731 559140608623596083591104097)
          ·
            refine ⟨419355456467697062693328073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559140608623596083591104097 419355456467697062693328073)
            ·
              refine ⟨314516592350772797019996055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419355456467697062693328073 314516592350772797019996055)
              ·
                refine ⟨471774888526159195529994083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314516592350772797019996055 471774888526159195529994083)
                ·
                  refine ⟨707662332789238793294991125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471774888526159195529994083 707662332789238793294991125)
                  ·
                    refine ⟨33171671849495568435702709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 707662332789238793294991125 33171671849495568435702709)
                    ·
                      refine ⟨3109844235890209540847129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33171671849495568435702709 3109844235890209540847129)
                      ·
                        rfl

theorem cell23_6056400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_6056400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056400 prefixEnd_6056400 := by exact prefixLift 6056400
  have htrace : WordTrace (prefixWord ++ tailWord_6056400) baseStart_6056400 baseEnd_6056400 := by
    simpa [prefixWord, tailWord_6056400, baseEnd_6056400] using wordTrace_append hprefix tailTrace_6056400
  have hstable : (prefixWord ++ tailWord_6056400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056400).length < 2 ^ (prefixWord ++ tailWord_6056400).sum := by decide
  have hdescent : baseEnd_6056400 < baseStart_6056400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056427 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4]
def baseStart_6056427 : Nat := 118140960795 + 6056427 * 2 ^ 59
def prefixEnd_6056427 : Nat := 4983230072969 + 3 ^ 40 * 6056427 * 2
def baseEnd_6056427 : Nat := 3109858099867880935209505

theorem tailTrace_6056427 : CollatzResearch.WordTrace tailWord_6056427 prefixEnd_6056427 3109858099867880935209505 := by
  unfold tailWord_6056427
  simp only [CollatzResearch.WordTrace]
  refine ⟨220896040029606809227471535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147264026686404539484981023 220896040029606809227471535)
  ·
    refine ⟨331344060044410213841207303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220896040029606809227471535 331344060044410213841207303)
    ·
      refine ⟨497016090066615320761810955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331344060044410213841207303 497016090066615320761810955)
      ·
        refine ⟨745524135099922981142716433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497016090066615320761810955 745524135099922981142716433)
        ·
          refine ⟨559143101324942235857037325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745524135099922981142716433 559143101324942235857037325)
          ·
            refine ⟨209678662996853338446388997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559143101324942235857037325 209678662996853338446388997)
            ·
              refine ⟨39314749311910000958697937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209678662996853338446388997 39314749311910000958697937)
              ·
                refine ⟨29486061983932500719023453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39314749311910000958697937 29486061983932500719023453)
                ·
                  refine ⟨11057273243974687769633795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29486061983932500719023453 11057273243974687769633795)
                  ·
                    refine ⟨16585909865962031654450693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11057273243974687769633795 16585909865962031654450693)
                    ·
                      refine ⟨3109858099867880935209505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16585909865962031654450693 3109858099867880935209505)
                      ·
                        rfl

theorem cell23_6056427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_6056427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056427 prefixEnd_6056427 := by exact prefixLift 6056427
  have htrace : WordTrace (prefixWord ++ tailWord_6056427) baseStart_6056427 baseEnd_6056427 := by
    simpa [prefixWord, tailWord_6056427, baseEnd_6056427] using wordTrace_append hprefix tailTrace_6056427
  have hstable : (prefixWord ++ tailWord_6056427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056427).length < 2 ^ (prefixWord ++ tailWord_6056427).sum := by decide
  have hdescent : baseEnd_6056427 < baseStart_6056427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056527 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 6]
def baseStart_6056527 : Nat := 118140960795 + 6056527 * 2 ^ 59
def prefixEnd_6056527 : Nat := 4983230072969 + 3 ^ 40 * 6056527 * 2
def baseEnd_6056527 : Nat := 1036636482644443514653015

theorem tailTrace_6056527 : CollatzResearch.WordTrace tailWord_6056527 prefixEnd_6056527 1036636482644443514653015 := by
  unfold tailWord_6056527
  simp only [CollatzResearch.WordTrace]
  refine ⟨220899687329244526306111835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147266458219496350870741223 220899687329244526306111835)
  ·
    refine ⟨331349530993866789459167753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220899687329244526306111835 331349530993866789459167753)
    ·
      refine ⟨248512148245400092094375815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331349530993866789459167753 248512148245400092094375815)
      ·
        refine ⟨372768222368100138141563723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248512148245400092094375815 372768222368100138141563723)
        ·
          refine ⟨559152333552150207212345585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372768222368100138141563723 559152333552150207212345585)
          ·
            refine ⟨419364250164112655409259189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559152333552150207212345585 419364250164112655409259189)
            ·
              refine ⟨39315398452885561444618049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419364250164112655409259189 39315398452885561444618049)
              ·
                refine ⟨29486548839664171083463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39315398452885561444618049 29486548839664171083463537)
                ·
                  refine ⟨22114911629748128312597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29486548839664171083463537 22114911629748128312597653)
                  ·
                    refine ⟨1036636482644443514653015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22114911629748128312597653 1036636482644443514653015)
                    ·
                      rfl

theorem cell23_6056527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_6056527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056527 prefixEnd_6056527 := by exact prefixLift 6056527
  have htrace : WordTrace (prefixWord ++ tailWord_6056527) baseStart_6056527 baseEnd_6056527 := by
    simpa [prefixWord, tailWord_6056527, baseEnd_6056527] using wordTrace_append hprefix tailTrace_6056527
  have hstable : (prefixWord ++ tailWord_6056527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056527).length < 2 ^ (prefixWord ++ tailWord_6056527).sum := by decide
  have hdescent : baseEnd_6056527 < baseStart_6056527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056537 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_6056537 : Nat := 118140960795 + 6056537 * 2 ^ 59
def prefixEnd_6056537 : Nat := 4983230072969 + 3 ^ 40 * 6056537 * 2
def baseEnd_6056537 : Nat := 3109914582739875504833999

theorem tailTrace_6056537 : CollatzResearch.WordTrace tailWord_6056537 prefixEnd_6056537 3109914582739875504833999 := by
  unfold tailWord_6056537
  simp only [CollatzResearch.WordTrace]
  refine ⟨220900052059208298013975865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147266701372805532009317243 220900052059208298013975865)
  ·
    refine ⟨165675039044406223510481899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220900052059208298013975865 165675039044406223510481899)
    ·
      refine ⟨248512558566609335265722849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165675039044406223510481899 248512558566609335265722849)
      ·
        refine ⟨186384418924957001449292137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248512558566609335265722849 186384418924957001449292137)
        ·
          refine ⟨139788314193717751086969103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186384418924957001449292137 139788314193717751086969103)
          ·
            refine ⟨209682471290576626630453655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139788314193717751086969103 209682471290576626630453655)
            ·
              refine ⟨314523706935864939945680483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209682471290576626630453655 314523706935864939945680483)
              ·
                refine ⟨471785560403797409918520725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314523706935864939945680483 471785560403797409918520725)
                ·
                  refine ⟨22114948143928003589930659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 471785560403797409918520725 22114948143928003589930659)
                  ·
                    refine ⟨33172422215892005384895989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22114948143928003589930659 33172422215892005384895989)
                    ·
                      refine ⟨3109914582739875504833999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33172422215892005384895989 3109914582739875504833999)
                      ·
                        rfl

theorem cell23_6056537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_6056537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056537 prefixEnd_6056537 := by exact prefixLift 6056537
  have htrace : WordTrace (prefixWord ++ tailWord_6056537) baseStart_6056537 baseEnd_6056537 := by
    simpa [prefixWord, tailWord_6056537, baseEnd_6056537] using wordTrace_append hprefix tailTrace_6056537
  have hstable : (prefixWord ++ tailWord_6056537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056537).length < 2 ^ (prefixWord ++ tailWord_6056537).sum := by decide
  have hdescent : baseEnd_6056537 < baseStart_6056537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056542 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6056542 : Nat := 118140960795 + 6056542 * 2 ^ 59
def prefixEnd_6056542 : Nat := 4983230072969 + 3 ^ 40 * 6056542 * 2
def baseEnd_6056542 : Nat := 3109917150143147985271477

theorem tailTrace_6056542 : CollatzResearch.WordTrace tailWord_6056542 prefixEnd_6056542 3109917150143147985271477 := by
  unfold tailWord_6056542
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612529303023772983488485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147266822949460122578605253 27612529303023772983488485)
  ·
    refine ⟨5177349244316957434404091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27612529303023772983488485 5177349244316957434404091)
    ·
      refine ⟨7766023866475436151606137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177349244316957434404091 7766023866475436151606137)
      ·
        refine ⟨5824517899856577113704603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7766023866475436151606137 5824517899856577113704603)
        ·
          refine ⟨8736776849784865670556905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824517899856577113704603 8736776849784865670556905)
          ·
            refine ⟨6552582637338649252917679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8736776849784865670556905 6552582637338649252917679)
            ·
              refine ⟨9828873956007973879376519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6552582637338649252917679 9828873956007973879376519)
              ·
                refine ⟨14743310934011960819064779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9828873956007973879376519 14743310934011960819064779)
                ·
                  refine ⟨22114966401017941228597169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14743310934011960819064779 22114966401017941228597169)
                  ·
                    refine ⟨16586224800763455921447877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22114966401017941228597169 16586224800763455921447877)
                    ·
                      refine ⟨3109917150143147985271477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16586224800763455921447877 3109917150143147985271477)
                      ·
                        rfl

theorem cell23_6056542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6056542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056542 prefixEnd_6056542 := by exact prefixLift 6056542
  have htrace : WordTrace (prefixWord ++ tailWord_6056542) baseStart_6056542 baseEnd_6056542 := by
    simpa [prefixWord, tailWord_6056542, baseEnd_6056542] using wordTrace_append hprefix tailTrace_6056542
  have hstable : (prefixWord ++ tailWord_6056542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056542).length < 2 ^ (prefixWord ++ tailWord_6056542).sum := by decide
  have hdescent : baseEnd_6056542 < baseStart_6056542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056554 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6056554 : Nat := 118140960795 + 6056554 * 2 ^ 59
def prefixEnd_6056554 : Nat := 4983230072969 + 3 ^ 40 * 6056554 * 2
def baseEnd_6056554 : Nat := 3109923311911001938321421

theorem tailTrace_6056554 : CollatzResearch.WordTrace tailWord_6056554 prefixEnd_6056554 3109923311911001938321421 := by
  unfold tailWord_6056554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55225168025036677479336179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147267114733431139944896477 55225168025036677479336179)
  ·
    refine ⟨82837752037555016219004269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55225168025036677479336179 82837752037555016219004269)
    ·
      refine ⟨31064157014083131082126601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82837752037555016219004269 31064157014083131082126601)
      ·
        refine ⟨23298117760562348311594951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31064157014083131082126601 23298117760562348311594951)
        ·
          refine ⟨34947176640843522467392427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23298117760562348311594951 34947176640843522467392427)
          ·
            refine ⟨52420764961265283701088641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34947176640843522467392427 52420764961265283701088641)
            ·
              refine ⟨39315573720948962775816481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52420764961265283701088641 39315573720948962775816481)
              ·
                refine ⟨29486680290711722081862361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39315573720948962775816481 29486680290711722081862361)
                ·
                  refine ⟨22115010218033791561396771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29486680290711722081862361 22115010218033791561396771)
                  ·
                    refine ⟨33172515327050687342095157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22115010218033791561396771 33172515327050687342095157)
                    ·
                      refine ⟨3109923311911001938321421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33172515327050687342095157 3109923311911001938321421)
                      ·
                        rfl

theorem cell23_6056554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6056554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056554 prefixEnd_6056554 := by exact prefixLift 6056554
  have htrace : WordTrace (prefixWord ++ tailWord_6056554) baseStart_6056554 baseEnd_6056554 := by
    simpa [prefixWord, tailWord_6056554, baseEnd_6056554] using wordTrace_append hprefix tailTrace_6056554
  have hstable : (prefixWord ++ tailWord_6056554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056554).length < 2 ^ (prefixWord ++ tailWord_6056554).sum := by decide
  have hdescent : baseEnd_6056554 < baseStart_6056554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056587 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 7]
def baseStart_6056587 : Nat := 118140960795 + 6056587 * 2 ^ 59
def prefixEnd_6056587 : Nat := 4983230072969 + 3 ^ 40 * 6056587 * 2
def baseEnd_6056587 : Nat := 1036646752257533436402923

theorem tailTrace_6056587 : CollatzResearch.WordTrace tailWord_6056587 prefixEnd_6056587 1036646752257533436402923 := by
  unfold tailWord_6056587
  simp only [CollatzResearch.WordTrace]
  refine ⟨220901875709027156553296015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147267917139351437702197343 220901875709027156553296015)
  ·
    refine ⟨331352813563540734829944023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220901875709027156553296015 331352813563540734829944023)
    ·
      refine ⟨497029220345311102244916035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331352813563540734829944023 497029220345311102244916035)
      ·
        refine ⟨745543830517966653367374053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497029220345311102244916035 745543830517966653367374053)
        ·
          refine ⟨139789468222118747506382635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 745543830517966653367374053 139789468222118747506382635)
          ·
            refine ⟨209684202333178121259573953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139789468222118747506382635 209684202333178121259573953)
            ·
              refine ⟨157263151749883590944680465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209684202333178121259573953 157263151749883590944680465)
              ·
                refine ⟨117947363812412693208510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157263151749883590944680465 117947363812412693208510349)
                ·
                  refine ⟨44230261429654759953191381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117947363812412693208510349 44230261429654759953191381)
                  ·
                    refine ⟨1036646752257533436402923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44230261429654759953191381 1036646752257533436402923)
                    ·
                      rfl

theorem cell23_6056587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_6056587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056587 prefixEnd_6056587 := by exact prefixLift 6056587
  have htrace : WordTrace (prefixWord ++ tailWord_6056587) baseStart_6056587 baseEnd_6056587 := by
    simpa [prefixWord, tailWord_6056587, baseEnd_6056587] using wordTrace_append hprefix tailTrace_6056587
  have hstable : (prefixWord ++ tailWord_6056587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056587).length < 2 ^ (prefixWord ++ tailWord_6056587).sum := by decide
  have hdescent : baseEnd_6056587 < baseStart_6056587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056602 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6056602 : Nat := 118140960795 + 6056602 * 2 ^ 59
def prefixEnd_6056602 : Nat := 4983230072969 + 3 ^ 40 * 6056602 * 2
def baseEnd_6056602 : Nat := 3109947958982417750521201

theorem tailTrace_6056602 : CollatzResearch.WordTrace tailWord_6056602 prefixEnd_6056602 3109947958982417750521201 := by
  unfold tailWord_6056602
  simp only [CollatzResearch.WordTrace]
  refine ⟨55225605700993203528773015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147268281869315209410061373 55225605700993203528773015)
  ·
    refine ⟨82838408551489805293159523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55225605700993203528773015 82838408551489805293159523)
    ·
      refine ⟨124257612827234707939739285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82838408551489805293159523 124257612827234707939739285)
      ·
        refine ⟨5824575601276626934675279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124257612827234707939739285 5824575601276626934675279)
        ·
          refine ⟨8736863401914940402012919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824575601276626934675279 8736863401914940402012919)
          ·
            refine ⟨13105295102872410603019379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736863401914940402012919 13105295102872410603019379)
            ·
              refine ⟨19657942654308615904529069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105295102872410603019379 19657942654308615904529069)
              ·
                refine ⟨7371728495365730964198401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19657942654308615904529069 7371728495365730964198401)
                ·
                  refine ⟨5528796371524298223148801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7371728495365730964198401 5528796371524298223148801)
                  ·
                    refine ⟨4146597278643223667361601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5528796371524298223148801 4146597278643223667361601)
                    ·
                      refine ⟨3109947958982417750521201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146597278643223667361601 3109947958982417750521201)
                      ·
                        rfl

theorem cell23_6056602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6056602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056602 prefixEnd_6056602 := by exact prefixLift 6056602
  have htrace : WordTrace (prefixWord ++ tailWord_6056602) baseStart_6056602 baseEnd_6056602 := by
    simpa [prefixWord, tailWord_6056602, baseEnd_6056602] using wordTrace_append hprefix tailTrace_6056602
  have hstable : (prefixWord ++ tailWord_6056602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056602).length < 2 ^ (prefixWord ++ tailWord_6056602).sum := by decide
  have hdescent : baseEnd_6056602 < baseStart_6056602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_6056617 : Nat := 118140960795 + 6056617 * 2 ^ 59
def prefixEnd_6056617 : Nat := 4983230072969 + 3 ^ 40 * 6056617 * 2
def baseEnd_6056617 : Nat := 1036651887064078397277877

theorem tailTrace_6056617 : CollatzResearch.WordTrace tailWord_6056617 prefixEnd_6056617 1036651887064078397277877 := by
  unfold tailWord_6056617
  simp only [CollatzResearch.WordTrace]
  refine ⟨220902969898918471676888105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147268646599278981117925403 220902969898918471676888105)
  ·
    refine ⟨165677227424188853757666079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220902969898918471676888105 165677227424188853757666079)
    ·
      refine ⟨248515841136283280636499119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165677227424188853757666079 248515841136283280636499119)
      ·
        refine ⟨372773761704424920954748679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248515841136283280636499119 372773761704424920954748679)
        ·
          refine ⟨559160642556637381432123019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372773761704424920954748679 559160642556637381432123019)
          ·
            refine ⟨838740963834956072148184529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559160642556637381432123019 838740963834956072148184529)
            ·
              refine ⟨629055722876217054111138397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838740963834956072148184529 629055722876217054111138397)
              ·
                refine ⟨235895896078581395291676899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629055722876217054111138397 235895896078581395291676899)
                ·
                  refine ⟨353843844117872092937515349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235895896078581395291676899 353843844117872092937515349)
                  ·
                    refine ⟨1036651887064078397277877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 353843844117872092937515349 1036651887064078397277877)
                    ·
                      rfl

theorem cell23_6056617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_6056617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056617 prefixEnd_6056617 := by exact prefixLift 6056617
  have htrace : WordTrace (prefixWord ++ tailWord_6056617) baseStart_6056617 baseEnd_6056617 := by
    simpa [prefixWord, tailWord_6056617, baseEnd_6056617] using wordTrace_append hprefix tailTrace_6056617
  have hstable : (prefixWord ++ tailWord_6056617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056617).length < 2 ^ (prefixWord ++ tailWord_6056617).sum := by decide
  have hdescent : baseEnd_6056617 < baseStart_6056617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056621 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6056621 : Nat := 118140960795 + 6056621 * 2 ^ 59
def prefixEnd_6056621 : Nat := 4983230072969 + 3 ^ 40 * 6056621 * 2
def baseEnd_6056621 : Nat := 1036652571704951058727871

theorem tailTrace_6056621 : CollatzResearch.WordTrace tailWord_6056621 prefixEnd_6056621 1036652571704951058727871 := by
  unfold tailWord_6056621
  simp only [CollatzResearch.WordTrace]
  refine ⟨220903115790903980360033717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147268743860602653573355811 220903115790903980360033717)
  ·
    refine ⟨20709667105397248158753161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220903115790903980360033717 20709667105397248158753161)
    ·
      refine ⟨15532250329047936119064871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20709667105397248158753161 15532250329047936119064871)
      ·
        refine ⟨23298375493571904178597307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15532250329047936119064871 23298375493571904178597307)
        ·
          refine ⟨34947563240357856267895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23298375493571904178597307 34947563240357856267895961)
          ·
            refine ⟨26210672430268392200921971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34947563240357856267895961 26210672430268392200921971)
            ·
              refine ⟨39316008645402588301382957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26210672430268392200921971 39316008645402588301382957)
              ·
                refine ⟨14743503242025970613018609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39316008645402588301382957 14743503242025970613018609)
                ·
                  refine ⟨11057627431519477959763957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14743503242025970613018609 11057627431519477959763957)
                  ·
                    refine ⟨1036652571704951058727871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11057627431519477959763957 1036652571704951058727871)
                    ·
                      rfl

theorem cell23_6056621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6056621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056621 prefixEnd_6056621 := by exact prefixLift 6056621
  have htrace : WordTrace (prefixWord ++ tailWord_6056621) baseStart_6056621 baseEnd_6056621 := by
    simpa [prefixWord, tailWord_6056621, baseEnd_6056621] using wordTrace_append hprefix tailTrace_6056621
  have hstable : (prefixWord ++ tailWord_6056621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056621).length < 2 ^ (prefixWord ++ tailWord_6056621).sum := by decide
  have hdescent : baseEnd_6056621 < baseStart_6056621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056668 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6056668 : Nat := 118140960795 + 6056668 * 2 ^ 59
def prefixEnd_6056668 : Nat := 4983230072969 + 3 ^ 40 * 6056668 * 2
def baseEnd_6056668 : Nat := 1036660616235204830765299

theorem tailTrace_6056668 : CollatzResearch.WordTrace tailWord_6056668 prefixEnd_6056668 1036660616235204830765299 := by
  unfold tailWord_6056668
  simp only [CollatzResearch.WordTrace]
  refine ⟨110452415010866853693497329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147269886681155804924663105 110452415010866853693497329)
  ·
    refine ⟨82839311258150140270122997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110452415010866853693497329 82839311258150140270122997)
    ·
      refine ⟨7766185430451575650324031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82839311258150140270122997 7766185430451575650324031)
      ·
        refine ⟨11649278145677363475486047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766185430451575650324031 11649278145677363475486047)
        ·
          refine ⟨17473917218516045213229071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11649278145677363475486047 17473917218516045213229071)
          ·
            refine ⟨26210875827774067819843607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17473917218516045213229071 26210875827774067819843607)
            ·
              refine ⟨39316313741661101729765411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26210875827774067819843607 39316313741661101729765411)
              ·
                refine ⟨58974470612491652594648117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39316313741661101729765411 58974470612491652594648117)
                ·
                  refine ⟨5528856619921092430748261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58974470612491652594648117 5528856619921092430748261)
                  ·
                    refine ⟨1036660616235204830765299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528856619921092430748261 1036660616235204830765299)
                    ·
                      rfl

theorem cell23_6056668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6056668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056668 prefixEnd_6056668 := by exact prefixLift 6056668
  have htrace : WordTrace (prefixWord ++ tailWord_6056668) baseStart_6056668 baseEnd_6056668 := by
    simpa [prefixWord, tailWord_6056668, baseEnd_6056668] using wordTrace_append hprefix tailTrace_6056668
  have hstable : (prefixWord ++ tailWord_6056668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056668).length < 2 ^ (prefixWord ++ tailWord_6056668).sum := by decide
  have hdescent : baseEnd_6056668 < baseStart_6056668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056685 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6056685 : Nat := 118140960795 + 6056685 * 2 ^ 59
def prefixEnd_6056685 : Nat := 4983230072969 + 3 ^ 40 * 6056685 * 2
def baseEnd_6056685 : Nat := 1036663525958913641927773

theorem tailTrace_6056685 : CollatzResearch.WordTrace tailWord_6056685 prefixEnd_6056685 1036663525958913641927773 := by
  unfold tailWord_6056685
  simp only [CollatzResearch.WordTrace]
  refine ⟨220905450062672119290363509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147270300041781412860242339 220905450062672119290363509)
  ·
    refine ⟨20709885943375511183471579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220905450062672119290363509 20709885943375511183471579)
    ·
      refine ⟨31064828915063266775207369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20709885943375511183471579 31064828915063266775207369)
      ·
        refine ⟨23298621686297450081405527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31064828915063266775207369 23298621686297450081405527)
        ·
          refine ⟨34947932529446175122108291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23298621686297450081405527 34947932529446175122108291)
          ·
            refine ⟨52421898794169262683162437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34947932529446175122108291 52421898794169262683162437)
            ·
              refine ⟨9829106023906736753092957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52421898794169262683162437 9829106023906736753092957)
              ·
                refine ⟨3685914758965026282409859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9829106023906736753092957 3685914758965026282409859)
                ·
                  refine ⟨5528872138447539423614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685914758965026282409859 5528872138447539423614789)
                  ·
                    refine ⟨1036663525958913641927773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528872138447539423614789 1036663525958913641927773)
                    ·
                      rfl

theorem cell23_6056685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6056685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056685 prefixEnd_6056685 := by exact prefixLift 6056685
  have htrace : WordTrace (prefixWord ++ tailWord_6056685) baseStart_6056685 baseEnd_6056685 := by
    simpa [prefixWord, tailWord_6056685, baseEnd_6056685] using wordTrace_append hprefix tailTrace_6056685
  have hstable : (prefixWord ++ tailWord_6056685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056685).length < 2 ^ (prefixWord ++ tailWord_6056685).sum := by decide
  have hdescent : baseEnd_6056685 < baseStart_6056685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056691 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 3]
def baseStart_6056691 : Nat := 118140960795 + 6056691 * 2 ^ 59
def prefixEnd_6056691 : Nat := 4983230072969 + 3 ^ 40 * 6056691 * 2
def baseEnd_6056691 : Nat := 3109993658760667902308291

theorem tailTrace_6056691 : CollatzResearch.WordTrace tailWord_6056691 prefixEnd_6056691 3109993658760667902308291 := by
  unfold tailWord_6056691
  simp only [CollatzResearch.WordTrace]
  refine ⟨220905668900650382315081927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147270445933766921543387951 220905668900650382315081927)
  ·
    refine ⟨331358503350975573472622891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220905668900650382315081927 331358503350975573472622891)
    ·
      refine ⟨497037755026463360208934337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331358503350975573472622891 497037755026463360208934337)
      ·
        refine ⟨372778316269847520156700753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497037755026463360208934337 372778316269847520156700753)
        ·
          refine ⟨279583737202385640117525565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372778316269847520156700753 279583737202385640117525565)
          ·
            refine ⟨104843901450894615044072087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279583737202385640117525565 104843901450894615044072087)
            ·
              refine ⟨157265852176341922566108131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104843901450894615044072087 157265852176341922566108131)
              ·
                refine ⟨235898778264512883849162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157265852176341922566108131 235898778264512883849162197)
                ·
                  refine ⟨5528877615574520715214739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235898778264512883849162197 5528877615574520715214739)
                  ·
                    refine ⟨8293316423361781072822109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5528877615574520715214739 8293316423361781072822109)
                    ·
                      refine ⟨3109993658760667902308291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293316423361781072822109 3109993658760667902308291)
                      ·
                        rfl

theorem cell23_6056691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_6056691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056691 prefixEnd_6056691 := by exact prefixLift 6056691
  have htrace : WordTrace (prefixWord ++ tailWord_6056691) baseStart_6056691 baseEnd_6056691 := by
    simpa [prefixWord, tailWord_6056691, baseEnd_6056691] using wordTrace_append hprefix tailTrace_6056691
  have hstable : (prefixWord ++ tailWord_6056691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056691).length < 2 ^ (prefixWord ++ tailWord_6056691).sum := by decide
  have hdescent : baseEnd_6056691 < baseStart_6056691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056741 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_6056741 : Nat := 118140960795 + 6056741 * 2 ^ 59
def prefixEnd_6056741 : Nat := 4983230072969 + 3 ^ 40 * 6056741 * 2
def baseEnd_6056741 : Nat := 1036673110931130902227687

theorem tailTrace_6056741 : CollatzResearch.WordTrace tailWord_6056741 prefixEnd_6056741 1036673110931130902227687 := by
  unfold tailWord_6056741
  simp only [CollatzResearch.WordTrace]
  refine ⟨220907492550469240854402077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147271661700312827236268051 220907492550469240854402077)
  ·
    refine ⟨82840309706425965320400779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220907492550469240854402077 82840309706425965320400779)
    ·
      refine ⟨124260464559638947980601169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82840309706425965320400779 124260464559638947980601169)
      ·
        refine ⟨93195348419729210985450877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124260464559638947980601169 93195348419729210985450877)
        ·
          refine ⟨34948255657398454119544079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93195348419729210985450877 34948255657398454119544079)
          ·
            refine ⟨52422383486097681179316119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34948255657398454119544079 52422383486097681179316119)
            ·
              refine ⟨78633575229146521768974179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52422383486097681179316119 78633575229146521768974179)
              ·
                refine ⟨117950362843719782653461269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78633575229146521768974179 117950362843719782653461269)
                ·
                  refine ⟨5528923258299364811880997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117950362843719782653461269 5528923258299364811880997)
                  ·
                    refine ⟨1036673110931130902227687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528923258299364811880997 1036673110931130902227687)
                    ·
                      rfl

theorem cell23_6056741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_6056741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056741 prefixEnd_6056741 := by exact prefixLift 6056741
  have htrace : WordTrace (prefixWord ++ tailWord_6056741) baseStart_6056741 baseEnd_6056741 := by
    simpa [prefixWord, tailWord_6056741, baseEnd_6056741] using wordTrace_append hprefix tailTrace_6056741
  have hstable : (prefixWord ++ tailWord_6056741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056741).length < 2 ^ (prefixWord ++ tailWord_6056741).sum := by decide
  have hdescent : baseEnd_6056741 < baseStart_6056741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056802 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6056802 : Nat := 118140960795 + 6056802 * 2 ^ 59
def prefixEnd_6056802 : Nat := 4983230072969 + 3 ^ 40 * 6056802 * 2
def baseEnd_6056802 : Nat := 3110050655113316968020281

theorem tailTrace_6056802 : CollatzResearch.WordTrace tailWord_6056802 prefixEnd_6056802 3110050655113316968020281 := by
  unfold tailWord_6056802
  simp only [CollatzResearch.WordTrace]
  refine ⟨55227429350812062068093165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147273144935498832181581773 55227429350812062068093165)
  ·
    refine ⟨20710286006554523275534937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55227429350812062068093165 20710286006554523275534937)
    ·
      refine ⟨15532714504915892456651203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20710286006554523275534937 15532714504915892456651203)
      ·
        refine ⟨23299071757373838684976805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15532714504915892456651203 23299071757373838684976805)
        ·
          refine ⟨4368575954507594753433151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23299071757373838684976805 4368575954507594753433151)
          ·
            refine ⟨6552863931761392130149727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368575954507594753433151 6552863931761392130149727)
            ·
              refine ⟨9829295897642088195224591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6552863931761392130149727 9829295897642088195224591)
              ·
                refine ⟨14743943846463132292836887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9829295897642088195224591 14743943846463132292836887)
                ·
                  refine ⟨22115915769694698439255331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14743943846463132292836887 22115915769694698439255331)
                  ·
                    refine ⟨33173873654542047658882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22115915769694698439255331 33173873654542047658882997)
                    ·
                      refine ⟨3110050655113316968020281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33173873654542047658882997 3110050655113316968020281)
                      ·
                        rfl

theorem cell23_6056802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6056802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056802 prefixEnd_6056802 := by exact prefixLift 6056802
  have htrace : WordTrace (prefixWord ++ tailWord_6056802) baseStart_6056802 baseEnd_6056802 := by
    simpa [prefixWord, tailWord_6056802, baseEnd_6056802] using wordTrace_append hprefix tailTrace_6056802
  have hstable : (prefixWord ++ tailWord_6056802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056802).length < 2 ^ (prefixWord ++ tailWord_6056802).sum := by decide
  have hdescent : baseEnd_6056802 < baseStart_6056802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056855 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_6056855 : Nat := 118140960795 + 6056855 * 2 ^ 59
def prefixEnd_6056855 : Nat := 4983230072969 + 3 ^ 40 * 6056855 * 2
def baseEnd_6056855 : Nat := 3110077869588005260657537

theorem tailTrace_6056855 : CollatzResearch.WordTrace tailWord_6056855 prefixEnd_6056855 3110077869588005260657537 := by
  unfold tailWord_6056855
  simp only [CollatzResearch.WordTrace]
  refine ⟨220911650472056238324052019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147274433648037492216034679 220911650472056238324052019)
  ·
    refine ⟨331367475708084357486078029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220911650472056238324052019 331367475708084357486078029)
    ·
      refine ⟨124262803390531634057279261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331367475708084357486078029 124262803390531634057279261)
      ·
        refine ⟨46598551271449362771479723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124262803390531634057279261 46598551271449362771479723)
        ·
          refine ⟨69897826907174044157219585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46598551271449362771479723 69897826907174044157219585)
          ·
            refine ⟨52423370180380533117914689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69897826907174044157219585 52423370180380533117914689)
            ·
              refine ⟨39317527635285399838436017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52423370180380533117914689 39317527635285399838436017)
              ·
                refine ⟨29488145726464049878827013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39317527635285399838436017 29488145726464049878827013)
                ·
                  refine ⟨5529027323712009352280065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29488145726464049878827013 5529027323712009352280065)
                  ·
                    refine ⟨4146770492784007014210049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529027323712009352280065 4146770492784007014210049)
                    ·
                      refine ⟨3110077869588005260657537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146770492784007014210049 3110077869588005260657537)
                      ·
                        rfl

theorem cell23_6056855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_6056855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056855 prefixEnd_6056855 := by exact prefixLift 6056855
  have htrace : WordTrace (prefixWord ++ tailWord_6056855) baseStart_6056855 baseEnd_6056855 := by
    simpa [prefixWord, tailWord_6056855, baseEnd_6056855] using wordTrace_append hprefix tailTrace_6056855
  have hstable : (prefixWord ++ tailWord_6056855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056855).length < 2 ^ (prefixWord ++ tailWord_6056855).sum := by decide
  have hdescent : baseEnd_6056855 < baseStart_6056855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056861 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 9]
def baseStart_6056861 : Nat := 118140960795 + 6056861 * 2 ^ 59
def prefixEnd_6056861 : Nat := 4983230072969 + 3 ^ 40 * 6056861 * 2
def baseEnd_6056861 : Nat := 345564550052436915242501

theorem tailTrace_6056861 : CollatzResearch.WordTrace tailWord_6056861 prefixEnd_6056861 345564550052436915242501 := by
  unfold tailWord_6056861
  simp only [CollatzResearch.WordTrace]
  refine ⟨220911869310034501348770437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147274579540023000899180291 220911869310034501348770437)
  ·
    refine ⟨41420975495631469002894457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220911869310034501348770437 41420975495631469002894457)
    ·
      refine ⟨31065731621723601752170843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41420975495631469002894457 31065731621723601752170843)
      ·
        refine ⟨46598597432585402628256265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31065731621723601752170843 46598597432585402628256265)
        ·
          refine ⟨34948948074439051971192199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46598597432585402628256265 34948948074439051971192199)
          ·
            refine ⟨52423422111658577956788299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34948948074439051971192199 52423422111658577956788299)
            ·
              refine ⟨78635133167487866935182449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52423422111658577956788299 78635133167487866935182449)
              ·
                refine ⟨58976349875615900201386837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78635133167487866935182449 58976349875615900201386837)
                ·
                  refine ⟨345564550052436915242501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58976349875615900201386837 345564550052436915242501)
                  ·
                    rfl

theorem cell23_6056861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_6056861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056861 prefixEnd_6056861 := by exact prefixLift 6056861
  have htrace : WordTrace (prefixWord ++ tailWord_6056861) baseStart_6056861 baseEnd_6056861 := by
    simpa [prefixWord, tailWord_6056861, baseEnd_6056861] using wordTrace_append hprefix tailTrace_6056861
  have hstable : (prefixWord ++ tailWord_6056861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056861).length < 2 ^ (prefixWord ++ tailWord_6056861).sum := by decide
  have hdescent : baseEnd_6056861 < baseStart_6056861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056888 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_6056888 : Nat := 118140960795 + 6056888 * 2 ^ 59
def prefixEnd_6056888 : Nat := 4983230072969 + 3 ^ 40 * 6056888 * 2
def baseEnd_6056888 : Nat := 3110094814449603631544885

theorem tailTrace_6056888 : CollatzResearch.WordTrace tailWord_6056888 prefixEnd_6056888 3110094814449603631544885 := by
  unfold tailWord_6056888
  simp only [CollatzResearch.WordTrace]
  refine ⟨110456427040468342480001659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147275236053957789973335545 110456427040468342480001659)
  ·
    refine ⟨165684640560702513720002489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110456427040468342480001659 165684640560702513720002489)
    ·
      refine ⟨124263480420526885290001867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165684640560702513720002489 124263480420526885290001867)
      ·
        refine ⟨186395220630790327935002801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124263480420526885290001867 186395220630790327935002801)
        ·
          refine ⟨139796415473092745951252101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186395220630790327935002801 139796415473092745951252101)
          ·
            refine ⟨26211827901204889865859769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139796415473092745951252101 26211827901204889865859769)
            ·
              refine ⟨19658870925903667399394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26211827901204889865859769 19658870925903667399394827)
              ·
                refine ⟨29488306388855501099092241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19658870925903667399394827 29488306388855501099092241)
                ·
                  refine ⟨22116229791641625824319181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29488306388855501099092241 22116229791641625824319181)
                  ·
                    refine ⟨8293586171865609684119693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22116229791641625824319181 8293586171865609684119693)
                    ·
                      refine ⟨3110094814449603631544885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293586171865609684119693 3110094814449603631544885)
                      ·
                        rfl

theorem cell23_6056888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_6056888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056888 prefixEnd_6056888 := by exact prefixLift 6056888
  have htrace : WordTrace (prefixWord ++ tailWord_6056888) baseStart_6056888 baseEnd_6056888 := by
    simpa [prefixWord, tailWord_6056888, baseEnd_6056888] using wordTrace_append hprefix tailTrace_6056888
  have hstable : (prefixWord ++ tailWord_6056888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056888).length < 2 ^ (prefixWord ++ tailWord_6056888).sum := by decide
  have hdescent : baseEnd_6056888 < baseStart_6056888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056889 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6056889 : Nat := 118140960795 + 6056889 * 2 ^ 59
def prefixEnd_6056889 : Nat := 4983230072969 + 3 ^ 40 * 6056889 * 2
def baseEnd_6056889 : Nat := 3110095327930258127632381

theorem tailTrace_6056889 : CollatzResearch.WordTrace tailWord_6056889 prefixEnd_6056889 3110095327930258127632381 := by
  unfold tailWord_6056889
  simp only [CollatzResearch.WordTrace]
  refine ⟨220912890553933062130789721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147275260369288708087193147 220912890553933062130789721)
  ·
    refine ⟨165684667915449796598092291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220912890553933062130789721 165684667915449796598092291)
    ·
      refine ⟨248527001873174694897138437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165684667915449796598092291 248527001873174694897138437)
      ·
        refine ⟨46598812851220255293213457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248527001873174694897138437 46598812851220255293213457)
        ·
          refine ⟨34949109638415191469910093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46598812851220255293213457 34949109638415191469910093)
          ·
            refine ⟨13105916114405696801216285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34949109638415191469910093 13105916114405696801216285)
            ·
              refine ⟨4914718542902136300456107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13105916114405696801216285 4914718542902136300456107)
              ·
                refine ⟨7372077814353204450684161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914718542902136300456107 7372077814353204450684161)
                ·
                  refine ⟨5529058360764903338013121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372077814353204450684161 5529058360764903338013121)
                  ·
                    refine ⟨4146793770573677503509841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529058360764903338013121 4146793770573677503509841)
                    ·
                      refine ⟨3110095327930258127632381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146793770573677503509841 3110095327930258127632381)
                      ·
                        rfl

theorem cell23_6056889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6056889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056889 prefixEnd_6056889 := by exact prefixLift 6056889
  have htrace : WordTrace (prefixWord ++ tailWord_6056889) baseStart_6056889 baseEnd_6056889 := by
    simpa [prefixWord, tailWord_6056889, baseEnd_6056889] using wordTrace_append hprefix tailTrace_6056889
  have hstable : (prefixWord ++ tailWord_6056889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056889).length < 2 ^ (prefixWord ++ tailWord_6056889).sum := by decide
  have hdescent : baseEnd_6056889 < baseStart_6056889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056908 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_6056908 : Nat := 118140960795 + 6056908 * 2 ^ 59
def prefixEnd_6056908 : Nat := 4983230072969 + 3 ^ 40 * 6056908 * 2
def baseEnd_6056908 : Nat := 1036701694687564517764931

theorem tailTrace_6056908 : CollatzResearch.WordTrace tailWord_6056908 prefixEnd_6056908 1036701694687564517764931 := by
  unfold tailWord_6056908
  simp only [CollatzResearch.WordTrace]
  refine ⟨110456791770432114187865689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147275722360576152250487585 110456791770432114187865689)
  ·
    refine ⟨82842593827824085640899267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110456791770432114187865689 82842593827824085640899267)
    ·
      refine ⟨124263890741736128461348901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82842593827824085640899267 124263890741736128461348901)
      ·
        refine ⟨23299479514075524086502919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124263890741736128461348901 23299479514075524086502919)
        ·
          refine ⟨34949219271113286129754379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23299479514075524086502919 34949219271113286129754379)
          ·
            refine ⟨52423828906669929194631569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34949219271113286129754379 52423828906669929194631569)
            ·
              refine ⟨39317871680002446895973677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52423828906669929194631569 39317871680002446895973677)
              ·
                refine ⟨14744201880000917585990129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39317871680002446895973677 14744201880000917585990129)
                ·
                  refine ⟨11058151410000688189492597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14744201880000917585990129 11058151410000688189492597)
                  ·
                    refine ⟨1036701694687564517764931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11058151410000688189492597 1036701694687564517764931)
                    ·
                      rfl

theorem cell23_6056908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_6056908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056908 prefixEnd_6056908 := by exact prefixLift 6056908
  have htrace : WordTrace (prefixWord ++ tailWord_6056908) baseStart_6056908 baseEnd_6056908 := by
    simpa [prefixWord, tailWord_6056908, baseEnd_6056908] using wordTrace_append hprefix tailTrace_6056908
  have hstable : (prefixWord ++ tailWord_6056908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056908).length < 2 ^ (prefixWord ++ tailWord_6056908).sum := by decide
  have hdescent : baseEnd_6056908 < baseStart_6056908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056909 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6056909 : Nat := 118140960795 + 6056909 * 2 ^ 59
def prefixEnd_6056909 : Nat := 4983230072969 + 3 ^ 40 * 6056909 * 2
def baseEnd_6056909 : Nat := 3110105597543348049382289

theorem tailTrace_6056909 : CollatzResearch.WordTrace tailWord_6056909 prefixEnd_6056909 3110105597543348049382289 := by
  unfold tailWord_6056909
  simp only [CollatzResearch.WordTrace]
  refine ⟨220913620013860605546517781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147275746675907070364345187 220913620013860605546517781)
  ·
    refine ⟨10355325938149715884993021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220913620013860605546517781 10355325938149715884993021)
    ·
      refine ⟨3883247226806143456872383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10355325938149715884993021 3883247226806143456872383)
      ·
        refine ⟨5824870840209215185308575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883247226806143456872383 5824870840209215185308575)
        ·
          refine ⟨8737306260313822777962863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824870840209215185308575 8737306260313822777962863)
          ·
            refine ⟨13105959390470734166944295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737306260313822777962863 13105959390470734166944295)
            ·
              refine ⟨19658939085706101250416443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105959390470734166944295 19658939085706101250416443)
              ·
                refine ⟨29488408628559151875624665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19658939085706101250416443 29488408628559151875624665)
                ·
                  refine ⟨22116306471419363906718499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29488408628559151875624665 22116306471419363906718499)
                  ·
                    refine ⟨33174459707129045860077749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22116306471419363906718499 33174459707129045860077749)
                    ·
                      refine ⟨3110105597543348049382289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33174459707129045860077749 3110105597543348049382289)
                      ·
                        rfl

theorem cell23_6056909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6056909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056909 prefixEnd_6056909 := by exact prefixLift 6056909
  have htrace : WordTrace (prefixWord ++ tailWord_6056909) baseStart_6056909 baseEnd_6056909 := by
    simpa [prefixWord, tailWord_6056909, baseEnd_6056909] using wordTrace_append hprefix tailTrace_6056909
  have hstable : (prefixWord ++ tailWord_6056909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056909).length < 2 ^ (prefixWord ++ tailWord_6056909).sum := by decide
  have hdescent : baseEnd_6056909 < baseStart_6056909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056925 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6056925 : Nat := 118140960795 + 6056925 * 2 ^ 59
def prefixEnd_6056925 : Nat := 4983230072969 + 3 ^ 40 * 6056925 * 2
def baseEnd_6056925 : Nat := 1036704604411273328927405

theorem tailTrace_6056925 : CollatzResearch.WordTrace tailWord_6056925 prefixEnd_6056925 1036704604411273328927405 := by
  unfold tailWord_6056925
  simp only [CollatzResearch.WordTrace]
  refine ⟨220914203581802640279100229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147276135721201760186066819 220914203581802640279100229)
  ·
    refine ⟨41421413171587995052331293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220914203581802640279100229 41421413171587995052331293)
    ·
      refine ⟨15533029939345498144624235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41421413171587995052331293 15533029939345498144624235)
      ·
        refine ⟨23299544909018247216936353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15533029939345498144624235 23299544909018247216936353)
        ·
          refine ⟨17474658681763685412702265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23299544909018247216936353 17474658681763685412702265)
          ·
            refine ⟨13105994011322764059526699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17474658681763685412702265 13105994011322764059526699)
            ·
              refine ⟨19658991016984146089290049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105994011322764059526699 19658991016984146089290049)
              ·
                refine ⟨14744243262738109566967537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19658991016984146089290049 14744243262738109566967537)
                ·
                  refine ⟨11058182447053582175225653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14744243262738109566967537 11058182447053582175225653)
                  ·
                    refine ⟨1036704604411273328927405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11058182447053582175225653 1036704604411273328927405)
                    ·
                      rfl

theorem cell23_6056925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6056925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056925 prefixEnd_6056925 := by exact prefixLift 6056925
  have htrace : WordTrace (prefixWord ++ tailWord_6056925) baseStart_6056925 baseEnd_6056925 := by
    simpa [prefixWord, tailWord_6056925, baseEnd_6056925] using wordTrace_append hprefix tailTrace_6056925
  have hstable : (prefixWord ++ tailWord_6056925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056925).length < 2 ^ (prefixWord ++ tailWord_6056925).sum := by decide
  have hdescent : baseEnd_6056925 < baseStart_6056925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056965 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_6056965 : Nat := 118140960795 + 6056965 * 2 ^ 59
def prefixEnd_6056965 : Nat := 4983230072969 + 3 ^ 40 * 6056965 * 2
def baseEnd_6056965 : Nat := 3110134352459999830282031

theorem tailTrace_6056965 : CollatzResearch.WordTrace tailWord_6056965 prefixEnd_6056965 3110134352459999830282031 := by
  unfold tailWord_6056965
  simp only [CollatzResearch.WordTrace]
  refine ⟨220915662501657727110556349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147277108334438484740370899 220915662501657727110556349)
  ·
    refine ⟨82843373438121647666458631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220915662501657727110556349 82843373438121647666458631)
    ·
      refine ⟨124265060157182471499687947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82843373438121647666458631 124265060157182471499687947)
      ·
        refine ⟨186397590235773707249531921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124265060157182471499687947 186397590235773707249531921)
        ·
          refine ⟨139798192676830280437148941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186397590235773707249531921 139798192676830280437148941)
          ·
            refine ⟨52424322253811355163930853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139798192676830280437148941 52424322253811355163930853)
            ·
              refine ⟨9829560422589629093237035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52424322253811355163930853 9829560422589629093237035)
              ·
                refine ⟨14744340633884443639855553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9829560422589629093237035 14744340633884443639855553)
                ·
                  refine ⟨11058255475413332729891665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14744340633884443639855553 11058255475413332729891665)
                  ·
                    refine ⟨8293691606559999547418749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11058255475413332729891665 8293691606559999547418749)
                    ·
                      refine ⟨3110134352459999830282031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293691606559999547418749 3110134352459999830282031)
                      ·
                        rfl

theorem cell23_6056965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_6056965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056965 prefixEnd_6056965 := by exact prefixLift 6056965
  have htrace : WordTrace (prefixWord ++ tailWord_6056965) baseStart_6056965 baseEnd_6056965 := by
    simpa [prefixWord, tailWord_6056965, baseEnd_6056965] using wordTrace_append hprefix tailTrace_6056965
  have hstable : (prefixWord ++ tailWord_6056965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056965).length < 2 ^ (prefixWord ++ tailWord_6056965).sum := by decide
  have hdescent : baseEnd_6056965 < baseStart_6056965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6056989 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_6056989 : Nat := 118140960795 + 6056989 * 2 ^ 59
def prefixEnd_6056989 : Nat := 4983230072969 + 3 ^ 40 * 6056989 * 2
def baseEnd_6056989 : Nat := 1036715558665235912127307

theorem tailTrace_6056989 : CollatzResearch.WordTrace tailWord_6056989 prefixEnd_6056989 1036715558665235912127307 := by
  unfold tailWord_6056989
  simp only [CollatzResearch.WordTrace]
  refine ⟨220916537853570779209430021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147277691902380519472953347 220916537853570779209430021)
  ·
    refine ⟨41421850847544521101768129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220916537853570779209430021 41421850847544521101768129)
    ·
      refine ⟨31066388135658390826326097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41421850847544521101768129 31066388135658390826326097)
      ·
        refine ⟨23299791101743793119744573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31066388135658390826326097 23299791101743793119744573)
        ·
          refine ⟨8737421663153922419904215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23299791101743793119744573 8737421663153922419904215)
          ·
            refine ⟨13106132494730883629856323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737421663153922419904215 13106132494730883629856323)
            ·
              refine ⟨19659198742096325444784485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106132494730883629856323 19659198742096325444784485)
              ·
                refine ⟨3686099764143061020897091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19659198742096325444784485 3686099764143061020897091)
                ·
                  refine ⟨5529149646214591531345637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686099764143061020897091 5529149646214591531345637)
                  ·
                    refine ⟨1036715558665235912127307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529149646214591531345637 1036715558665235912127307)
                    ·
                      rfl

theorem cell23_6056989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_6056989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6056989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6056989 prefixEnd_6056989 := by exact prefixLift 6056989
  have htrace : WordTrace (prefixWord ++ tailWord_6056989) baseStart_6056989 baseEnd_6056989 := by
    simpa [prefixWord, tailWord_6056989, baseEnd_6056989] using wordTrace_append hprefix tailTrace_6056989
  have hstable : (prefixWord ++ tailWord_6056989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6056989).length < 2 ^ (prefixWord ++ tailWord_6056989).sum := by decide
  have hdescent : baseEnd_6056989 < baseStart_6056989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6056989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057045 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_6057045 : Nat := 118140960795 + 6057045 * 2 ^ 59
def prefixEnd_6057045 : Nat := 4983230072969 + 3 ^ 40 * 6057045 * 2
def baseEnd_6057045 : Nat := 1036725143637453172427221

theorem tailTrace_6057045 : CollatzResearch.WordTrace tailWord_6057045 prefixEnd_6057045 1036725143637453172427221 := by
  unfold tailWord_6057045
  simp only [CollatzResearch.WordTrace]
  refine ⟨220918580341367900773468589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147279053560911933848979059 220918580341367900773468589)
  ·
    refine ⟨82844467628012962790050721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220918580341367900773468589 82844467628012962790050721)
    ·
      refine ⟨62133350721009722092538041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82844467628012962790050721 62133350721009722092538041)
      ·
        refine ⟨46600013040757291569403531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62133350721009722092538041 46600013040757291569403531)
        ·
          refine ⟨69900019561135937354105297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46600013040757291569403531 69900019561135937354105297)
          ·
            refine ⟨52425014670851953015578973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69900019561135937354105297 52425014670851953015578973)
            ·
              refine ⟨19659380501569482380842115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52425014670851953015578973 19659380501569482380842115)
              ·
                refine ⟨29489070752354223571263173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19659380501569482380842115 29489070752354223571263173)
                ·
                  refine ⟨5529200766066416919611845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29489070752354223571263173 5529200766066416919611845)
                  ·
                    refine ⟨1036725143637453172427221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529200766066416919611845 1036725143637453172427221)
                    ·
                      rfl

theorem cell23_6057045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_6057045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057045 prefixEnd_6057045 := by exact prefixLift 6057045
  have htrace : WordTrace (prefixWord ++ tailWord_6057045) baseStart_6057045 baseEnd_6057045 := by
    simpa [prefixWord, tailWord_6057045, baseEnd_6057045] using wordTrace_append hprefix tailTrace_6057045
  have hstable : (prefixWord ++ tailWord_6057045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057045).length < 2 ^ (prefixWord ++ tailWord_6057045).sum := by decide
  have hdescent : baseEnd_6057045 < baseStart_6057045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057048 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6057048 : Nat := 118140960795 + 6057048 * 2 ^ 59
def prefixEnd_6057048 : Nat := 4983230072969 + 3 ^ 40 * 6057048 * 2
def baseEnd_6057048 : Nat := 3110176971354323005544149

theorem tailTrace_6057048 : CollatzResearch.WordTrace tailWord_6057048 prefixEnd_6057048 3110176971354323005544149 := by
  unfold tailWord_6057048
  simp only [CollatzResearch.WordTrace]
  refine ⟨110459344880178516142913899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147279126506904688190551865 110459344880178516142913899)
  ·
    refine ⟨165689017320267774214370849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110459344880178516142913899 165689017320267774214370849)
    ·
      refine ⟨124266762990200830660778137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165689017320267774214370849 124266762990200830660778137)
      ·
        refine ⟨93200072242650622995583603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124266762990200830660778137 93200072242650622995583603)
        ·
          refine ⟨139800108363975934493375405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93200072242650622995583603 139800108363975934493375405)
          ·
            refine ⟨52425040636490975435015777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139800108363975934493375405 52425040636490975435015777)
            ·
              refine ⟨39318780477368231576261833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52425040636490975435015777 39318780477368231576261833)
              ·
                refine ⟨29489085358026173682196375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39318780477368231576261833 29489085358026173682196375)
                ·
                  refine ⟨44233628037039260523294563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29489085358026173682196375 44233628037039260523294563)
                  ·
                    refine ⟨66350442055558890784941845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44233628037039260523294563 66350442055558890784941845)
                    ·
                      refine ⟨3110176971354323005544149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66350442055558890784941845 3110176971354323005544149)
                      ·
                        rfl

theorem cell23_6057048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6057048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057048 prefixEnd_6057048 := by exact prefixLift 6057048
  have htrace : WordTrace (prefixWord ++ tailWord_6057048) baseStart_6057048 baseEnd_6057048 := by
    simpa [prefixWord, tailWord_6057048, baseEnd_6057048] using wordTrace_append hprefix tailTrace_6057048
  have hstable : (prefixWord ++ tailWord_6057048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057048).length < 2 ^ (prefixWord ++ tailWord_6057048).sum := by decide
  have hdescent : baseEnd_6057048 < baseStart_6057048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057065 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_6057065 : Nat := 118140960795 + 6057065 * 2 ^ 59
def prefixEnd_6057065 : Nat := 4983230072969 + 3 ^ 40 * 6057065 * 2
def baseEnd_6057065 : Nat := 3110185700525449439031571

theorem tailTrace_6057065 : CollatzResearch.WordTrace tailWord_6057065 prefixEnd_6057065 3110185700525449439031571 := by
  unfold tailWord_6057065
  simp only [CollatzResearch.WordTrace]
  refine ⟨220919309801295444189196649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147279539867530296126131099 220919309801295444189196649)
  ·
    refine ⟨165689482350971583141897487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220919309801295444189196649 165689482350971583141897487)
    ·
      refine ⟨248534223526457374712846231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165689482350971583141897487 248534223526457374712846231)
      ·
        refine ⟨372801335289686062069269347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248534223526457374712846231 372801335289686062069269347)
        ·
          refine ⟨559202002934529093103904021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372801335289686062069269347 559202002934529093103904021)
          ·
            refine ⟨26212593887556051239245501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 559202002934529093103904021 26212593887556051239245501)
            ·
              refine ⟨9829722707833519214717063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26212593887556051239245501 9829722707833519214717063)
              ·
                refine ⟨14744584061750278822075595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9829722707833519214717063 14744584061750278822075595)
                ·
                  refine ⟨22116876092625418233113393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14744584061750278822075595 22116876092625418233113393)
                  ·
                    refine ⟨16587657069469063674835045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22116876092625418233113393 16587657069469063674835045)
                    ·
                      refine ⟨3110185700525449439031571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16587657069469063674835045 3110185700525449439031571)
                      ·
                        rfl

theorem cell23_6057065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_6057065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057065 prefixEnd_6057065 := by exact prefixLift 6057065
  have htrace : WordTrace (prefixWord ++ tailWord_6057065) baseStart_6057065 baseEnd_6057065 := by
    simpa [prefixWord, tailWord_6057065, baseEnd_6057065] using wordTrace_append hprefix tailTrace_6057065
  have hstable : (prefixWord ++ tailWord_6057065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057065).length < 2 ^ (prefixWord ++ tailWord_6057065).sum := by decide
  have hdescent : baseEnd_6057065 < baseStart_6057065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057069 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6057069 : Nat := 118140960795 + 6057069 * 2 ^ 59
def prefixEnd_6057069 : Nat := 4983230072969 + 3 ^ 40 * 6057069 * 2
def baseEnd_6057069 : Nat := 3110187754448067423381553

theorem tailTrace_6057069 : CollatzResearch.WordTrace tailWord_6057069 prefixEnd_6057069 3110187754448067423381553 := by
  unfold tailWord_6057069
  simp only [CollatzResearch.WordTrace]
  refine ⟨220919455693280952872342261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147279637128853968581561507 220919455693280952872342261)
  ·
    refine ⟨20711198971245089331782087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220919455693280952872342261 20711198971245089331782087)
    ·
      refine ⟨31066798456867633997673131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20711198971245089331782087 31066798456867633997673131)
      ·
        refine ⟨46600197685301450996509697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31066798456867633997673131 46600197685301450996509697)
        ·
          refine ⟨34950148263976088247382273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46600197685301450996509697 34950148263976088247382273)
          ·
            refine ⟨26212611197982066185536705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34950148263976088247382273 26212611197982066185536705)
            ·
              refine ⟨19659458398486549639152529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26212611197982066185536705 19659458398486549639152529)
              ·
                refine ⟨14744593798864912229364397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19659458398486549639152529 14744593798864912229364397)
                ·
                  refine ⟨5529222674574342086011649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14744593798864912229364397 5529222674574342086011649)
                  ·
                    refine ⟨4146917005930756564508737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529222674574342086011649 4146917005930756564508737)
                    ·
                      refine ⟨3110187754448067423381553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146917005930756564508737 3110187754448067423381553)
                      ·
                        rfl

theorem cell23_6057069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6057069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057069 prefixEnd_6057069 := by exact prefixLift 6057069
  have htrace : WordTrace (prefixWord ++ tailWord_6057069) baseStart_6057069 baseEnd_6057069 := by
    simpa [prefixWord, tailWord_6057069, baseEnd_6057069] using wordTrace_append hprefix tailTrace_6057069
  have hstable : (prefixWord ++ tailWord_6057069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057069).length < 2 ^ (prefixWord ++ tailWord_6057069).sum := by decide
  have hdescent : baseEnd_6057069 < baseStart_6057069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057072 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_6057072 : Nat := 118140960795 + 6057072 * 2 ^ 59
def prefixEnd_6057072 : Nat := 4983230072969 + 3 ^ 40 * 6057072 * 2
def baseEnd_6057072 : Nat := 3110189294890030911644039

theorem tailTrace_6057072 : CollatzResearch.WordTrace tailWord_6057072 prefixEnd_6057072 3110189294890030911644039 := by
  unfold tailWord_6057072
  simp only [CollatzResearch.WordTrace]
  refine ⟨110459782556135042192350735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147279710074846722923134313 110459782556135042192350735)
  ·
    refine ⟨165689673834202563288526103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110459782556135042192350735 165689673834202563288526103)
    ·
      refine ⟨248534510751303844932789155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165689673834202563288526103 248534510751303844932789155)
      ·
        refine ⟨372801766126955767399183733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248534510751303844932789155 372801766126955767399183733)
        ·
          refine ⟨34950165574402103193673475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372801766126955767399183733 34950165574402103193673475)
          ·
            refine ⟨52425248361603154790510213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34950165574402103193673475 52425248361603154790510213)
            ·
              refine ⟨9829734067800591523220665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52425248361603154790510213 9829734067800591523220665)
              ·
                refine ⟨7372300550850443642415499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9829734067800591523220665 7372300550850443642415499)
                ·
                  refine ⟨11058450826275665463623249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7372300550850443642415499 11058450826275665463623249)
                  ·
                    refine ⟨8293838119706749097717437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11058450826275665463623249 8293838119706749097717437)
                    ·
                      refine ⟨3110189294890030911644039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293838119706749097717437 3110189294890030911644039)
                      ·
                        rfl

theorem cell23_6057072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_6057072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057072 prefixEnd_6057072 := by exact prefixLift 6057072
  have htrace : WordTrace (prefixWord ++ tailWord_6057072) baseStart_6057072 baseEnd_6057072 := by
    simpa [prefixWord, tailWord_6057072, baseEnd_6057072] using wordTrace_append hprefix tailTrace_6057072
  have hstable : (prefixWord ++ tailWord_6057072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057072).length < 2 ^ (prefixWord ++ tailWord_6057072).sum := by decide
  have hdescent : baseEnd_6057072 < baseStart_6057072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057085 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_6057085 : Nat := 118140960795 + 6057085 * 2 ^ 59
def prefixEnd_6057085 : Nat := 4983230072969 + 3 ^ 40 * 6057085 * 2
def baseEnd_6057085 : Nat := 3110195970138539360781479

theorem tailTrace_6057085 : CollatzResearch.WordTrace tailWord_6057085 prefixEnd_6057085 3110195970138539360781479 := by
  unfold tailWord_6057085
  simp only [CollatzResearch.WordTrace]
  refine ⟨220920039261222987604924709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147280026174148658403283139 220920039261222987604924709)
  ·
    refine ⟨41422507361479310175923383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220920039261222987604924709 41422507361479310175923383)
    ·
      refine ⟨62133761042218965263885075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41422507361479310175923383 62133761042218965263885075)
      ·
        refine ⟨93200641563328447895827613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62133761042218965263885075 93200641563328447895827613)
        ·
          refine ⟨34950240586248167960935355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93200641563328447895827613 34950240586248167960935355)
          ·
            refine ⟨52425360879372251941403033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34950240586248167960935355 52425360879372251941403033)
            ·
              refine ⟨39319020659529188956052275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52425360879372251941403033 39319020659529188956052275)
              ·
                refine ⟨58978530989293783434078413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39319020659529188956052275 58978530989293783434078413)
                ·
                  refine ⟨22116949120985168787779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58978530989293783434078413 22116949120985168787779405)
                  ·
                    refine ⟨8293855920369438295417277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22116949120985168787779405 8293855920369438295417277)
                    ·
                      refine ⟨3110195970138539360781479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293855920369438295417277 3110195970138539360781479)
                      ·
                        rfl

theorem cell23_6057085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_6057085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057085 prefixEnd_6057085 := by exact prefixLift 6057085
  have htrace : WordTrace (prefixWord ++ tailWord_6057085) baseStart_6057085 baseEnd_6057085 := by
    simpa [prefixWord, tailWord_6057085, baseEnd_6057085] using wordTrace_append hprefix tailTrace_6057085
  have hstable : (prefixWord ++ tailWord_6057085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057085).length < 2 ^ (prefixWord ++ tailWord_6057085).sum := by decide
  have hdescent : baseEnd_6057085 < baseStart_6057085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057145 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6057145 : Nat := 118140960795 + 6057145 * 2 ^ 59
def prefixEnd_6057145 : Nat := 4983230072969 + 3 ^ 40 * 6057145 * 2
def baseEnd_6057145 : Nat := 3110226778977809126031203

theorem tailTrace_6057145 : CollatzResearch.WordTrace tailWord_6057145 prefixEnd_6057145 3110226778977809126031203 := by
  unfold tailWord_6057145
  simp only [CollatzResearch.WordTrace]
  refine ⟨220922227641005617852108889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147281485094003745234739259 220922227641005617852108889)
  ·
    refine ⟨165691670730754213389081667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220922227641005617852108889 165691670730754213389081667)
    ·
      refine ⟨248537506096131320083622501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165691670730754213389081667 248537506096131320083622501)
      ·
        refine ⟨46600782393024622515679219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248537506096131320083622501 46600782393024622515679219)
        ·
          refine ⟨69901173589536933773518829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46600782393024622515679219 69901173589536933773518829)
          ·
            refine ⟨26212940096076350165069561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69901173589536933773518829 26212940096076350165069561)
            ·
              refine ⟨19659705072057262623802171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26212940096076350165069561 19659705072057262623802171)
              ·
                refine ⟨29489557608085893935703257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19659705072057262623802171 29489557608085893935703257)
                ·
                  refine ⟨22117168206064420451777443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29489557608085893935703257 22117168206064420451777443)
                  ·
                    refine ⟨33175752309096630677666165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22117168206064420451777443 33175752309096630677666165)
                    ·
                      refine ⟨3110226778977809126031203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33175752309096630677666165 3110226778977809126031203)
                      ·
                        rfl

theorem cell23_6057145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6057145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057145 prefixEnd_6057145 := by exact prefixLift 6057145
  have htrace : WordTrace (prefixWord ++ tailWord_6057145) baseStart_6057145 baseEnd_6057145 := by
    simpa [prefixWord, tailWord_6057145, baseEnd_6057145] using wordTrace_append hprefix tailTrace_6057145
  have hstable : (prefixWord ++ tailWord_6057145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057145).length < 2 ^ (prefixWord ++ tailWord_6057145).sum := by decide
  have hdescent : baseEnd_6057145 < baseStart_6057145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057154 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6057154 : Nat := 118140960795 + 6057154 * 2 ^ 59
def prefixEnd_6057154 : Nat := 4983230072969 + 3 ^ 40 * 6057154 * 2
def baseEnd_6057154 : Nat := 3110231400303699590818663

theorem tailTrace_6057154 : CollatzResearch.WordTrace tailWord_6057154 prefixEnd_6057154 3110231400303699590818663 := by
  unfold tailWord_6057154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55230638974493253097296629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147281703931982008259457677 55230638974493253097296629)
  ·
    refine ⟨5177872403858742477871559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55230638974493253097296629 5177872403858742477871559)
    ·
      refine ⟨7766808605788113716807339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177872403858742477871559 7766808605788113716807339)
      ·
        refine ⟨11650212908682170575211009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766808605788113716807339 11650212908682170575211009)
        ·
          refine ⟨8737659681511627931408257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11650212908682170575211009 8737659681511627931408257)
          ·
            refine ⟨6553244761133720948556193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737659681511627931408257 6553244761133720948556193)
            ·
              refine ⟨4914933570850290711417145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553244761133720948556193 4914933570850290711417145)
              ·
                refine ⟨3686200178137718033562859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914933570850290711417145 3686200178137718033562859)
                ·
                  refine ⟨5529300267206577050344289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686200178137718033562859 5529300267206577050344289)
                  ·
                    refine ⟨4146975200404932787758217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529300267206577050344289 4146975200404932787758217)
                    ·
                      refine ⟨3110231400303699590818663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4146975200404932787758217 3110231400303699590818663)
                      ·
                        rfl

theorem cell23_6057154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6057154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057154 prefixEnd_6057154 := by exact prefixLift 6057154
  have htrace : WordTrace (prefixWord ++ tailWord_6057154) baseStart_6057154 baseEnd_6057154 := by
    simpa [prefixWord, tailWord_6057154, baseEnd_6057154] using wordTrace_append hprefix tailTrace_6057154
  have hstable : (prefixWord ++ tailWord_6057154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057154).length < 2 ^ (prefixWord ++ tailWord_6057154).sum := by decide
  have hdescent : baseEnd_6057154 < baseStart_6057154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057175 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_6057175 : Nat := 118140960795 + 6057175 * 2 ^ 59
def prefixEnd_6057175 : Nat := 4983230072969 + 3 ^ 40 * 6057175 * 2
def baseEnd_6057175 : Nat := 3110242183397444008656065

theorem tailTrace_6057175 : CollatzResearch.WordTrace tailWord_6057175 prefixEnd_6057175 3110242183397444008656065 := by
  unfold tailWord_6057175
  simp only [CollatzResearch.WordTrace]
  refine ⟨220923321830896932975700979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147282214553931288650467319 220923321830896932975700979)
  ·
    refine ⟨331384982746345399463551469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220923321830896932975700979 331384982746345399463551469)
    ·
      refine ⟨124269368529879524798831801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331384982746345399463551469 124269368529879524798831801)
      ·
        refine ⟨93202026397409643599123851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124269368529879524798831801 93202026397409643599123851)
        ·
          refine ⟨139803039596114465398685777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93202026397409643599123851 139803039596114465398685777)
          ·
            refine ⟨104852279697085849049014333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139803039596114465398685777 104852279697085849049014333)
            ·
              refine ⟨39319604886407193393380375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104852279697085849049014333 39319604886407193393380375)
              ·
                refine ⟨58979407329610790090070563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39319604886407193393380375 58979407329610790090070563)
                ·
                  refine ⟨88469110994416185135105845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58979407329610790090070563 88469110994416185135105845)
                  ·
                    refine ⟨8293979155726517356416173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88469110994416185135105845 8293979155726517356416173)
                    ·
                      refine ⟨3110242183397444008656065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8293979155726517356416173 3110242183397444008656065)
                      ·
                        rfl

theorem cell23_6057175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_6057175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057175 prefixEnd_6057175 := by exact prefixLift 6057175
  have htrace : WordTrace (prefixWord ++ tailWord_6057175) baseStart_6057175 baseEnd_6057175 := by
    simpa [prefixWord, tailWord_6057175, baseEnd_6057175] using wordTrace_append hprefix tailTrace_6057175
  have hstable : (prefixWord ++ tailWord_6057175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057175).length < 2 ^ (prefixWord ++ tailWord_6057175).sum := by decide
  have hdescent : baseEnd_6057175 < baseStart_6057175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057195 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 7]
def baseStart_6057195 : Nat := 118140960795 + 6057195 * 2 ^ 59
def prefixEnd_6057195 : Nat := 4983230072969 + 3 ^ 40 * 6057195 * 2
def baseEnd_6057195 : Nat := 1036750817670177976801991

theorem tailTrace_6057195 : CollatzResearch.WordTrace tailWord_6057195 prefixEnd_6057195 1036750817670177976801991 := by
  unfold tailWord_6057195
  simp only [CollatzResearch.WordTrace]
  refine ⟨220924051290824476391429039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147282700860549650927619359 220924051290824476391429039)
  ·
    refine ⟨331386076936236714587143559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220924051290824476391429039 331386076936236714587143559)
    ·
      refine ⟨497079115404355071880715339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331386076936236714587143559 497079115404355071880715339)
      ·
        refine ⟨745618673106532607821073009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497079115404355071880715339 745618673106532607821073009)
        ·
          refine ⟨559214004829899455865804757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745618673106532607821073009 559214004829899455865804757)
          ·
            refine ⟨13106578238200768496854799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 559214004829899455865804757 13106578238200768496854799)
            ·
              refine ⟨19659867357301152745282199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106578238200768496854799 19659867357301152745282199)
              ·
                refine ⟨29489801035951729117923299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19659867357301152745282199 29489801035951729117923299)
                ·
                  refine ⟨44234701553927593676884949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29489801035951729117923299 44234701553927593676884949)
                  ·
                    refine ⟨1036750817670177976801991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44234701553927593676884949 1036750817670177976801991)
                    ·
                      rfl

theorem cell23_6057195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_6057195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057195 prefixEnd_6057195 := by exact prefixLift 6057195
  have htrace : WordTrace (prefixWord ++ tailWord_6057195) baseStart_6057195 baseEnd_6057195 := by
    simpa [prefixWord, tailWord_6057195, baseEnd_6057195] using wordTrace_append hprefix tailTrace_6057195
  have hstable : (prefixWord ++ tailWord_6057195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057195).length < 2 ^ (prefixWord ++ tailWord_6057195).sum := by decide
  have hdescent : baseEnd_6057195 < baseStart_6057195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057199 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 5]
def baseStart_6057199 : Nat := 118140960795 + 6057199 * 2 ^ 59
def prefixEnd_6057199 : Nat := 4983230072969 + 3 ^ 40 * 6057199 * 2
def baseEnd_6057199 : Nat := 345583834103683546083995

theorem tailTrace_6057199 : CollatzResearch.WordTrace tailWord_6057199 prefixEnd_6057199 345583834103683546083995 := by
  unfold tailWord_6057199
  simp only [CollatzResearch.WordTrace]
  refine ⟨220924197182809985074574651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147282798121873323383049767 220924197182809985074574651)
  ·
    refine ⟨331386295774214977611861977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220924197182809985074574651 331386295774214977611861977)
    ·
      refine ⟨248539721830661233208896483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331386295774214977611861977 248539721830661233208896483)
      ·
        refine ⟨372809582745991849813344725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248539721830661233208896483 372809582745991849813344725)
        ·
          refine ⟨8737724595609183980000267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 372809582745991849813344725 8737724595609183980000267)
          ·
            refine ⟨13106586893413775970000401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737724595609183980000267 13106586893413775970000401)
            ·
              refine ⟨9829940170060331977500301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13106586893413775970000401 9829940170060331977500301)
              ·
                refine ⟨3686227563772624491562613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9829940170060331977500301 3686227563772624491562613)
                ·
                  refine ⟨345583834103683546083995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3686227563772624491562613 345583834103683546083995)
                  ·
                    rfl

theorem cell23_6057199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 5].length) (baseStart_6057199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057199 prefixEnd_6057199 := by exact prefixLift 6057199
  have htrace : WordTrace (prefixWord ++ tailWord_6057199) baseStart_6057199 baseEnd_6057199 := by
    simpa [prefixWord, tailWord_6057199, baseEnd_6057199] using wordTrace_append hprefix tailTrace_6057199
  have hstable : (prefixWord ++ tailWord_6057199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057199).length < 2 ^ (prefixWord ++ tailWord_6057199).sum := by decide
  have hdescent : baseEnd_6057199 < baseStart_6057199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057252 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_6057252 : Nat := 118140960795 + 6057252 * 2 ^ 59
def prefixEnd_6057252 : Nat := 4983230072969 + 3 ^ 40 * 6057252 * 2
def baseEnd_6057252 : Nat := 3110281721407840207393211

theorem tailTrace_6057252 : CollatzResearch.WordTrace tailWord_6057252 prefixEnd_6057252 3110281721407840207393211 := by
  unfold tailWord_6057252
  simp only [CollatzResearch.WordTrace]
  refine ⟨110463065125808987563127005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147284086834411983417502673 110463065125808987563127005)
  ·
    refine ⟨41423649422178370336172627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110463065125808987563127005 41423649422178370336172627)
    ·
      refine ⟨62135474133267555504258941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41423649422178370336172627 62135474133267555504258941)
      ·
        refine ⟨23300802799975333314097103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62135474133267555504258941 23300802799975333314097103)
        ·
          refine ⟨34951204199962999971145655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23300802799975333314097103 34951204199962999971145655)
          ·
            refine ⟨52426806299944499956718483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34951204199962999971145655 52426806299944499956718483)
            ·
              refine ⟨78640209449916749935077725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52426806299944499956718483 78640209449916749935077725)
              ·
                refine ⟨29490078543718781225654147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78640209449916749935077725 29490078543718781225654147)
                ·
                  refine ⟨44235117815578171838481221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29490078543718781225654147 44235117815578171838481221)
                  ·
                    refine ⟨8294084590420907219715229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44235117815578171838481221 8294084590420907219715229)
                    ·
                      refine ⟨3110281721407840207393211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8294084590420907219715229 3110281721407840207393211)
                      ·
                        rfl

theorem cell23_6057252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_6057252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057252 prefixEnd_6057252 := by exact prefixLift 6057252
  have htrace : WordTrace (prefixWord ++ tailWord_6057252) baseStart_6057252 baseEnd_6057252 := by
    simpa [prefixWord, tailWord_6057252, baseEnd_6057252] using wordTrace_append hprefix tailTrace_6057252
  have hstable : (prefixWord ++ tailWord_6057252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057252).length < 2 ^ (prefixWord ++ tailWord_6057252).sum := by decide
  have hdescent : baseEnd_6057252 < baseStart_6057252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057269 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_6057269 : Nat := 118140960795 + 6057269 * 2 ^ 59
def prefixEnd_6057269 : Nat := 4983230072969 + 3 ^ 40 * 6057269 * 2
def baseEnd_6057269 : Nat := 3110290450578966640880633

theorem tailTrace_6057269 : CollatzResearch.WordTrace tailWord_6057269 prefixEnd_6057269 3110290450578966640880633 := by
  unfold tailWord_6057269
  simp only [CollatzResearch.WordTrace]
  refine ⟨220926750292556387029622861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147284500195037591353081907 220926750292556387029622861)
  ·
    refine ⟨82847531359708645136108573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220926750292556387029622861 82847531359708645136108573)
    ·
      refine ⟨31067824259890741926040715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82847531359708645136108573 31067824259890741926040715)
      ·
        refine ⟨46601736389836112889061073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31067824259890741926040715 46601736389836112889061073)
        ·
          refine ⟨34951302292377084666795805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46601736389836112889061073 34951302292377084666795805)
          ·
            refine ⟨13106738359641406750048427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34951302292377084666795805 13106738359641406750048427)
            ·
              refine ⟨19660107539462110125072641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106738359641406750048427 19660107539462110125072641)
              ·
                refine ⟨14745080654596582593804481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19660107539462110125072641 14745080654596582593804481)
                ·
                  refine ⟨11058810490947436945353361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14745080654596582593804481 11058810490947436945353361)
                  ·
                    refine ⟨8294107868210577709015021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11058810490947436945353361 8294107868210577709015021)
                    ·
                      refine ⟨3110290450578966640880633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8294107868210577709015021 3110290450578966640880633)
                      ·
                        rfl

theorem cell23_6057269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_6057269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057269 prefixEnd_6057269 := by exact prefixLift 6057269
  have htrace : WordTrace (prefixWord ++ tailWord_6057269) baseStart_6057269 baseEnd_6057269 := by
    simpa [prefixWord, tailWord_6057269, baseEnd_6057269] using wordTrace_append hprefix tailTrace_6057269
  have hstable : (prefixWord ++ tailWord_6057269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057269).length < 2 ^ (prefixWord ++ tailWord_6057269).sum := by decide
  have hdescent : baseEnd_6057269 < baseStart_6057269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057349 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_6057349 : Nat := 118140960795 + 6057349 * 2 ^ 59
def prefixEnd_6057349 : Nat := 4983230072969 + 3 ^ 40 * 6057349 * 2
def baseEnd_6057349 : Nat := 1036777176343775442626755

theorem tailTrace_6057349 : CollatzResearch.WordTrace tailWord_6057349 prefixEnd_6057349 1036777176343775442626755 := by
  unfold tailWord_6057349
  simp only [CollatzResearch.WordTrace]
  refine ⟨220929668132266560692535101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147286445421511040461690067 220929668132266560692535101)
  ·
    refine ⟨82848625549599960259700663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220929668132266560692535101 82848625549599960259700663)
    ·
      refine ⟨124272938324399940389550995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82848625549599960259700663 124272938324399940389550995)
      ·
        refine ⟨186409407486599910584326493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124272938324399940389550995 186409407486599910584326493)
        ·
          refine ⟨69903527807474966469122435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186409407486599910584326493 69903527807474966469122435)
          ·
            refine ⟨104855291711212449703683653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69903527807474966469122435 104855291711212449703683653)
            ·
              refine ⟨19660367195852334319440685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104855291711212449703683653 19660367195852334319440685)
              ·
                refine ⟨7372637698444625369790257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19660367195852334319440685 7372637698444625369790257)
                ·
                  refine ⟨5529478273833469027342693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372637698444625369790257 5529478273833469027342693)
                  ·
                    refine ⟨1036777176343775442626755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529478273833469027342693 1036777176343775442626755)
                    ·
                      rfl

theorem cell23_6057349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_6057349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057349 prefixEnd_6057349 := by exact prefixLift 6057349
  have htrace : WordTrace (prefixWord ++ tailWord_6057349) baseStart_6057349 baseEnd_6057349 := by
    simpa [prefixWord, tailWord_6057349, baseEnd_6057349] using wordTrace_append hprefix tailTrace_6057349
  have hstable : (prefixWord ++ tailWord_6057349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057349).length < 2 ^ (prefixWord ++ tailWord_6057349).sum := by decide
  have hdescent : baseEnd_6057349 < baseStart_6057349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057356 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 3, 2, 2]
def baseStart_6057356 : Nat := 118140960795 + 6057356 * 2 ^ 59
def prefixEnd_6057356 : Nat := 4983230072969 + 3 ^ 40 * 6057356 * 2
def baseEnd_6057356 : Nat := 3110335123395907800492733

theorem tailTrace_6057356 : CollatzResearch.WordTrace tailWord_6057356 prefixEnd_6057356 3110335123395907800492733 := by
  unfold tailWord_6057356
  simp only [CollatzResearch.WordTrace]
  refine ⟨110464961721620600444019961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147286615628827467258693281 110464961721620600444019961)
  ·
    refine ⟨82848721291215450333014971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110464961721620600444019961 82848721291215450333014971)
    ·
      refine ⟨124273081936823175499522457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82848721291215450333014971 124273081936823175499522457)
      ·
        refine ⟨93204811452617381624641843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124273081936823175499522457 93204811452617381624641843)
        ·
          refine ⟨139807217178926072436962765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93204811452617381624641843 139807217178926072436962765)
          ·
            refine ⟨52427706442097277163861037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139807217178926072436962765 52427706442097277163861037)
            ·
              refine ⟨19660389915786478936447889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52427706442097277163861037 19660389915786478936447889)
              ·
                refine ⟨14745292436839859202335917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19660389915786478936447889 14745292436839859202335917)
                ·
                  refine ⟨5529484663814947200875969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14745292436839859202335917 5529484663814947200875969)
                  ·
                    refine ⟨4147113497861210400656977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529484663814947200875969 4147113497861210400656977)
                    ·
                      refine ⟨3110335123395907800492733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147113497861210400656977 3110335123395907800492733)
                      ·
                        rfl

theorem cell23_6057356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_6057356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057356 prefixEnd_6057356 := by exact prefixLift 6057356
  have htrace : WordTrace (prefixWord ++ tailWord_6057356) baseStart_6057356 baseEnd_6057356 := by
    simpa [prefixWord, tailWord_6057356, baseEnd_6057356] using wordTrace_append hprefix tailTrace_6057356
  have hstable : (prefixWord ++ tailWord_6057356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057356).length < 2 ^ (prefixWord ++ tailWord_6057356).sum := by decide
  have hdescent : baseEnd_6057356 < baseStart_6057356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057373 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_6057373 : Nat := 118140960795 + 6057373 * 2 ^ 59
def prefixEnd_6057373 : Nat := 4983230072969 + 3 ^ 40 * 6057373 * 2
def baseEnd_6057373 : Nat := 3110343852567034233980155

theorem tailTrace_6057373 : CollatzResearch.WordTrace tailWord_6057373 prefixEnd_6057373 3110343852567034233980155 := by
  unfold tailWord_6057373
  simp only [CollatzResearch.WordTrace]
  refine ⟨220930543484179612791408773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147287028989453075194272515 220930543484179612791408773)
  ·
    refine ⟨41424476903283677398389145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220930543484179612791408773 41424476903283677398389145)
    ·
      refine ⟨31068357677462758048791859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41424476903283677398389145 31068357677462758048791859)
      ·
        refine ⟨46602536516194137073187789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31068357677462758048791859 46602536516194137073187789)
        ·
          refine ⟨17475951193572801402445421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46602536516194137073187789 17475951193572801402445421)
          ·
            refine ⟨6553481697589800525917033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17475951193572801402445421 6553481697589800525917033)
            ·
              refine ⟨4915111273192350394437775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553481697589800525917033 4915111273192350394437775)
              ·
                refine ⟨7372666909788525591656663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915111273192350394437775 7372666909788525591656663)
                ·
                  refine ⟨11059000364682788387484995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7372666909788525591656663 11059000364682788387484995)
                  ·
                    refine ⟨16588500547024182581227493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11059000364682788387484995 16588500547024182581227493)
                    ·
                      refine ⟨3110343852567034233980155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16588500547024182581227493 3110343852567034233980155)
                      ·
                        rfl

theorem cell23_6057373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_6057373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057373 prefixEnd_6057373 := by exact prefixLift 6057373
  have htrace : WordTrace (prefixWord ++ tailWord_6057373) baseStart_6057373 baseEnd_6057373 := by
    simpa [prefixWord, tailWord_6057373, baseEnd_6057373] using wordTrace_append hprefix tailTrace_6057373
  have hstable : (prefixWord ++ tailWord_6057373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057373).length < 2 ^ (prefixWord ++ tailWord_6057373).sum := by decide
  have hdescent : baseEnd_6057373 < baseStart_6057373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057422 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_6057422 : Nat := 118140960795 + 6057422 * 2 ^ 59
def prefixEnd_6057422 : Nat := 4983230072969 + 3 ^ 40 * 6057422 * 2
def baseEnd_6057422 : Nat := 1036789671039701514089143

theorem tailTrace_6057422 : CollatzResearch.WordTrace tailWord_6057422 prefixEnd_6057422 1036789671039701514089143 := by
  unfold tailWord_6057422
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616541332625261769992815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147288220440668062773295013 27616541332625261769992815)
  ·
    refine ⟨41424811998937892654989223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27616541332625261769992815 41424811998937892654989223)
    ·
      refine ⟨62137217998406838982483835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41424811998937892654989223 62137217998406838982483835)
      ·
        refine ⟨93205826997610258473725753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62137217998406838982483835 93205826997610258473725753)
        ·
          refine ⟨69904370248207693855294315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93205826997610258473725753 69904370248207693855294315)
          ·
            refine ⟨104856555372311540782941473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69904370248207693855294315 104856555372311540782941473)
            ·
              refine ⟨78642416529233655587206105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104856555372311540782941473 78642416529233655587206105)
              ·
                refine ⟨58981812396925241690404579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78642416529233655587206105 58981812396925241690404579)
                ·
                  refine ⟨88472718595387862535606869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58981812396925241690404579 88472718595387862535606869)
                  ·
                    refine ⟨1036789671039701514089143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88472718595387862535606869 1036789671039701514089143)
                    ·
                      rfl

theorem cell23_6057422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_6057422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057422 prefixEnd_6057422 := by exact prefixLift 6057422
  have htrace : WordTrace (prefixWord ++ tailWord_6057422) baseStart_6057422 baseEnd_6057422 := by
    simpa [prefixWord, tailWord_6057422, baseEnd_6057422] using wordTrace_append hprefix tailTrace_6057422
  have hstable : (prefixWord ++ tailWord_6057422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057422).length < 2 ^ (prefixWord ++ tailWord_6057422).sum := by decide
  have hdescent : baseEnd_6057422 < baseStart_6057422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057432 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6057432 : Nat := 118140960795 + 6057432 * 2 ^ 59
def prefixEnd_6057432 : Nat := 4983230072969 + 3 ^ 40 * 6057432 * 2
def baseEnd_6057432 : Nat := 3110374147925649503142383

theorem tailTrace_6057432 : CollatzResearch.WordTrace tailWord_6057432 prefixEnd_6057432 3110374147925649503142383 := by
  unfold tailWord_6057432
  simp only [CollatzResearch.WordTrace]
  refine ⟨110466347695482932933903275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147288463593977243911871033 110466347695482932933903275)
  ·
    refine ⟨165699521543224399400854913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110466347695482932933903275 165699521543224399400854913)
    ·
      refine ⟨124274641157418299550641185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165699521543224399400854913 124274641157418299550641185)
      ·
        refine ⟨93205980868063724662980889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124274641157418299550641185 93205980868063724662980889)
        ·
          refine ⟨69904485651047793497235667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93205980868063724662980889 69904485651047793497235667)
          ·
            refine ⟨104856728476571690245853501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69904485651047793497235667 104856728476571690245853501)
            ·
              refine ⟨39321273178714383842195063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104856728476571690245853501 39321273178714383842195063)
              ·
                refine ⟨58981909768071575763292595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39321273178714383842195063 58981909768071575763292595)
                ·
                  refine ⟨88472864652107363644938893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58981909768071575763292595 88472864652107363644938893)
                  ·
                    refine ⟨33177324244540261366852085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88472864652107363644938893 33177324244540261366852085)
                    ·
                      refine ⟨3110374147925649503142383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33177324244540261366852085 3110374147925649503142383)
                      ·
                        rfl

theorem cell23_6057432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6057432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057432 prefixEnd_6057432 := by exact prefixLift 6057432
  have htrace : WordTrace (prefixWord ++ tailWord_6057432) baseStart_6057432 baseEnd_6057432 := by
    simpa [prefixWord, tailWord_6057432, baseEnd_6057432] using wordTrace_append hprefix tailTrace_6057432
  have hstable : (prefixWord ++ tailWord_6057432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057432).length < 2 ^ (prefixWord ++ tailWord_6057432).sum := by decide
  have hdescent : baseEnd_6057432 < baseStart_6057432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057452 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 7]
def baseStart_6057452 : Nat := 118140960795 + 6057452 * 2 ^ 59
def prefixEnd_6057452 : Nat := 4983230072969 + 3 ^ 40 * 6057452 * 2
def baseEnd_6057452 : Nat := 345598268615415491654699

theorem tailTrace_6057452 : CollatzResearch.WordTrace tailWord_6057452 prefixEnd_6057452 345598268615415491654699 := by
  unfold tailWord_6057452
  simp only [CollatzResearch.WordTrace]
  refine ⟨110466712425446704641767305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147288949900595606189023073 110466712425446704641767305)
  ·
    refine ⟨82850034319085028481325479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110466712425446704641767305 82850034319085028481325479)
    ·
      refine ⟨124275051478627542721988219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82850034319085028481325479 124275051478627542721988219)
      ·
        refine ⟨186412577217941314082982329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124275051478627542721988219 186412577217941314082982329)
        ·
          refine ⟨139809432913455985562236747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186412577217941314082982329 139809432913455985562236747)
          ·
            refine ⟨209714149370183978343355121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139809432913455985562236747 209714149370183978343355121)
            ·
              refine ⟨157285612027637983757516341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209714149370183978343355121 157285612027637983757516341)
              ·
                refine ⟨14745526127591060977267157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157285612027637983757516341 14745526127591060977267157)
                ·
                  refine ⟨345598268615415491654699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14745526127591060977267157 345598268615415491654699)
                  ·
                    rfl

theorem cell23_6057452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_6057452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057452 prefixEnd_6057452 := by exact prefixLift 6057452
  have htrace : WordTrace (prefixWord ++ tailWord_6057452) baseStart_6057452 baseEnd_6057452 := by
    simpa [prefixWord, tailWord_6057452, baseEnd_6057452] using wordTrace_append hprefix tailTrace_6057452
  have hstable : (prefixWord ++ tailWord_6057452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057452).length < 2 ^ (prefixWord ++ tailWord_6057452).sum := by decide
  have hdescent : baseEnd_6057452 < baseStart_6057452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057506 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6057506 : Nat := 118140960795 + 6057506 * 2 ^ 59
def prefixEnd_6057506 : Nat := 4983230072969 + 3 ^ 40 * 6057506 * 2
def baseEnd_6057506 : Nat := 3110412145494082213617043

theorem tailTrace_6057506 : CollatzResearch.WordTrace tailWord_6057506 prefixEnd_6057506 3110412145494082213617043 := by
  unfold tailWord_6057506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55233848598174444126500093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147290262928465184337333581 55233848598174444126500093)
  ·
    refine ⟨20712693224315416547437535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55233848598174444126500093 20712693224315416547437535)
    ·
      refine ⟨31069039836473124821156303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20712693224315416547437535 31069039836473124821156303)
      ·
        refine ⟨46603559754709687231734455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31069039836473124821156303 46603559754709687231734455)
        ·
          refine ⟨69905339632064530847601683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46603559754709687231734455 69905339632064530847601683)
          ·
            refine ⟨104858009448096796271402525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69905339632064530847601683 104858009448096796271402525)
            ·
              refine ⟨39321753543036298601775947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104858009448096796271402525 39321753543036298601775947)
              ·
                refine ⟨58982630314554447902663921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39321753543036298601775947 58982630314554447902663921)
                ·
                  refine ⟨44236972735915835926997941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58982630314554447902663921 44236972735915835926997941)
                  ·
                    refine ⟨4147216193992109618156057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44236972735915835926997941 4147216193992109618156057)
                    ·
                      refine ⟨3110412145494082213617043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147216193992109618156057 3110412145494082213617043)
                      ·
                        rfl

theorem cell23_6057506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6057506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057506 prefixEnd_6057506 := by exact prefixLift 6057506
  have htrace : WordTrace (prefixWord ++ tailWord_6057506) baseStart_6057506 baseEnd_6057506 := by
    simpa [prefixWord, tailWord_6057506, baseEnd_6057506] using wordTrace_append hprefix tailTrace_6057506
  have hstable : (prefixWord ++ tailWord_6057506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057506).length < 2 ^ (prefixWord ++ tailWord_6057506).sum := by decide
  have hdescent : baseEnd_6057506 < baseStart_6057506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057533 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_6057533 : Nat := 118140960795 + 6057533 * 2 ^ 59
def prefixEnd_6057533 : Nat := 4983230072969 + 3 ^ 40 * 6057533 * 2
def baseEnd_6057533 : Nat := 1036808669823917869326473

theorem tailTrace_6057533 : CollatzResearch.WordTrace tailWord_6057533 prefixEnd_6057533 1036808669823917869326473 := by
  unfold tailWord_6057533
  simp only [CollatzResearch.WordTrace]
  refine ⟨220936379163599960117233253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147290919442399973411488835 220936379163599960117233253)
  ·
    refine ⟨41425571093174992521981235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220936379163599960117233253 41425571093174992521981235)
    ·
      refine ⟨62138356639762488782971853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41425571093174992521981235 62138356639762488782971853)
      ·
        refine ⟨23301883739910933293614445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62138356639762488782971853 23301883739910933293614445)
        ·
          refine ⟨8738206402466599985105417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23301883739910933293614445 8738206402466599985105417)
          ·
            refine ⟨6553654801849949988829063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8738206402466599985105417 6553654801849949988829063)
            ·
              refine ⟨9830482202774924983243595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553654801849949988829063 9830482202774924983243595)
              ·
                refine ⟨14745723304162387474865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830482202774924983243595 14745723304162387474865393)
                ·
                  refine ⟨11059292478121790606149045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14745723304162387474865393 11059292478121790606149045)
                  ·
                    refine ⟨1036808669823917869326473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11059292478121790606149045 1036808669823917869326473)
                    ·
                      rfl

theorem cell23_6057533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_6057533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057533 prefixEnd_6057533 := by exact prefixLift 6057533
  have htrace : WordTrace (prefixWord ++ tailWord_6057533) baseStart_6057533 baseEnd_6057533 := by
    simpa [prefixWord, tailWord_6057533, baseEnd_6057533] using wordTrace_append hprefix tailTrace_6057533
  have hstable : (prefixWord ++ tailWord_6057533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057533).length < 2 ^ (prefixWord ++ tailWord_6057533).sum := by decide
  have hdescent : baseEnd_6057533 < baseStart_6057533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057556 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_6057556 : Nat := 118140960795 + 6057556 * 2 ^ 59
def prefixEnd_6057556 : Nat := 4983230072969 + 3 ^ 40 * 6057556 * 2
def baseEnd_6057556 : Nat := 3110437819526807017991813

theorem tailTrace_6057556 : CollatzResearch.WordTrace tailWord_6057556 prefixEnd_6057556 3110437819526807017991813 := by
  unfold tailWord_6057556
  simp only [CollatzResearch.WordTrace]
  refine ⟨110468609021258317522660261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147291478695011090030213681 110468609021258317522660261)
  ·
    refine ⟨20712864191485934535498799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110468609021258317522660261 20712864191485934535498799)
    ·
      refine ⟨31069296287228901803248199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20712864191485934535498799 31069296287228901803248199)
      ·
        refine ⟨46603944430843352704872299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31069296287228901803248199 46603944430843352704872299)
        ·
          refine ⟨69905916646265029057308449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46603944430843352704872299 69905916646265029057308449)
          ·
            refine ⟨52429437484698771792981337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69905916646265029057308449 52429437484698771792981337)
            ·
              refine ⟨39322078113524078844736003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52429437484698771792981337 39322078113524078844736003)
              ·
                refine ⟨58983117170286118267104005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39322078113524078844736003 58983117170286118267104005)
                ·
                  refine ⟨11059334469428647175082001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58983117170286118267104005 11059334469428647175082001)
                  ·
                    refine ⟨8294500852071485381311501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11059334469428647175082001 8294500852071485381311501)
                    ·
                      refine ⟨3110437819526807017991813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8294500852071485381311501 3110437819526807017991813)
                      ·
                        rfl

theorem cell23_6057556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_6057556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057556 prefixEnd_6057556 := by exact prefixLift 6057556
  have htrace : WordTrace (prefixWord ++ tailWord_6057556) baseStart_6057556 baseEnd_6057556 := by
    simpa [prefixWord, tailWord_6057556, baseEnd_6057556] using wordTrace_append hprefix tailTrace_6057556
  have hstable : (prefixWord ++ tailWord_6057556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057556).length < 2 ^ (prefixWord ++ tailWord_6057556).sum := by decide
  have hdescent : baseEnd_6057556 < baseStart_6057556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057559 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 8]
def baseStart_6057559 : Nat := 118140960795 + 6057559 * 2 ^ 59
def prefixEnd_6057559 : Nat := 4983230072969 + 3 ^ 40 * 6057559 * 2
def baseEnd_6057559 : Nat := 345604373329863389583811

theorem tailTrace_6057559 : CollatzResearch.WordTrace tailWord_6057559 prefixEnd_6057559 345604373329863389583811 := by
  unfold tailWord_6057559
  simp only [CollatzResearch.WordTrace]
  refine ⟨220937327461505766557679731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147291551641003844371786487 220937327461505766557679731)
  ·
    refine ⟨331405991192258649836519597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220937327461505766557679731 331405991192258649836519597)
    ·
      refine ⟨124277246697096993688694849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331405991192258649836519597 124277246697096993688694849)
      ·
        refine ⟨93207935022822745266521137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124277246697096993688694849 93207935022822745266521137)
        ·
          refine ⟨69905951267117058949890853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93207935022822745266521137 69905951267117058949890853)
          ·
            refine ⟨13107365862584448553104535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69905951267117058949890853 13107365862584448553104535)
            ·
              refine ⟨19661048793876672829656803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13107365862584448553104535 19661048793876672829656803)
              ·
                refine ⟨29491573190815009244485205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19661048793876672829656803 29491573190815009244485205)
                ·
                  refine ⟨345604373329863389583811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29491573190815009244485205 345604373329863389583811)
                  ·
                    rfl

theorem cell23_6057559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 8].length) (baseStart_6057559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057559 prefixEnd_6057559 := by exact prefixLift 6057559
  have htrace : WordTrace (prefixWord ++ tailWord_6057559) baseStart_6057559 baseEnd_6057559 := by
    simpa [prefixWord, tailWord_6057559, baseEnd_6057559] using wordTrace_append hprefix tailTrace_6057559
  have hstable : (prefixWord ++ tailWord_6057559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057559).length < 2 ^ (prefixWord ++ tailWord_6057559).sum := by decide
  have hdescent : baseEnd_6057559 < baseStart_6057559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057653 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_6057653 : Nat := 118140960795 + 6057653 * 2 ^ 59
def prefixEnd_6057653 : Nat := 4983230072969 + 3 ^ 40 * 6057653 * 2
def baseEnd_6057653 : Nat := 1036829209050097712826289

theorem tailTrace_6057653 : CollatzResearch.WordTrace tailWord_6057653 prefixEnd_6057653 1036829209050097712826289 := by
  unfold tailWord_6057653
  simp only [CollatzResearch.WordTrace]
  refine ⟨220940755923165220611601613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147293837282110147074401075 220940755923165220611601613)
  ·
    refine ⟨82852783471186957729350605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220940755923165220611601613 82852783471186957729350605)
    ·
      refine ⟨31069793801695109148506477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82852783471186957729350605 31069793801695109148506477)
      ·
        refine ⟨11651172675635665930689929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31069793801695109148506477 11651172675635665930689929)
        ·
          refine ⟨8738379506726749448017447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11651172675635665930689929 8738379506726749448017447)
          ·
            refine ⟨13107569260090124172026171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738379506726749448017447 13107569260090124172026171)
            ·
              refine ⟨19661353890135186258039257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13107569260090124172026171 19661353890135186258039257)
              ·
                refine ⟨14746015417601389693529443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19661353890135186258039257 14746015417601389693529443)
                ·
                  refine ⟨22119023126402084540294165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14746015417601389693529443 22119023126402084540294165)
                  ·
                    refine ⟨1036829209050097712826289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22119023126402084540294165 1036829209050097712826289)
                    ·
                      rfl

theorem cell23_6057653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_6057653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057653 prefixEnd_6057653 := by exact prefixLift 6057653
  have htrace : WordTrace (prefixWord ++ tailWord_6057653) baseStart_6057653 baseEnd_6057653 := by
    simpa [prefixWord, tailWord_6057653, baseEnd_6057653] using wordTrace_append hprefix tailTrace_6057653
  have hstable : (prefixWord ++ tailWord_6057653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057653).length < 2 ^ (prefixWord ++ tailWord_6057653).sum := by decide
  have hdescent : baseEnd_6057653 < baseStart_6057653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057660 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_6057660 : Nat := 118140960795 + 6057660 * 2 ^ 59
def prefixEnd_6057660 : Nat := 4983230072969 + 3 ^ 40 * 6057660 * 2
def baseEnd_6057660 : Nat := 3110491221514874611091335

theorem tailTrace_6057660 : CollatzResearch.WordTrace tailWord_6057660 prefixEnd_6057660 3110491221514874611091335 := by
  unfold tailWord_6057660
  simp only [CollatzResearch.WordTrace]
  refine ⟨110470505617069930403553217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147294007489426573871404289 110470505617069930403553217)
  ·
    refine ⟨82852879212802447802664913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110470505617069930403553217 82852879212802447802664913)
    ·
      refine ⟨62139659409601835851998685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82852879212802447802664913 62139659409601835851998685)
      ·
        refine ⟨23302372278600688444499507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62139659409601835851998685 23302372278600688444499507)
        ·
          refine ⟨34953558417901032666749261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23302372278600688444499507 34953558417901032666749261)
          ·
            refine ⟨13107584406712887250030973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34953558417901032666749261 13107584406712887250030973)
            ·
              refine ⟨4915344152517332718761615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13107584406712887250030973 4915344152517332718761615)
              ·
                refine ⟨7373016228775999078142423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915344152517332718761615 7373016228775999078142423)
                ·
                  refine ⟨11059524343163998617213635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373016228775999078142423 11059524343163998617213635)
                  ·
                    refine ⟨16589286514745997925820453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11059524343163998617213635 16589286514745997925820453)
                    ·
                      refine ⟨3110491221514874611091335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16589286514745997925820453 3110491221514874611091335)
                      ·
                        rfl

theorem cell23_6057660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_6057660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057660 prefixEnd_6057660 := by exact prefixLift 6057660
  have htrace : WordTrace (prefixWord ++ tailWord_6057660) baseStart_6057660 baseEnd_6057660 := by
    simpa [prefixWord, tailWord_6057660, baseEnd_6057660] using wordTrace_append hprefix tailTrace_6057660
  have hstable : (prefixWord ++ tailWord_6057660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057660).length < 2 ^ (prefixWord ++ tailWord_6057660).sum := by decide
  have hdescent : baseEnd_6057660 < baseStart_6057660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057741 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6057741 : Nat := 118140960795 + 6057741 * 2 ^ 59
def prefixEnd_6057741 : Nat := 4983230072969 + 3 ^ 40 * 6057741 * 2
def baseEnd_6057741 : Nat := 3110532813447888794178463

theorem tailTrace_6057741 : CollatzResearch.WordTrace tailWord_6057741 prefixEnd_6057741 3110532813447888794178463 := by
  unfold tailWord_6057741
  simp only [CollatzResearch.WordTrace]
  refine ⟨220943965546846411640805077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147295977031230941093870051 220943965546846411640805077)
  ·
    refine ⟨5178374192504212772831369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 220943965546846411640805077 5178374192504212772831369)
    ·
      refine ⟨3883780644378159579623527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5178374192504212772831369 3883780644378159579623527)
      ·
        refine ⟨5825670966567239369435291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883780644378159579623527 5825670966567239369435291)
        ·
          refine ⟨8738506449850859054152937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825670966567239369435291 8738506449850859054152937)
          ·
            refine ⟨6553879837388144290614703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8738506449850859054152937 6553879837388144290614703)
            ·
              refine ⟨9830819756082216435922055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553879837388144290614703 9830819756082216435922055)
              ·
                refine ⟨14746229634123324653883083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830819756082216435922055 14746229634123324653883083)
                ·
                  refine ⟨22119344451184986980824625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14746229634123324653883083 22119344451184986980824625)
                  ·
                    refine ⟨16589508338388740235618469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22119344451184986980824625 16589508338388740235618469)
                    ·
                      refine ⟨3110532813447888794178463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16589508338388740235618469 3110532813447888794178463)
                      ·
                        rfl

theorem cell23_6057741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6057741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057741 prefixEnd_6057741 := by exact prefixLift 6057741
  have htrace : WordTrace (prefixWord ++ tailWord_6057741) baseStart_6057741 baseEnd_6057741 := by
    simpa [prefixWord, tailWord_6057741, baseEnd_6057741] using wordTrace_append hprefix tailTrace_6057741
  have hstable : (prefixWord ++ tailWord_6057741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057741).length < 2 ^ (prefixWord ++ tailWord_6057741).sum := by decide
  have hdescent : baseEnd_6057741 < baseStart_6057741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057756 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 7]
def baseStart_6057756 : Nat := 118140960795 + 6057756 * 2 ^ 59
def prefixEnd_6057756 : Nat := 4983230072969 + 3 ^ 40 * 6057756 * 2
def baseEnd_6057756 : Nat := 345615612850856248387877

theorem tailTrace_6057756 : CollatzResearch.WordTrace tailWord_6057756 prefixEnd_6057756 345615612850856248387877 := by
  unfold tailWord_6057756
  simp only [CollatzResearch.WordTrace]
  refine ⟨110472256320896034601300561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147296341761194712801734081 110472256320896034601300561)
  ·
    refine ⟨82854192240672025950975421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110472256320896034601300561 82854192240672025950975421)
    ·
      refine ⟨31070322090252009731615783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82854192240672025950975421 31070322090252009731615783)
      ·
        refine ⟨46605483135378014597423675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31070322090252009731615783 46605483135378014597423675)
        ·
          refine ⟨69908224703067021896135513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46605483135378014597423675 69908224703067021896135513)
          ·
            refine ⟨52431168527300266422101635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69908224703067021896135513 52431168527300266422101635)
            ·
              refine ⟨78646752790950399633152453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52431168527300266422101635 78646752790950399633152453)
              ·
                refine ⟨14746266148303199931216085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78646752790950399633152453 14746266148303199931216085)
                ·
                  refine ⟨345615612850856248387877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14746266148303199931216085 345615612850856248387877)
                  ·
                    rfl

theorem cell23_6057756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_6057756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057756 prefixEnd_6057756 := by exact prefixLift 6057756
  have htrace : WordTrace (prefixWord ++ tailWord_6057756) baseStart_6057756 baseEnd_6057756 := by
    simpa [prefixWord, tailWord_6057756, baseEnd_6057756] using wordTrace_append hprefix tailTrace_6057756
  have hstable : (prefixWord ++ tailWord_6057756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057756).length < 2 ^ (prefixWord ++ tailWord_6057756).sum := by decide
  have hdescent : baseEnd_6057756 < baseStart_6057756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057790 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_6057790 : Nat := 118140960795 + 6057790 * 2 ^ 59
def prefixEnd_6057790 : Nat := 4983230072969 + 3 ^ 40 * 6057790 * 2
def baseEnd_6057790 : Nat := 345617552666662122496193

theorem tailTrace_6057790 : CollatzResearch.WordTrace tailWord_6057790 prefixEnd_6057790 345617552666662122496193 := by
  unfold tailWord_6057790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27618219090458611626167353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147297168482445928672892549 27618219090458611626167353)
  ·
    refine ⟨20713664317843958719625515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27618219090458611626167353 20713664317843958719625515)
    ·
      refine ⟨31070496476765938079438273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20713664317843958719625515 31070496476765938079438273)
      ·
        refine ⟨23302872357574453559578705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31070496476765938079438273 23302872357574453559578705)
        ·
          refine ⟨17477154268180840169684029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23302872357574453559578705 17477154268180840169684029)
          ·
            refine ⟨6553932850567815063631511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17477154268180840169684029 6553932850567815063631511)
            ·
              refine ⟨9830899275851722595447267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553932850567815063631511 9830899275851722595447267)
              ·
                refine ⟨14746348913777583893170901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830899275851722595447267 14746348913777583893170901)
                ·
                  refine ⟨345617552666662122496193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14746348913777583893170901 345617552666662122496193)
                  ·
                    rfl

theorem cell23_6057790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_6057790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057790 prefixEnd_6057790 := by exact prefixLift 6057790
  have htrace : WordTrace (prefixWord ++ tailWord_6057790) baseStart_6057790 baseEnd_6057790 := by
    simpa [prefixWord, tailWord_6057790, baseEnd_6057790] using wordTrace_append hprefix tailTrace_6057790
  have hstable : (prefixWord ++ tailWord_6057790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057790).length < 2 ^ (prefixWord ++ tailWord_6057790).sum := by decide
  have hdescent : baseEnd_6057790 < baseStart_6057790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057823 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_6057823 : Nat := 118140960795 + 6057823 * 2 ^ 59
def prefixEnd_6057823 : Nat := 4983230072969 + 3 ^ 40 * 6057823 * 2
def baseEnd_6057823 : Nat := 3110574918861557473353085

theorem tailTrace_6057823 : CollatzResearch.WordTrace tailWord_6057823 prefixEnd_6057823 3110574918861557473353085 := by
  unfold tailWord_6057823
  simp only [CollatzResearch.WordTrace]
  refine ⟨220946956332549339645290123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147297970888366226430193415 220946956332549339645290123)
  ·
    refine ⟨331420434498824009467935185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220946956332549339645290123 331420434498824009467935185)
    ·
      refine ⟨248565325874118007100951389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331420434498824009467935185 248565325874118007100951389)
      ·
        refine ⟨93211997202794252662856771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248565325874118007100951389 93211997202794252662856771)
        ·
          refine ⟨139817995804191378994285157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93211997202794252662856771 139817995804191378994285157)
          ·
            refine ⟨26215874213285883561428467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139817995804191378994285157 26215874213285883561428467)
            ·
              refine ⟨39323811319928825342142701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26215874213285883561428467 39323811319928825342142701)
              ·
                refine ⟨14746429244973309503303513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39323811319928825342142701 14746429244973309503303513)
                ·
                  refine ⟨11059821933729982127477635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14746429244973309503303513 11059821933729982127477635)
                  ·
                    refine ⟨16589732900594973191216453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11059821933729982127477635 16589732900594973191216453)
                    ·
                      refine ⟨3110574918861557473353085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16589732900594973191216453 3110574918861557473353085)
                      ·
                        rfl

theorem cell23_6057823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_6057823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057823 prefixEnd_6057823 := by exact prefixLift 6057823
  have htrace : WordTrace (prefixWord ++ tailWord_6057823) baseStart_6057823 baseEnd_6057823 := by
    simpa [prefixWord, tailWord_6057823, baseEnd_6057823] using wordTrace_append hprefix tailTrace_6057823
  have hstable : (prefixWord ++ tailWord_6057823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057823).length < 2 ^ (prefixWord ++ tailWord_6057823).sum := by decide
  have hdescent : baseEnd_6057823 < baseStart_6057823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057884 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_6057884 : Nat := 118140960795 + 6057884 * 2 ^ 59
def prefixEnd_6057884 : Nat := 4983230072969 + 3 ^ 40 * 6057884 * 2
def baseEnd_6057884 : Nat := 1036868747060493911563435

theorem tailTrace_6057884 : CollatzResearch.WordTrace tailWord_6057884 prefixEnd_6057884 1036868747060493911563435 := by
  unfold tailWord_6057884
  simp only [CollatzResearch.WordTrace]
  refine ⟨110474590592664173531630353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147299454123552231375507137 110474590592664173531630353)
  ·
    refine ⟨82855942944498130148722765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110474590592664173531630353 82855942944498130148722765)
    ·
      refine ⟨31070978604186798805771037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82855942944498130148722765 31070978604186798805771037)
      ·
        refine ⟨11651616976570049552164139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31070978604186798805771037 11651616976570049552164139)
        ·
          refine ⟨17477425464855074328246209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651616976570049552164139 17477425464855074328246209)
          ·
            refine ⟨13108069098641305746184657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17477425464855074328246209 13108069098641305746184657)
            ·
              refine ⟨9831051823980979309638493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13108069098641305746184657 9831051823980979309638493)
              ·
                refine ⟨3686644433992867241114435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9831051823980979309638493 3686644433992867241114435)
                ·
                  refine ⟨5529966650989300861671653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686644433992867241114435 5529966650989300861671653)
                  ·
                    refine ⟨1036868747060493911563435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5529966650989300861671653 1036868747060493911563435)
                    ·
                      rfl

theorem cell23_6057884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_6057884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057884 prefixEnd_6057884 := by exact prefixLift 6057884
  have htrace : WordTrace (prefixWord ++ tailWord_6057884) baseStart_6057884 baseEnd_6057884 := by
    simpa [prefixWord, tailWord_6057884, baseEnd_6057884] using wordTrace_append hprefix tailTrace_6057884
  have hstable : (prefixWord ++ tailWord_6057884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057884).length < 2 ^ (prefixWord ++ tailWord_6057884).sum := by decide
  have hdescent : baseEnd_6057884 < baseStart_6057884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057907 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 1, 1, 3]
def baseStart_6057907 : Nat := 118140960795 + 6057907 * 2 ^ 59
def prefixEnd_6057907 : Nat := 4983230072969 + 3 ^ 40 * 6057907 * 2
def baseEnd_6057907 : Nat := 3110618051236535144702699

theorem tailTrace_6057907 : CollatzResearch.WordTrace tailWord_6057907 prefixEnd_6057907 3110618051236535144702699 := by
  unfold tailWord_6057907
  simp only [CollatzResearch.WordTrace]
  refine ⟨220950020064245021991347975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147300013376163347994231983 220950020064245021991347975)
  ·
    refine ⟨331425030096367532987021963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220950020064245021991347975 331425030096367532987021963)
    ·
      refine ⟨497137545144551299480532945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331425030096367532987021963 497137545144551299480532945)
      ·
        refine ⟨372853158858413474610399709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497137545144551299480532945 372853158858413474610399709)
        ·
          refine ⟨139819934571905052978899891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372853158858413474610399709 139819934571905052978899891)
          ·
            refine ⟨209729901857857579468349837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139819934571905052978899891 209729901857857579468349837)
            ·
              refine ⟨78648713196696592300631189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209729901857857579468349837 78648713196696592300631189)
              ·
                refine ⟨3686658431095152764092087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78648713196696592300631189 3686658431095152764092087)
                ·
                  refine ⟨5529987646642729146138131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686658431095152764092087 5529987646642729146138131)
                  ·
                    refine ⟨8294981469964093719207197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5529987646642729146138131 8294981469964093719207197)
                    ·
                      refine ⟨3110618051236535144702699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8294981469964093719207197 3110618051236535144702699)
                      ·
                        rfl

theorem cell23_6057907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 1, 3].length) (baseStart_6057907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057907 prefixEnd_6057907 := by exact prefixLift 6057907
  have htrace : WordTrace (prefixWord ++ tailWord_6057907) baseStart_6057907 baseEnd_6057907 := by
    simpa [prefixWord, tailWord_6057907, baseEnd_6057907] using wordTrace_append hprefix tailTrace_6057907
  have hstable : (prefixWord ++ tailWord_6057907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057907).length < 2 ^ (prefixWord ++ tailWord_6057907).sum := by decide
  have hdescent : baseEnd_6057907 < baseStart_6057907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057923 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 8, 4]
def baseStart_6057923 : Nat := 118140960795 + 6057923 * 2 ^ 59
def prefixEnd_6057923 : Nat := 4983230072969 + 3 ^ 40 * 6057923 * 2
def baseEnd_6057923 : Nat := 1036875422309002360700875

theorem tailTrace_6057923 : CollatzResearch.WordTrace tailWord_6057923 prefixEnd_6057923 1036875422309002360700875 := by
  unfold tailWord_6057923
  simp only [CollatzResearch.WordTrace]
  refine ⟨220950603632187056723930423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147300402421458037815953615 220950603632187056723930423)
  ·
    refine ⟨331425905448280585085895635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220950603632187056723930423 331425905448280585085895635)
    ·
      refine ⟨497138858172420877628843453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331425905448280585085895635 497138858172420877628843453)
      ·
        refine ⟨186427071814657829110816295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497138858172420877628843453 186427071814657829110816295)
        ·
          refine ⟨279640607721986743666224443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186427071814657829110816295 279640607721986743666224443)
          ·
            refine ⟨419460911582980115499336665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279640607721986743666224443 419460911582980115499336665)
            ·
              refine ⟨314595683687235086624502499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419460911582980115499336665 314595683687235086624502499)
              ·
                refine ⟨471893525530852629936753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314595683687235086624502499 471893525530852629936753749)
                ·
                  refine ⟨5530002252314679257071333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 471893525530852629936753749 5530002252314679257071333)
                  ·
                    refine ⟨1036875422309002360700875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530002252314679257071333 1036875422309002360700875)
                    ·
                      rfl

theorem cell23_6057923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 4].length) (baseStart_6057923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057923 prefixEnd_6057923 := by exact prefixLift 6057923
  have htrace : WordTrace (prefixWord ++ tailWord_6057923) baseStart_6057923 baseEnd_6057923 := by
    simpa [prefixWord, tailWord_6057923, baseEnd_6057923] using wordTrace_append hprefix tailTrace_6057923
  have hstable : (prefixWord ++ tailWord_6057923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057923).length < 2 ^ (prefixWord ++ tailWord_6057923).sum := by decide
  have hdescent : baseEnd_6057923 < baseStart_6057923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057930 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_6057930 : Nat := 118140960795 + 6057930 * 2 ^ 59
def prefixEnd_6057930 : Nat := 4983230072969 + 3 ^ 40 * 6057930 * 2
def baseEnd_6057930 : Nat := 3110629861291588554715093

theorem tailTrace_6057930 : CollatzResearch.WordTrace tailWord_6057930 prefixEnd_6057930 3110629861291588554715093 := by
  unfold tailWord_6057930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55237714735790424229858811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147300572628774464612956829 55237714735790424229858811)
  ·
    refine ⟨82856572103685636344788217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55237714735790424229858811 82856572103685636344788217)
    ·
      refine ⟨62142429077764227258591163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82856572103685636344788217 62142429077764227258591163)
      ·
        refine ⟨93213643616646340887886745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62142429077764227258591163 93213643616646340887886745)
        ·
          refine ⟨69910232712484755665915059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93213643616646340887886745 69910232712484755665915059)
          ·
            refine ⟨104865349068727133498872589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69910232712484755665915059 104865349068727133498872589)
            ·
              refine ⟨39324505900772675062077221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104865349068727133498872589 39324505900772675062077221)
              ·
                refine ⟨7373344856394876574139479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39324505900772675062077221 7373344856394876574139479)
                ·
                  refine ⟨11060017284592314861209219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373344856394876574139479 11060017284592314861209219)
                  ·
                    refine ⟨16590025926888472291813829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11060017284592314861209219 16590025926888472291813829)
                    ·
                      refine ⟨3110629861291588554715093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16590025926888472291813829 3110629861291588554715093)
                      ·
                        rfl

theorem cell23_6057930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_6057930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057930 prefixEnd_6057930 := by exact prefixLift 6057930
  have htrace : WordTrace (prefixWord ++ tailWord_6057930) baseStart_6057930 baseEnd_6057930 := by
    simpa [prefixWord, tailWord_6057930, baseEnd_6057930] using wordTrace_append hprefix tailTrace_6057930
  have hstable : (prefixWord ++ tailWord_6057930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057930).length < 2 ^ (prefixWord ++ tailWord_6057930).sum := by decide
  have hdescent : baseEnd_6057930 < baseStart_6057930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057940 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_6057940 : Nat := 118140960795 + 6057940 * 2 ^ 59
def prefixEnd_6057940 : Nat := 4983230072969 + 3 ^ 40 * 6057940 * 2
def baseEnd_6057940 : Nat := 1036878332032711171863349

theorem tailTrace_6057940 : CollatzResearch.WordTrace tailWord_6057940 prefixEnd_6057940 1036878332032711171863349 := by
  unfold tailWord_6057940
  simp only [CollatzResearch.WordTrace]
  refine ⟨110475611836562734313649637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147300815782083645751532849 110475611836562734313649637)
  ·
    refine ⟨20714177219355512683809307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110475611836562734313649637 20714177219355512683809307)
    ·
      refine ⟨31071265829033269025713961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714177219355512683809307 31071265829033269025713961)
      ·
        refine ⟨23303449371774951769285471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31071265829033269025713961 23303449371774951769285471)
        ·
          refine ⟨34955174057662427653928207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23303449371774951769285471 34955174057662427653928207)
          ·
            refine ⟨52432761086493641480892311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34955174057662427653928207 52432761086493641480892311)
            ·
              refine ⟨78649141629740462221338467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52432761086493641480892311 78649141629740462221338467)
              ·
                refine ⟨117973712444610693332007701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78649141629740462221338467 117973712444610693332007701)
                ·
                  refine ⟨5530017770841126249937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117973712444610693332007701 5530017770841126249937861)
                  ·
                    refine ⟨1036878332032711171863349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530017770841126249937861 1036878332032711171863349)
                    ·
                      rfl

theorem cell23_6057940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_6057940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057940 prefixEnd_6057940 := by exact prefixLift 6057940
  have htrace : WordTrace (prefixWord ++ tailWord_6057940) baseStart_6057940 baseEnd_6057940 := by
    simpa [prefixWord, tailWord_6057940, baseEnd_6057940] using wordTrace_append hprefix tailTrace_6057940
  have hstable : (prefixWord ++ tailWord_6057940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057940).length < 2 ^ (prefixWord ++ tailWord_6057940).sum := by decide
  have hdescent : baseEnd_6057940 < baseStart_6057940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057941 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6057941 : Nat := 118140960795 + 6057941 * 2 ^ 59
def prefixEnd_6057941 : Nat := 4983230072969 + 3 ^ 40 * 6057941 * 2
def baseEnd_6057941 : Nat := 3110635509578788011677543

theorem tailTrace_6057941 : CollatzResearch.WordTrace tailWord_6057941 prefixEnd_6057941 3110635509578788011677543 := by
  unfold tailWord_6057941
  simp only [CollatzResearch.WordTrace]
  refine ⟨220951260146121845798085677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147300840097414563865390451 220951260146121845798085677)
  ·
    refine ⟨82856722554795692174282129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220951260146121845798085677 82856722554795692174282129)
    ·
      refine ⟨62142541916096769130711597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82856722554795692174282129 62142541916096769130711597)
      ·
        refine ⟨23303453218536288424016849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62142541916096769130711597 23303453218536288424016849)
        ·
          refine ⟨17477589913902216318012637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23303453218536288424016849 17477589913902216318012637)
          ·
            refine ⟨6554096217713331119254739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17477589913902216318012637 6554096217713331119254739)
            ·
              refine ⟨9831144326569996678882109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554096217713331119254739 9831144326569996678882109)
              ·
                refine ⟨3686679122463748754580791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9831144326569996678882109 3686679122463748754580791)
                ·
                  refine ⟨5530018683695623131871187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686679122463748754580791 5530018683695623131871187)
                  ·
                    refine ⟨8295028025543434697806781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530018683695623131871187 8295028025543434697806781)
                    ·
                      refine ⟨3110635509578788011677543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295028025543434697806781 3110635509578788011677543)
                      ·
                        rfl

theorem cell23_6057941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6057941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057941 prefixEnd_6057941 := by exact prefixLift 6057941
  have htrace : WordTrace (prefixWord ++ tailWord_6057941) baseStart_6057941 baseEnd_6057941 := by
    simpa [prefixWord, tailWord_6057941, baseEnd_6057941] using wordTrace_append hprefix tailTrace_6057941
  have hstable : (prefixWord ++ tailWord_6057941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057941).length < 2 ^ (prefixWord ++ tailWord_6057941).sum := by decide
  have hdescent : baseEnd_6057941 < baseStart_6057941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057943 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_6057943 : Nat := 118140960795 + 6057943 * 2 ^ 59
def prefixEnd_6057943 : Nat := 4983230072969 + 3 ^ 40 * 6057943 * 2
def baseEnd_6057943 : Nat := 3110636536540097003852533

theorem tailTrace_6057943 : CollatzResearch.WordTrace tailWord_6057943 prefixEnd_6057943 3110636536540097003852533 := by
  unfold tailWord_6057943
  simp only [CollatzResearch.WordTrace]
  refine ⟨220951333092114600139658483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147300888728076400093105655 220951333092114600139658483)
  ·
    refine ⟨331426999638171900209487725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220951333092114600139658483 331426999638171900209487725)
    ·
      refine ⟨124285124864314462578557897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331426999638171900209487725 124285124864314462578557897)
      ·
        refine ⟨93213843648235846933918423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124285124864314462578557897 93213843648235846933918423)
        ·
          refine ⟨139820765472353770400877635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93213843648235846933918423 139820765472353770400877635)
          ·
            refine ⟨209731148208530655601316453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139820765472353770400877635 209731148208530655601316453)
            ·
              refine ⟨39324590289099497925246835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209731148208530655601316453 39324590289099497925246835)
              ·
                refine ⟨58986885433649246887870253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39324590289099497925246835 58986885433649246887870253)
                ·
                  refine ⟨22120082037618467582951345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58986885433649246887870253 22120082037618467582951345)
                  ·
                    refine ⟨16590061528213850687213509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22120082037618467582951345 16590061528213850687213509)
                    ·
                      refine ⟨3110636536540097003852533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16590061528213850687213509 3110636536540097003852533)
                      ·
                        rfl

theorem cell23_6057943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_6057943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057943 prefixEnd_6057943 := by exact prefixLift 6057943
  have htrace : WordTrace (prefixWord ++ tailWord_6057943) baseStart_6057943 baseEnd_6057943 := by
    simpa [prefixWord, tailWord_6057943, baseEnd_6057943] using wordTrace_append hprefix tailTrace_6057943
  have hstable : (prefixWord ++ tailWord_6057943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057943).length < 2 ^ (prefixWord ++ tailWord_6057943).sum := by decide
  have hdescent : baseEnd_6057943 < baseStart_6057943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057964 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 1, 2, 2]
def baseStart_6057964 : Nat := 118140960795 + 6057964 * 2 ^ 59
def prefixEnd_6057964 : Nat := 4983230072969 + 3 ^ 40 * 6057964 * 2
def baseEnd_6057964 : Nat := 3110647319633841421689937

theorem tailTrace_6057964 : CollatzResearch.WordTrace tailWord_6057964 prefixEnd_6057964 3110647319633841421689937 := by
  unfold tailWord_6057964
  simp only [CollatzResearch.WordTrace]
  refine ⟨110476049512519260363086473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147301399350025680484115297 110476049512519260363086473)
  ·
    refine ⟨82857037134389445272314855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110476049512519260363086473 82857037134389445272314855)
    ·
      refine ⟨124285555701584167908472283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82857037134389445272314855 124285555701584167908472283)
      ·
        refine ⟨186428333552376251862708425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124285555701584167908472283 186428333552376251862708425)
        ·
          refine ⟨139821250164282188897031319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186428333552376251862708425 139821250164282188897031319)
          ·
            refine ⟨209731875246423283345546979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139821250164282188897031319 209731875246423283345546979)
            ·
              refine ⟨314597812869634925018320469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209731875246423283345546979 314597812869634925018320469)
              ·
                refine ⟨3686693119566034277558443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 314597812869634925018320469 3686693119566034277558443)
                ·
                  refine ⟨5530039679349051416337665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686693119566034277558443 5530039679349051416337665)
                  ·
                    refine ⟨4147529759511788562253249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530039679349051416337665 4147529759511788562253249)
                    ·
                      refine ⟨3110647319633841421689937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147529759511788562253249 3110647319633841421689937)
                      ·
                        rfl

theorem cell23_6057964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_6057964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057964 prefixEnd_6057964 := by exact prefixLift 6057964
  have htrace : WordTrace (prefixWord ++ tailWord_6057964) baseStart_6057964 baseEnd_6057964 := by
    simpa [prefixWord, tailWord_6057964, baseEnd_6057964] using wordTrace_append hprefix tailTrace_6057964
  have hstable : (prefixWord ++ tailWord_6057964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057964).length < 2 ^ (prefixWord ++ tailWord_6057964).sum := by decide
  have hdescent : baseEnd_6057964 < baseStart_6057964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057974 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6057974 : Nat := 118140960795 + 6057974 * 2 ^ 59
def prefixEnd_6057974 : Nat := 4983230072969 + 3 ^ 40 * 6057974 * 2
def baseEnd_6057974 : Nat := 1036884151480128794188297

theorem tailTrace_6057974 : CollatzResearch.WordTrace tailWord_6057974 prefixEnd_6057974 1036884151480128794188297 := by
  unfold tailWord_6057974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809528984687643277127311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147301642503334861622691317 13809528984687643277127311)
  ·
    refine ⟨20714293477031464915690967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13809528984687643277127311 20714293477031464915690967)
    ·
      refine ⟨31071440215547197373536451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714293477031464915690967 31071440215547197373536451)
      ·
        refine ⟨46607160323320796060304677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31071440215547197373536451 46607160323320796060304677)
        ·
          refine ⟨8738842560622649261307127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46607160323320796060304677 8738842560622649261307127)
          ·
            refine ⟨13108263840933973891960691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738842560622649261307127 13108263840933973891960691)
            ·
              refine ⟨19662395761400960837941037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13108263840933973891960691 19662395761400960837941037)
              ·
                refine ⟨7373398410525360314227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19662395761400960837941037 7373398410525360314227889)
                ·
                  refine ⟨5530048807894020235670917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7373398410525360314227889 5530048807894020235670917)
                  ·
                    refine ⟨1036884151480128794188297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530048807894020235670917 1036884151480128794188297)
                    ·
                      rfl

theorem cell23_6057974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6057974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057974 prefixEnd_6057974 := by exact prefixLift 6057974
  have htrace : WordTrace (prefixWord ++ tailWord_6057974) baseStart_6057974 baseEnd_6057974 := by
    simpa [prefixWord, tailWord_6057974, baseEnd_6057974] using wordTrace_append hprefix tailTrace_6057974
  have hstable : (prefixWord ++ tailWord_6057974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057974).length < 2 ^ (prefixWord ++ tailWord_6057974).sum := by decide
  have hdescent : baseEnd_6057974 < baseStart_6057974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6057980 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_6057980 : Nat := 118140960795 + 6057980 * 2 ^ 59
def prefixEnd_6057980 : Nat := 4983230072969 + 3 ^ 40 * 6057980 * 2
def baseEnd_6057980 : Nat := 3110655535324313359089863

theorem tailTrace_6057980 : CollatzResearch.WordTrace tailWord_6057980 prefixEnd_6057980 3110655535324313359089863 := by
  unfold tailWord_6057980
  simp only [CollatzResearch.WordTrace]
  refine ⟨110476341296490277729377697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147301788395320370305836929 110476341296490277729377697)
  ·
    refine ⟨82857255972367708297033273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110476341296490277729377697 82857255972367708297033273)
    ·
      refine ⟨62142941979275781222774955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82857255972367708297033273 62142941979275781222774955)
      ·
        refine ⟨93214412968913671834162433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62142941979275781222774955 93214412968913671834162433)
        ·
          refine ⟨69910809726685253875621825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93214412968913671834162433 69910809726685253875621825)
          ·
            refine ⟨52433107295013940406716369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69910809726685253875621825 52433107295013940406716369)
            ·
              refine ⟨39324830471260455305037277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52433107295013940406716369 39324830471260455305037277)
              ·
                refine ⟨14746811426722670739388979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39324830471260455305037277 14746811426722670739388979)
                ·
                  refine ⟨22120217140084006109083469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14746811426722670739388979 22120217140084006109083469)
                  ·
                    refine ⟨8295081427531502290906301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22120217140084006109083469 8295081427531502290906301)
                    ·
                      refine ⟨3110655535324313359089863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295081427531502290906301 3110655535324313359089863)
                      ·
                        rfl

theorem cell23_6057980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_6057980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6057980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6057980 prefixEnd_6057980 := by exact prefixLift 6057980
  have htrace : WordTrace (prefixWord ++ tailWord_6057980) baseStart_6057980 baseEnd_6057980 := by
    simpa [prefixWord, tailWord_6057980, baseEnd_6057980] using wordTrace_append hprefix tailTrace_6057980
  have hstable : (prefixWord ++ tailWord_6057980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6057980).length < 2 ^ (prefixWord ++ tailWord_6057980).sum := by decide
  have hdescent : baseEnd_6057980 < baseStart_6057980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6057980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058030 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6058030 : Nat := 118140960795 + 6058030 * 2 ^ 59
def prefixEnd_6058030 : Nat := 4983230072969 + 3 ^ 40 * 6058030 * 2
def baseEnd_6058030 : Nat := 1036893736452346054488211

theorem tailTrace_6058030 : CollatzResearch.WordTrace tailWord_6058030 prefixEnd_6058030 1036893736452346054488211 := by
  unfold tailWord_6058030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27619313280349926749759443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147303004161866275998717029 27619313280349926749759443)
  ·
    refine ⟨41428969920524890124639165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27619313280349926749759443 41428969920524890124639165)
    ·
      refine ⟨15535863720196833796739687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41428969920524890124639165 15535863720196833796739687)
      ·
        refine ⟨23303795580295250695109531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15535863720196833796739687 23303795580295250695109531)
        ·
          refine ⟨34955693370442876042664297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23303795580295250695109531 34955693370442876042664297)
          ·
            refine ⟨26216770027832157031998223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34955693370442876042664297 26216770027832157031998223)
            ·
              refine ⟨39325155041748235547997335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26216770027832157031998223 39325155041748235547997335)
              ·
                refine ⟨58987732562622353321996003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39325155041748235547997335 58987732562622353321996003)
                ·
                  refine ⟨88481598843933529982994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58987732562622353321996003 88481598843933529982994005)
                  ·
                    refine ⟨1036893736452346054488211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88481598843933529982994005 1036893736452346054488211)
                    ·
                      rfl

theorem cell23_6058030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6058030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058030 prefixEnd_6058030 := by exact prefixLift 6058030
  have htrace : WordTrace (prefixWord ++ tailWord_6058030) baseStart_6058030 baseEnd_6058030 := by
    simpa [prefixWord, tailWord_6058030, baseEnd_6058030] using wordTrace_append hprefix tailTrace_6058030
  have hstable : (prefixWord ++ tailWord_6058030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058030).length < 2 ^ (prefixWord ++ tailWord_6058030).sum := by decide
  have hdescent : baseEnd_6058030 < baseStart_6058030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058037 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_6058037 : Nat := 118140960795 + 6058037 * 2 ^ 59
def prefixEnd_6058037 : Nat := 4983230072969 + 3 ^ 40 * 6058037 * 2
def baseEnd_6058037 : Nat := 3110684803721619636077101

theorem tailTrace_6058037 : CollatzResearch.WordTrace tailWord_6058037 prefixEnd_6058037 3110684803721619636077101 := by
  unfold tailWord_6058037
  simp only [CollatzResearch.WordTrace]
  refine ⟨220954761553774054193580365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147303174369182702795720243 220954761553774054193580365)
  ·
    refine ⟨82858035582665270322592637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220954761553774054193580365 82858035582665270322592637)
    ·
      refine ⟨31071763343499476370972239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82858035582665270322592637 31071763343499476370972239)
      ·
        refine ⟨46607645015249214556458359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31071763343499476370972239 46607645015249214556458359)
        ·
          refine ⟨69911467522873821834687539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46607645015249214556458359 69911467522873821834687539)
          ·
            refine ⟨104867201284310732752031309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69911467522873821834687539 104867201284310732752031309)
            ·
              refine ⟨39325200481616524782011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104867201284310732752031309 39325200481616524782011741)
              ·
                refine ⟨14746950180606196793254403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39325200481616524782011741 14746950180606196793254403)
                ·
                  refine ⟨22120425270909295189881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14746950180606196793254403 22120425270909295189881605)
                  ·
                    refine ⟨4147579738295492848102801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22120425270909295189881605 4147579738295492848102801)
                    ·
                      refine ⟨3110684803721619636077101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147579738295492848102801 3110684803721619636077101)
                      ·
                        rfl

theorem cell23_6058037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_6058037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058037 prefixEnd_6058037 := by exact prefixLift 6058037
  have htrace : WordTrace (prefixWord ++ tailWord_6058037) baseStart_6058037 baseEnd_6058037 := by
    simpa [prefixWord, tailWord_6058037, baseEnd_6058037] using wordTrace_append hprefix tailTrace_6058037
  have hstable : (prefixWord ++ tailWord_6058037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058037).length < 2 ^ (prefixWord ++ tailWord_6058037).sum := by decide
  have hdescent : baseEnd_6058037 < baseStart_6058037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058043 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 7]
def baseStart_6058043 : Nat := 118140960795 + 6058043 * 2 ^ 59
def prefixEnd_6058043 : Nat := 4983230072969 + 3 ^ 40 * 6058043 * 2
def baseEnd_6058043 : Nat := 345631987178394068066897

theorem tailTrace_6058043 : CollatzResearch.WordTrace tailWord_6058043 prefixEnd_6058043 345631987178394068066897 := by
  unfold tailWord_6058043
  simp only [CollatzResearch.WordTrace]
  refine ⟨220954980391752317218298783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147303320261168211478865855 220954980391752317218298783)
  ·
    refine ⟨331432470587628475827448175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220954980391752317218298783 331432470587628475827448175)
    ·
      refine ⟨497148705881442713741172263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331432470587628475827448175 497148705881442713741172263)
      ·
        refine ⟨745723058822164070611758395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497148705881442713741172263 745723058822164070611758395)
        ·
          refine ⟨1118584588233246105917637593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745723058822164070611758395 1118584588233246105917637593)
          ·
            refine ⟨838938441174934579438228195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118584588233246105917637593 838938441174934579438228195)
            ·
              refine ⟨1258407661762401869157342293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838938441174934579438228195 1258407661762401869157342293)
              ·
                refine ⟨14746964786278146904187605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1258407661762401869157342293 14746964786278146904187605)
                ·
                  refine ⟨345631987178394068066897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14746964786278146904187605 345631987178394068066897)
                  ·
                    rfl

theorem cell23_6058043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 7].length) (baseStart_6058043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058043 prefixEnd_6058043 := by exact prefixLift 6058043
  have htrace : WordTrace (prefixWord ++ tailWord_6058043) baseStart_6058043 baseEnd_6058043 := by
    simpa [prefixWord, tailWord_6058043, baseEnd_6058043] using wordTrace_append hprefix tailTrace_6058043
  have hstable : (prefixWord ++ tailWord_6058043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058043).length < 2 ^ (prefixWord ++ tailWord_6058043).sum := by decide
  have hdescent : baseEnd_6058043 < baseStart_6058043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058053 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_6058053 : Nat := 118140960795 + 6058053 * 2 ^ 59
def prefixEnd_6058053 : Nat := 4983230072969 + 3 ^ 40 * 6058053 * 2
def baseEnd_6058053 : Nat := 3110693019412091573477027

theorem tailTrace_6058053 : CollatzResearch.WordTrace tailWord_6058053 prefixEnd_6058053 3110693019412091573477027 := by
  unfold tailWord_6058053
  simp only [CollatzResearch.WordTrace]
  refine ⟨220955345121716088926162813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147303563414477392617441875 220955345121716088926162813)
  ·
    refine ⟨82858254420643533347311055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220955345121716088926162813 82858254420643533347311055)
    ·
      refine ⟨124287381630965300020966583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82858254420643533347311055 124287381630965300020966583)
      ·
        refine ⟨186431072446447950031449875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124287381630965300020966583 186431072446447950031449875)
        ·
          refine ⟨279646608669671925047174813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186431072446447950031449875 279646608669671925047174813)
          ·
            refine ⟨104867478251126971892690555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279646608669671925047174813 104867478251126971892690555)
            ·
              refine ⟨157301217376690457839035833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104867478251126971892690555 157301217376690457839035833)
              ·
                refine ⟨117975913032517843379276875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157301217376690457839035833 117975913032517843379276875)
                ·
                  refine ⟨176963869548776765068915313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117975913032517843379276875 176963869548776765068915313)
                  ·
                    refine ⟨132722902161582573801686485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176963869548776765068915313 132722902161582573801686485)
                    ·
                      refine ⟨3110693019412091573477027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132722902161582573801686485 3110693019412091573477027)
                      ·
                        rfl

theorem cell23_6058053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_6058053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058053 prefixEnd_6058053 := by exact prefixLift 6058053
  have htrace : WordTrace (prefixWord ++ tailWord_6058053) baseStart_6058053 baseEnd_6058053 := by
    simpa [prefixWord, tailWord_6058053, baseEnd_6058053] using wordTrace_append hprefix tailTrace_6058053
  have hstable : (prefixWord ++ tailWord_6058053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058053).length < 2 ^ (prefixWord ++ tailWord_6058053).sum := by decide
  have hdescent : baseEnd_6058053 < baseStart_6058053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058077 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 7]
def baseStart_6058077 : Nat := 118140960795 + 6058077 * 2 ^ 59
def prefixEnd_6058077 : Nat := 4983230072969 + 3 ^ 40 * 6058077 * 2
def baseEnd_6058077 : Nat := 345633926994199942175213

theorem tailTrace_6058077 : CollatzResearch.WordTrace tailWord_6058077 prefixEnd_6058077 345633926994199942175213 := by
  unfold tailWord_6058077
  simp only [CollatzResearch.WordTrace]
  refine ⟨220956220473629141025036485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147304146982419427350024323 220956220473629141025036485)
  ·
    refine ⟨41429291338805463942194341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220956220473629141025036485 41429291338805463942194341)
    ·
      refine ⟨7767992126026024489161439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41429291338805463942194341 7767992126026024489161439)
      ·
        refine ⟨11651988189039036733742159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767992126026024489161439 11651988189039036733742159)
        ·
          refine ⟨17477982283558555100613239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651988189039036733742159 17477982283558555100613239)
          ·
            refine ⟨26216973425337832650919859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17477982283558555100613239 26216973425337832650919859)
            ·
              refine ⟨39325460138006748976379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26216973425337832650919859 39325460138006748976379789)
              ·
                refine ⟨14747047551752530866142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39325460138006748976379789 14747047551752530866142421)
                ·
                  refine ⟨345633926994199942175213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14747047551752530866142421 345633926994199942175213)
                  ·
                    rfl

theorem cell23_6058077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_6058077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058077 prefixEnd_6058077 := by exact prefixLift 6058077
  have htrace : WordTrace (prefixWord ++ tailWord_6058077) baseStart_6058077 baseEnd_6058077 := by
    simpa [prefixWord, tailWord_6058077, baseEnd_6058077] using wordTrace_append hprefix tailTrace_6058077
  have hstable : (prefixWord ++ tailWord_6058077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058077).length < 2 ^ (prefixWord ++ tailWord_6058077).sum := by decide
  have hdescent : baseEnd_6058077 < baseStart_6058077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058188 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_6058188 : Nat := 118140960795 + 6058188 * 2 ^ 59
def prefixEnd_6058188 : Nat := 4983230072969 + 3 ^ 40 * 6058188 * 2
def baseEnd_6058188 : Nat := 1036920779766816181762969

theorem tailTrace_6058188 : CollatzResearch.WordTrace tailWord_6058188 prefixEnd_6058188 1036920779766816181762969 := by
  unfold tailWord_6058188
  simp only [CollatzResearch.WordTrace]
  refine ⟨110480134488113503491163609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147306845984151337988218145 110480134488113503491163609)
  ·
    refine ⟨82860100866085127618372707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110480134488113503491163609 82860100866085127618372707)
    ·
      refine ⟨124290151299127691427559061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82860100866085127618372707 124290151299127691427559061)
      ·
        refine ⟨5826100842146610535666831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124290151299127691427559061 5826100842146610535666831)
        ·
          refine ⟨8739151263219915803500247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826100842146610535666831 8739151263219915803500247)
          ·
            refine ⟨13108726894829873705250371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739151263219915803500247 13108726894829873705250371)
            ·
              refine ⟨19663090342244810557875557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13108726894829873705250371 19663090342244810557875557)
              ·
                refine ⟨3686829439170901979601667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19663090342244810557875557 3686829439170901979601667)
                ·
                  refine ⟨5530244158756352969402501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686829439170901979601667 5530244158756352969402501)
                  ·
                    refine ⟨1036920779766816181762969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530244158756352969402501 1036920779766816181762969)
                    ·
                      rfl

theorem cell23_6058188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_6058188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058188 prefixEnd_6058188 := by exact prefixLift 6058188
  have htrace : WordTrace (prefixWord ++ tailWord_6058188) baseStart_6058188 baseEnd_6058188 := by
    simpa [prefixWord, tailWord_6058188, baseEnd_6058188] using wordTrace_append hprefix tailTrace_6058188
  have hstable : (prefixWord ++ tailWord_6058188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058188).length < 2 ^ (prefixWord ++ tailWord_6058188).sum := by decide
  have hdescent : baseEnd_6058188 < baseStart_6058188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058217 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 6, 2]
def baseStart_6058217 : Nat := 118140960795 + 6058217 * 2 ^ 59
def prefixEnd_6058217 : Nat := 4983230072969 + 3 ^ 40 * 6058217 * 2
def baseEnd_6058217 : Nat := 3110777230239428931826273

theorem tailTrace_6058217 : CollatzResearch.WordTrace tailWord_6058217 prefixEnd_6058217 3110777230239428931826273 := by
  unfold tailWord_6058217
  simp only [CollatzResearch.WordTrace]
  refine ⟨220961326693121944935132905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147307551128747963290088603 220961326693121944935132905)
  ·
    refine ⟨165720995019841458701349679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220961326693121944935132905 165720995019841458701349679)
    ·
      refine ⟨248581492529762188052024519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165720995019841458701349679 248581492529762188052024519)
      ·
        refine ⟨372872238794643282078036779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248581492529762188052024519 372872238794643282078036779)
        ·
          refine ⟨559308358191964923117055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372872238794643282078036779 559308358191964923117055169)
          ·
            refine ⟨419481268643973692337791377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559308358191964923117055169 419481268643973692337791377)
            ·
              refine ⟨314610951482980269253343533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419481268643973692337791377 314610951482980269253343533)
              ·
                refine ⟨117979106806117600970003825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314610951482980269253343533 117979106806117600970003825)
                ·
                  refine ⟨88484330104588200727502869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117979106806117600970003825 88484330104588200727502869)
                  ·
                    refine ⟨4147702973652571909101697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88484330104588200727502869 4147702973652571909101697)
                    ·
                      refine ⟨3110777230239428931826273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147702973652571909101697 3110777230239428931826273)
                      ·
                        rfl

theorem cell23_6058217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6, 2].length) (baseStart_6058217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058217 prefixEnd_6058217 := by exact prefixLift 6058217
  have htrace : WordTrace (prefixWord ++ tailWord_6058217) baseStart_6058217 baseEnd_6058217 := by
    simpa [prefixWord, tailWord_6058217, baseEnd_6058217] using wordTrace_append hprefix tailTrace_6058217
  have hstable : (prefixWord ++ tailWord_6058217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058217).length < 2 ^ (prefixWord ++ tailWord_6058217).sum := by decide
  have hdescent : baseEnd_6058217 < baseStart_6058217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058221 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6058221 : Nat := 118140960795 + 6058221 * 2 ^ 59
def prefixEnd_6058221 : Nat := 4983230072969 + 3 ^ 40 * 6058221 * 2
def baseEnd_6058221 : Nat := 3110779284162046916176255

theorem tailTrace_6058221 : CollatzResearch.WordTrace tailWord_6058221 prefixEnd_6058221 3110779284162046916176255 := by
  unfold tailWord_6058221
  simp only [CollatzResearch.WordTrace]
  refine ⟨220961472585107453618278517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147307648390071635745519011 220961472585107453618278517)
  ·
    refine ⟨20715138054853823776713611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220961472585107453618278517 20715138054853823776713611)
    ·
      refine ⟨31072707082280735665070417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715138054853823776713611 31072707082280735665070417)
      ·
        refine ⟨23304530311710551748802813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31072707082280735665070417 23304530311710551748802813)
        ·
          refine ⟨8739198866891456905801055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23304530311710551748802813 8739198866891456905801055)
          ·
            refine ⟨13108798300337185358701583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739198866891456905801055 13108798300337185358701583)
            ·
              refine ⟨19663197450505778038052375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13108798300337185358701583 19663197450505778038052375)
              ·
                refine ⟨29494796175758667057078563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19663197450505778038052375 29494796175758667057078563)
                ·
                  refine ⟨44242194263638000585617845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29494796175758667057078563 44242194263638000585617845)
                  ·
                    refine ⟨4147705712216062554901673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44242194263638000585617845 4147705712216062554901673)
                    ·
                      refine ⟨3110779284162046916176255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147705712216062554901673 3110779284162046916176255)
                      ·
                        rfl

theorem cell23_6058221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6058221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058221 prefixEnd_6058221 := by exact prefixLift 6058221
  have htrace : WordTrace (prefixWord ++ tailWord_6058221) baseStart_6058221 baseEnd_6058221 := by
    simpa [prefixWord, tailWord_6058221, baseEnd_6058221] using wordTrace_append hprefix tailTrace_6058221
  have hstable : (prefixWord ++ tailWord_6058221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058221).length < 2 ^ (prefixWord ++ tailWord_6058221).sum := by decide
  have hdescent : baseEnd_6058221 < baseStart_6058221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058227 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 4, 4]
def baseStart_6058227 : Nat := 118140960795 + 6058227 * 2 ^ 59
def prefixEnd_6058227 : Nat := 4983230072969 + 3 ^ 40 * 6058227 * 2
def baseEnd_6058227 : Nat := 1036927455015324630900409

theorem tailTrace_6058227 : CollatzResearch.WordTrace tailWord_6058227 prefixEnd_6058227 1036927455015324630900409 := by
  unfold tailWord_6058227
  simp only [CollatzResearch.WordTrace]
  refine ⟨220961691423085716642996935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147307794282057144428664623 220961691423085716642996935)
  ·
    refine ⟨331442537134628574964495403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220961691423085716642996935 331442537134628574964495403)
    ·
      refine ⟨497163805701942862446743105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331442537134628574964495403 497163805701942862446743105)
      ·
        refine ⟨372872854276457146835057329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497163805701942862446743105 372872854276457146835057329)
        ·
          refine ⟨279654640707342860126292997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372872854276457146835057329 279654640707342860126292997)
          ·
            refine ⟨52435245132626786273679937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279654640707342860126292997 52435245132626786273679937)
            ·
              refine ⟨39326433849470089705259953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52435245132626786273679937 39326433849470089705259953)
              ·
                refine ⟨29494825387102567278944965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39326433849470089705259953 29494825387102567278944965)
                ·
                  refine ⟨5530279760081731364802181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29494825387102567278944965 5530279760081731364802181)
                  ·
                    refine ⟨1036927455015324630900409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5530279760081731364802181 1036927455015324630900409)
                    ·
                      rfl

theorem cell23_6058227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 4].length) (baseStart_6058227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058227 prefixEnd_6058227 := by exact prefixLift 6058227
  have htrace : WordTrace (prefixWord ++ tailWord_6058227) baseStart_6058227 baseEnd_6058227 := by
    simpa [prefixWord, tailWord_6058227, baseEnd_6058227] using wordTrace_append hprefix tailTrace_6058227
  have hstable : (prefixWord ++ tailWord_6058227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058227).length < 2 ^ (prefixWord ++ tailWord_6058227).sum := by decide
  have hdescent : baseEnd_6058227 < baseStart_6058227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058234 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_6058234 : Nat := 118140960795 + 6058234 * 2 ^ 59
def prefixEnd_6058234 : Nat := 4983230072969 + 3 ^ 40 * 6058234 * 2
def baseEnd_6058234 : Nat := 3110785959410555365313695

theorem tailTrace_6058234 : CollatzResearch.WordTrace tailWord_6058234 prefixEnd_6058234 3110785959410555365313695 := by
  unfold tailWord_6058234
  simp only [CollatzResearch.WordTrace]
  refine ⟨55240486683515089209625439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147307964489373571225667837 55240486683515089209625439)
  ·
    refine ⟨82860730025272633814438159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55240486683515089209625439 82860730025272633814438159)
    ·
      refine ⟨124291095037908950721657239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82860730025272633814438159 124291095037908950721657239)
      ·
        refine ⟨186436642556863426082485859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124291095037908950721657239 186436642556863426082485859)
        ·
          refine ⟨279654963835295139123728789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186436642556863426082485859 279654963835295139123728789)
          ·
            refine ⟨13108826429779459646424787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 279654963835295139123728789 13108826429779459646424787)
            ·
              refine ⟨19663239644669189469637181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13108826429779459646424787 19663239644669189469637181)
              ·
                refine ⟨7373714866750946051113943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19663239644669189469637181 7373714866750946051113943)
                ·
                  refine ⟨11060572300126419076670915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373714866750946051113943 11060572300126419076670915)
                  ·
                    refine ⟨16590858450189628615006373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11060572300126419076670915 16590858450189628615006373)
                    ·
                      refine ⟨3110785959410555365313695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16590858450189628615006373 3110785959410555365313695)
                      ·
                        rfl

theorem cell23_6058234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_6058234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058234 prefixEnd_6058234 := by exact prefixLift 6058234
  have htrace : WordTrace (prefixWord ++ tailWord_6058234) baseStart_6058234 baseEnd_6058234 := by
    simpa [prefixWord, tailWord_6058234, baseEnd_6058234] using wordTrace_append hprefix tailTrace_6058234
  have hstable : (prefixWord ++ tailWord_6058234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058234).length < 2 ^ (prefixWord ++ tailWord_6058234).sum := by decide
  have hdescent : baseEnd_6058234 < baseStart_6058234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058251 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 3, 2, 2]
def baseStart_6058251 : Nat := 118140960795 + 6058251 * 2 ^ 59
def prefixEnd_6058251 : Nat := 4983230072969 + 3 ^ 40 * 6058251 * 2
def baseEnd_6058251 : Nat := 3110794688581681798801117

theorem tailTrace_6058251 : CollatzResearch.WordTrace tailWord_6058251 prefixEnd_6058251 3110794688581681798801117 := by
  unfold tailWord_6058251
  simp only [CollatzResearch.WordTrace]
  refine ⟨220962566774998768741870607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147308377849999179161247071 220962566774998768741870607)
  ·
    refine ⟨331443850162498153112805911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220962566774998768741870607 331443850162498153112805911)
    ·
      refine ⟨497165775243747229669208867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331443850162498153112805911 497165775243747229669208867)
      ·
        refine ⟨745748662865620844503813301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497165775243747229669208867 745748662865620844503813301)
        ·
          refine ⟨69913937143651954172232497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 745748662865620844503813301 69913937143651954172232497)
          ·
            refine ⟨52435452857738965629174373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69913937143651954172232497 52435452857738965629174373)
            ·
              refine ⟨9831647410826056055470195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52435452857738965629174373 9831647410826056055470195)
              ·
                refine ⟨14747471116239084083205293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9831647410826056055470195 14747471116239084083205293)
                ·
                  refine ⟨5530301668589656531201985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14747471116239084083205293 5530301668589656531201985)
                  ·
                    refine ⟨4147726251442242398401489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530301668589656531201985 4147726251442242398401489)
                    ·
                      refine ⟨3110794688581681798801117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147726251442242398401489 3110794688581681798801117)
                      ·
                        rfl

theorem cell23_6058251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2, 2].length) (baseStart_6058251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058251 prefixEnd_6058251 := by exact prefixLift 6058251
  have htrace : WordTrace (prefixWord ++ tailWord_6058251) baseStart_6058251 baseEnd_6058251 := by
    simpa [prefixWord, tailWord_6058251, baseEnd_6058251] using wordTrace_append hprefix tailTrace_6058251
  have hstable : (prefixWord ++ tailWord_6058251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058251).length < 2 ^ (prefixWord ++ tailWord_6058251).sum := by decide
  have hdescent : baseEnd_6058251 < baseStart_6058251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058271 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_6058271 : Nat := 118140960795 + 6058271 * 2 ^ 59
def prefixEnd_6058271 : Nat := 4983230072969 + 3 ^ 40 * 6058271 * 2
def baseEnd_6058271 : Nat := 3110804958194771720551025

theorem tailTrace_6058271 : CollatzResearch.WordTrace tailWord_6058271 prefixEnd_6058271 3110804958194771720551025 := by
  unfold tailWord_6058271
  simp only [CollatzResearch.WordTrace]
  refine ⟨220963296234926312157598667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147308864156617541438399111 220963296234926312157598667)
  ·
    refine ⟨331444944352389468236398001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220963296234926312157598667 331444944352389468236398001)
    ·
      refine ⟨248583708264292101177298501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331444944352389468236398001 248583708264292101177298501)
      ·
        refine ⟨46609445299554768970743469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248583708264292101177298501 46609445299554768970743469)
        ·
          refine ⟨17478541987333038364028801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46609445299554768970743469 17478541987333038364028801)
          ·
            refine ⟨13108906490499778773021601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17478541987333038364028801 13108906490499778773021601)
            ·
              refine ⟨9831679867874834079766201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13108906490499778773021601 9831679867874834079766201)
              ·
                refine ⟨7373759900906125559824651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9831679867874834079766201 7373759900906125559824651)
                ·
                  refine ⟨11060639851359188339736977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7373759900906125559824651 11060639851359188339736977)
                  ·
                    refine ⟨8295479888519391254802733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11060639851359188339736977 8295479888519391254802733)
                    ·
                      refine ⟨3110804958194771720551025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295479888519391254802733 3110804958194771720551025)
                      ·
                        rfl

theorem cell23_6058271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_6058271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058271 prefixEnd_6058271 := by exact prefixLift 6058271
  have htrace : WordTrace (prefixWord ++ tailWord_6058271) baseStart_6058271 baseEnd_6058271 := by
    simpa [prefixWord, tailWord_6058271, baseEnd_6058271] using wordTrace_append hprefix tailTrace_6058271
  have hstable : (prefixWord ++ tailWord_6058271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058271).length < 2 ^ (prefixWord ++ tailWord_6058271).sum := by decide
  have hdescent : baseEnd_6058271 < baseStart_6058271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058274 : List Nat := [3, 3, 1, 1, 3, 1, 4, 7]
def baseStart_6058274 : Nat := 118140960795 + 6058274 * 2 ^ 59
def prefixEnd_6058274 : Nat := 4983230072969 + 3 ^ 40 * 6058274 * 2
def baseEnd_6058274 : Nat := 115215055505064266993093

theorem tailTrace_6058274 : CollatzResearch.WordTrace tailWord_6058274 prefixEnd_6058274 115215055505064266993093 := by
  unfold tailWord_6058274
  simp only [CollatzResearch.WordTrace]
  refine ⟨55240851413478860917489469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147308937102610295779971917 55240851413478860917489469)
  ·
    refine ⟨20715319280054572844058551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55240851413478860917489469 20715319280054572844058551)
    ·
      refine ⟨31072978920081859266087827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715319280054572844058551 31072978920081859266087827)
      ·
        refine ⟨46609468380122788899131741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31072978920081859266087827 46609468380122788899131741)
        ·
          refine ⟨17478550642546045837174403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46609468380122788899131741 17478550642546045837174403)
          ·
            refine ⟨26217825963819068755761605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17478550642546045837174403 26217825963819068755761605)
            ·
              refine ⟨4915842368216075391705301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26217825963819068755761605 4915842368216075391705301)
              ·
                refine ⟨115215055505064266993093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4915842368216075391705301 115215055505064266993093)
                ·
                  rfl

theorem cell23_6058274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_6058274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058274 prefixEnd_6058274 := by exact prefixLift 6058274
  have htrace : WordTrace (prefixWord ++ tailWord_6058274) baseStart_6058274 baseEnd_6058274 := by
    simpa [prefixWord, tailWord_6058274, baseEnd_6058274] using wordTrace_append hprefix tailTrace_6058274
  have hstable : (prefixWord ++ tailWord_6058274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058274).length < 2 ^ (prefixWord ++ tailWord_6058274).sum := by decide
  have hdescent : baseEnd_6058274 < baseStart_6058274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058279 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6058279 : Nat := 118140960795 + 6058279 * 2 ^ 59
def prefixEnd_6058279 : Nat := 4983230072969 + 3 ^ 40 * 6058279 * 2
def baseEnd_6058279 : Nat := 3110809066040007689250989

theorem tailTrace_6058279 : CollatzResearch.WordTrace tailWord_6058279 prefixEnd_6058279 3110809066040007689250989 := by
  unfold tailWord_6058279
  simp only [CollatzResearch.WordTrace]
  refine ⟨220963588018897329523889891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147309058679264886349259927 220963588018897329523889891)
  ·
    refine ⟨331445382028345994285834837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220963588018897329523889891 331445382028345994285834837)
    ·
      refine ⟨3884125570644679620537127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 331445382028345994285834837 3884125570644679620537127)
      ·
        refine ⟨5826188355967019430805691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884125570644679620537127 5826188355967019430805691)
        ·
          refine ⟨8739282533950529146208537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826188355967019430805691 8739282533950529146208537)
          ·
            refine ⟨6554461900462896859656403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8739282533950529146208537 6554461900462896859656403)
            ·
              refine ⟨9831692850694345289484605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554461900462896859656403 9831692850694345289484605)
              ·
                refine ⟨3686884819010379483556727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9831692850694345289484605 3686884819010379483556727)
                ·
                  refine ⟨5530327228515569225335091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686884819010379483556727 5530327228515569225335091)
                  ·
                    refine ⟨8295490842773353838002637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530327228515569225335091 8295490842773353838002637)
                    ·
                      refine ⟨3110809066040007689250989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295490842773353838002637 3110809066040007689250989)
                      ·
                        rfl

theorem cell23_6058279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6058279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058279 prefixEnd_6058279 := by exact prefixLift 6058279
  have htrace : WordTrace (prefixWord ++ tailWord_6058279) baseStart_6058279 baseEnd_6058279 := by
    simpa [prefixWord, tailWord_6058279, baseEnd_6058279] using wordTrace_append hprefix tailTrace_6058279
  have hstable : (prefixWord ++ tailWord_6058279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058279).length < 2 ^ (prefixWord ++ tailWord_6058279).sum := by decide
  have hdescent : baseEnd_6058279 < baseStart_6058279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058284 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 3]
def baseStart_6058284 : Nat := 118140960795 + 6058284 * 2 ^ 59
def prefixEnd_6058284 : Nat := 4983230072969 + 3 ^ 40 * 6058284 * 2
def baseEnd_6058284 : Nat := 3110811633443280169688465

theorem tailTrace_6058284 : CollatzResearch.WordTrace tailWord_6058284 prefixEnd_6058284 3110811633443280169688465 := by
  unfold tailWord_6058284
  simp only [CollatzResearch.WordTrace]
  refine ⟨110481885191939607688910953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147309180255919476918547937 110481885191939607688910953)
  ·
    refine ⟨82861413893954705766683215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110481885191939607688910953 82861413893954705766683215)
    ·
      refine ⟨124292120840932058650024823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82861413893954705766683215 124292120840932058650024823)
      ·
        refine ⟨186438181261398087975037235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124292120840932058650024823 186438181261398087975037235)
        ·
          refine ⟨279657271892097131962555853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186438181261398087975037235 279657271892097131962555853)
          ·
            refine ⟨104871476959536424485958445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279657271892097131962555853 104871476959536424485958445)
            ·
              refine ⟨39326803859826159182234417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104871476959536424485958445 39326803859826159182234417)
              ·
                refine ⟨29495102894869619386675813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39326803859826159182234417 29495102894869619386675813)
                ·
                  refine ⟨5530331792788053635001715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29495102894869619386675813 5530331792788053635001715)
                  ·
                    refine ⟨8295497689182080452502573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530331792788053635001715 8295497689182080452502573)
                    ·
                      refine ⟨3110811633443280169688465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295497689182080452502573 3110811633443280169688465)
                      ·
                        rfl

theorem cell23_6058284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_6058284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058284 prefixEnd_6058284 := by exact prefixLift 6058284
  have htrace : WordTrace (prefixWord ++ tailWord_6058284) baseStart_6058284 baseEnd_6058284 := by
    simpa [prefixWord, tailWord_6058284, baseEnd_6058284] using wordTrace_append hprefix tailTrace_6058284
  have hstable : (prefixWord ++ tailWord_6058284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058284).length < 2 ^ (prefixWord ++ tailWord_6058284).sum := by decide
  have hdescent : baseEnd_6058284 < baseStart_6058284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058302 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6058302 : Nat := 118140960795 + 6058302 * 2 ^ 59
def prefixEnd_6058302 : Nat := 4983230072969 + 3 ^ 40 * 6058302 * 2
def baseEnd_6058302 : Nat := 3110820876095061099263383

theorem tailTrace_6058302 : CollatzResearch.WordTrace tailWord_6058302 prefixEnd_6058302 3110820876095061099263383 := by
  unfold tailWord_6058302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620553362226750556497145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147309617931876002967984773 27620553362226750556497145)
  ·
    refine ⟨20715415021670062917372859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27620553362226750556497145 20715415021670062917372859)
    ·
      refine ⟨31073122532505094376059289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715415021670062917372859 31073122532505094376059289)
      ·
        refine ⟨23304841899378820782044467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31073122532505094376059289 23304841899378820782044467)
        ·
          refine ⟨34957262849068231173066701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23304841899378820782044467 34957262849068231173066701)
          ·
            refine ⟨13108973568400586689900013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34957262849068231173066701 13108973568400586689900013)
            ·
              refine ⟨4915865088150220008712505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13108973568400586689900013 4915865088150220008712505)
              ·
                refine ⟨3686898816112665006534379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915865088150220008712505 3686898816112665006534379)
                ·
                  refine ⟨5530348224168997509801569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686898816112665006534379 5530348224168997509801569)
                  ·
                    refine ⟨4147761168126748132351177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530348224168997509801569 4147761168126748132351177)
                    ·
                      refine ⟨3110820876095061099263383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147761168126748132351177 3110820876095061099263383)
                      ·
                        rfl

theorem cell23_6058302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6058302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058302 prefixEnd_6058302 := by exact prefixLift 6058302
  have htrace : WordTrace (prefixWord ++ tailWord_6058302) baseStart_6058302 baseEnd_6058302 := by
    simpa [prefixWord, tailWord_6058302, baseEnd_6058302] using wordTrace_append hprefix tailTrace_6058302
  have hstable : (prefixWord ++ tailWord_6058302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058302).length < 2 ^ (prefixWord ++ tailWord_6058302).sum := by decide
  have hdescent : baseEnd_6058302 < baseStart_6058302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058327 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_6058327 : Nat := 118140960795 + 6058327 * 2 ^ 59
def prefixEnd_6058327 : Nat := 4983230072969 + 3 ^ 40 * 6058327 * 2
def baseEnd_6058327 : Nat := 3110833713111423501450767

theorem tailTrace_6058327 : CollatzResearch.WordTrace tailWord_6058327 prefixEnd_6058327 3110833713111423501450767 := by
  unfold tailWord_6058327
  simp only [CollatzResearch.WordTrace]
  refine ⟨220965338722723433721637235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147310225815148955814424823 220965338722723433721637235)
  ·
    refine ⟨331448008084085150582455853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220965338722723433721637235 331448008084085150582455853)
    ·
      refine ⟨124293003031531931468420945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331448008084085150582455853 124293003031531931468420945)
      ·
        refine ⟨93219752273648948601315709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124293003031531931468420945 93219752273648948601315709)
        ·
          refine ⟨34957407102618355725493391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93219752273648948601315709 34957407102618355725493391)
          ·
            refine ⟨52436110653927533588240087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34957407102618355725493391 52436110653927533588240087)
            ·
              refine ⟨78654165980891300382360131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52436110653927533588240087 78654165980891300382360131)
              ·
                refine ⟨117981248971336950573540197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78654165980891300382360131 117981248971336950573540197)
                ·
                  refine ⟨22121484182125678232538787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117981248971336950573540197 22121484182125678232538787)
                  ·
                    refine ⟨33182226273188517348808181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22121484182125678232538787 33182226273188517348808181)
                    ·
                      refine ⟨3110833713111423501450767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33182226273188517348808181 3110833713111423501450767)
                      ·
                        rfl

theorem cell23_6058327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_6058327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058327 prefixEnd_6058327 := by exact prefixLift 6058327
  have htrace : WordTrace (prefixWord ++ tailWord_6058327) baseStart_6058327 baseEnd_6058327 := by
    simpa [prefixWord, tailWord_6058327, baseEnd_6058327] using wordTrace_append hprefix tailTrace_6058327
  have hstable : (prefixWord ++ tailWord_6058327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058327).length < 2 ^ (prefixWord ++ tailWord_6058327).sum := by decide
  have hdescent : baseEnd_6058327 < baseStart_6058327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058337 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6058337 : Nat := 118140960795 + 6058337 * 2 ^ 59
def prefixEnd_6058337 : Nat := 4983230072969 + 3 ^ 40 * 6058337 * 2
def baseEnd_6058337 : Nat := 3110838847917968462325721

theorem tailTrace_6058337 : CollatzResearch.WordTrace tailWord_6058337 prefixEnd_6058337 3110838847917968462325721 := by
  unfold tailWord_6058337
  simp only [CollatzResearch.WordTrace]
  refine ⟨220965703452687205429501265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147310468968458136953000843 220965703452687205429501265)
  ·
    refine ⟨165724277589515404072125949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220965703452687205429501265 165724277589515404072125949)
    ·
      refine ⟨62146604096068276527047231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165724277589515404072125949 62146604096068276527047231)
      ·
        refine ⟨93219906144102414790570847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62146604096068276527047231 93219906144102414790570847)
        ·
          refine ⟨139829859216153622185856271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93219906144102414790570847 139829859216153622185856271)
          ·
            refine ⟨209744788824230433278784407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139829859216153622185856271 209744788824230433278784407)
            ·
              refine ⟨314617183236345649918176611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209744788824230433278784407 314617183236345649918176611)
              ·
                refine ⟨471925774854518474877264917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314617183236345649918176611 471925774854518474877264917)
                ·
                  refine ⟨22121520696305553509871793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 471925774854518474877264917 22121520696305553509871793)
                  ·
                    refine ⟨16591140522229165132403845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22121520696305553509871793 16591140522229165132403845)
                    ·
                      refine ⟨3110838847917968462325721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16591140522229165132403845 3110838847917968462325721)
                      ·
                        rfl

theorem cell23_6058337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6058337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058337 prefixEnd_6058337 := by exact prefixLift 6058337
  have htrace : WordTrace (prefixWord ++ tailWord_6058337) baseStart_6058337 baseEnd_6058337 := by
    simpa [prefixWord, tailWord_6058337, baseEnd_6058337] using wordTrace_append hprefix tailTrace_6058337
  have hstable : (prefixWord ++ tailWord_6058337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058337).length < 2 ^ (prefixWord ++ tailWord_6058337).sum := by decide
  have hdescent : baseEnd_6058337 < baseStart_6058337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058341 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_6058341 : Nat := 118140960795 + 6058341 * 2 ^ 59
def prefixEnd_6058341 : Nat := 4983230072969 + 3 ^ 40 * 6058341 * 2
def baseEnd_6058341 : Nat := 3110840901840586446675703

theorem tailTrace_6058341 : CollatzResearch.WordTrace tailWord_6058341 prefixEnd_6058341 3110840901840586446675703 := by
  unfold tailWord_6058341
  simp only [CollatzResearch.WordTrace]
  refine ⟨220965849344672714112646877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147310566229781809408431251 220965849344672714112646877)
  ·
    refine ⟨82862193504252267792242579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220965849344672714112646877 82862193504252267792242579)
    ·
      refine ⟨124293290256378401688363869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82862193504252267792242579 124293290256378401688363869)
      ·
        refine ⟨46609983846141900633136451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124293290256378401688363869 46609983846141900633136451)
        ·
          refine ⟨69914975769212850949704677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46609983846141900633136451 69914975769212850949704677)
          ·
            refine ⟨13109057956727409553069627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69914975769212850949704677 13109057956727409553069627)
            ·
              refine ⟨19663586935091114329604441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109057956727409553069627 19663586935091114329604441)
              ·
                refine ⟨14747690201318335747203331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19663586935091114329604441 14747690201318335747203331)
                ·
                  refine ⟨22121535301977503620804997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14747690201318335747203331 22121535301977503620804997)
                  ·
                    refine ⟨4147787869120781928900937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22121535301977503620804997 4147787869120781928900937)
                    ·
                      refine ⟨3110840901840586446675703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147787869120781928900937 3110840901840586446675703)
                      ·
                        rfl

theorem cell23_6058341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_6058341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058341 prefixEnd_6058341 := by exact prefixLift 6058341
  have htrace : WordTrace (prefixWord ++ tailWord_6058341) baseStart_6058341 baseEnd_6058341 := by
    simpa [prefixWord, tailWord_6058341, baseEnd_6058341] using wordTrace_append hprefix tailTrace_6058341
  have hstable : (prefixWord ++ tailWord_6058341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058341).length < 2 ^ (prefixWord ++ tailWord_6058341).sum := by decide
  have hdescent : baseEnd_6058341 < baseStart_6058341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058344 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6058344 : Nat := 118140960795 + 6058344 * 2 ^ 59
def prefixEnd_6058344 : Nat := 4983230072969 + 3 ^ 40 * 6058344 * 2
def baseEnd_6058344 : Nat := 3110842442282549934938189

theorem tailTrace_6058344 : CollatzResearch.WordTrace tailWord_6058344 prefixEnd_6058344 3110842442282549934938189 := by
  unfold tailWord_6058344
  simp only [CollatzResearch.WordTrace]
  refine ⟨110482979381830922812503043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147310639175774563750004057 110482979381830922812503043)
  ·
    refine ⟨165724469072746384218754565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110482979381830922812503043 165724469072746384218754565)
    ·
      refine ⟨31073337951139947041016481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165724469072746384218754565 31073337951139947041016481)
      ·
        refine ⟨23305003463354960280762361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31073337951139947041016481 23305003463354960280762361)
        ·
          refine ⟨17478752597516220210571771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23305003463354960280762361 17478752597516220210571771)
          ·
            refine ⟨26218128896274330315857657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17478752597516220210571771 26218128896274330315857657)
            ·
              refine ⟨19663596672205747736893243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26218128896274330315857657 19663596672205747736893243)
              ·
                refine ⟨29495395008308621605339865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19663596672205747736893243 29495395008308621605339865)
                ·
                  refine ⟨22121546256231466204004899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29495395008308621605339865 22121546256231466204004899)
                  ·
                    refine ⟨33182319384347199306007349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22121546256231466204004899 33182319384347199306007349)
                    ·
                      refine ⟨3110842442282549934938189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33182319384347199306007349 3110842442282549934938189)
                      ·
                        rfl

theorem cell23_6058344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6058344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058344 prefixEnd_6058344 := by exact prefixLift 6058344
  have htrace : WordTrace (prefixWord ++ tailWord_6058344) baseStart_6058344 baseEnd_6058344 := by
    simpa [prefixWord, tailWord_6058344, baseEnd_6058344] using wordTrace_append hprefix tailTrace_6058344
  have hstable : (prefixWord ++ tailWord_6058344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058344).length < 2 ^ (prefixWord ++ tailWord_6058344).sum := by decide
  have hdescent : baseEnd_6058344 < baseStart_6058344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058394 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_6058394 : Nat := 118140960795 + 6058394 * 2 ^ 59
def prefixEnd_6058394 : Nat := 4983230072969 + 3 ^ 40 * 6058394 * 2
def baseEnd_6058394 : Nat := 1036956038771758246437653

theorem tailTrace_6058394 : CollatzResearch.WordTrace tailWord_6058394 prefixEnd_6058394 1036956038771758246437653 := by
  unfold tailWord_6058394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55241945603370176041081559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147311854942320469442884157 55241945603370176041081559)
  ·
    refine ⟨82862918405055264061622339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55241945603370176041081559 82862918405055264061622339)
    ·
      refine ⟨124294377607582896092433509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82862918405055264061622339 124294377607582896092433509)
      ·
        refine ⟨23305195801421793017331283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124294377607582896092433509 23305195801421793017331283)
        ·
          refine ⟨34957793702132689525996925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23305195801421793017331283 34957793702132689525996925)
          ·
            refine ⟨13109172638299758572248847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34957793702132689525996925 13109172638299758572248847)
            ·
              refine ⟨19663758957449637858373271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109172638299758572248847 19663758957449637858373271)
              ·
                refine ⟨29495638436174456787559907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19663758957449637858373271 29495638436174456787559907)
                ·
                  refine ⟨44243457654261685181339861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29495638436174456787559907 44243457654261685181339861)
                  ·
                    refine ⟨1036956038771758246437653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44243457654261685181339861 1036956038771758246437653)
                    ·
                      rfl

theorem cell23_6058394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_6058394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058394 prefixEnd_6058394 := by exact prefixLift 6058394
  have htrace : WordTrace (prefixWord ++ tailWord_6058394) baseStart_6058394 baseEnd_6058394 := by
    simpa [prefixWord, tailWord_6058394, baseEnd_6058394] using wordTrace_append hprefix tailTrace_6058394
  have hstable : (prefixWord ++ tailWord_6058394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058394).length < 2 ^ (prefixWord ++ tailWord_6058394).sum := by decide
  have hdescent : baseEnd_6058394 < baseStart_6058394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058398 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_6058398 : Nat := 118140960795 + 6058398 * 2 ^ 59
def prefixEnd_6058398 : Nat := 4983230072969 + 3 ^ 40 * 6058398 * 2
def baseEnd_6058398 : Nat := 345652241137543635962549

theorem tailTrace_6058398 : CollatzResearch.WordTrace tailWord_6058398 prefixEnd_6058398 345652241137543635962549 := by
  unfold tailWord_6058398
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620991038183276605933981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147311952203644141898314565 27620991038183276605933981)
  ·
    refine ⟨10357871639318728727225243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27620991038183276605933981 10357871639318728727225243)
    ·
      refine ⟨15536807458978093090837865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357871639318728727225243 15536807458978093090837865)
      ·
        refine ⟨11652605594233569818128399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15536807458978093090837865 11652605594233569818128399)
        ·
          refine ⟨17478908391350354727192599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11652605594233569818128399 17478908391350354727192599)
          ·
            refine ⟨26218362587025532090788899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17478908391350354727192599 26218362587025532090788899)
            ·
              refine ⟨39327543880538298136183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26218362587025532090788899 39327543880538298136183349)
              ·
                refine ⟨3686957238800465450267189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39327543880538298136183349 3686957238800465450267189)
                ·
                  refine ⟨345652241137543635962549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3686957238800465450267189 345652241137543635962549)
                  ·
                    rfl

theorem cell23_6058398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_6058398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058398 prefixEnd_6058398 := by exact prefixLift 6058398
  have htrace : WordTrace (prefixWord ++ tailWord_6058398) baseStart_6058398 baseEnd_6058398 := by
    simpa [prefixWord, tailWord_6058398, baseEnd_6058398] using wordTrace_append hprefix tailTrace_6058398
  have hstable : (prefixWord ++ tailWord_6058398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058398).length < 2 ^ (prefixWord ++ tailWord_6058398).sum := by decide
  have hdescent : baseEnd_6058398 < baseStart_6058398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058501 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_6058501 : Nat := 118140960795 + 6058501 * 2 ^ 59
def prefixEnd_6058501 : Nat := 4983230072969 + 3 ^ 40 * 6058501 * 2
def baseEnd_6058501 : Nat := 1036974352915101940224989

theorem tailTrace_6058501 : CollatzResearch.WordTrace tailWord_6058501 prefixEnd_6058501 1036974352915101940224989 := by
  unfold tailWord_6058501
  simp only [CollatzResearch.WordTrace]
  refine ⟨220971685024093061438471357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147314456682728707625647571 220971685024093061438471357)
  ·
    refine ⟨82864381884034898039426759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220971685024093061438471357 82864381884034898039426759)
    ·
      refine ⟨124296572826052347059140139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82864381884034898039426759 124296572826052347059140139)
      ·
        refine ⟨186444859239078520588710209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124296572826052347059140139 186444859239078520588710209)
        ·
          refine ⟨139833644429308890441532657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186444859239078520588710209 139833644429308890441532657)
          ·
            refine ⟨104875233321981667831149493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139833644429308890441532657 104875233321981667831149493)
            ·
              refine ⟨9832053123935781359170265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104875233321981667831149493 9832053123935781359170265)
              ·
                refine ⟨7374039842951836019377699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9832053123935781359170265 7374039842951836019377699)
                ·
                  refine ⟨11061059764427754029066549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374039842951836019377699 11061059764427754029066549)
                  ·
                    refine ⟨1036974352915101940224989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11061059764427754029066549 1036974352915101940224989)
                    ·
                      rfl

theorem cell23_6058501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_6058501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058501 prefixEnd_6058501 := by exact prefixLift 6058501
  have htrace : WordTrace (prefixWord ++ tailWord_6058501) baseStart_6058501 baseEnd_6058501 := by
    simpa [prefixWord, tailWord_6058501, baseEnd_6058501] using wordTrace_append hprefix tailTrace_6058501
  have hstable : (prefixWord ++ tailWord_6058501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058501).length < 2 ^ (prefixWord ++ tailWord_6058501).sum := by decide
  have hdescent : baseEnd_6058501 < baseStart_6058501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058502 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6058502 : Nat := 118140960795 + 6058502 * 2 ^ 59
def prefixEnd_6058502 : Nat := 4983230072969 + 3 ^ 40 * 6058502 * 2
def baseEnd_6058502 : Nat := 3110923572225960316762463

theorem tailTrace_6058502 : CollatzResearch.WordTrace tailWord_6058502 prefixEnd_6058502 3110923572225960316762463 := by
  unfold tailWord_6058502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905366296784044956539305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147314480998059625739505173 6905366296784044956539305)
  ·
    refine ⟨5179024722588033717404479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6905366296784044956539305 5179024722588033717404479)
    ·
      refine ⟨7768537083882050576106719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179024722588033717404479 7768537083882050576106719)
      ·
        refine ⟨11652805625823075864160079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7768537083882050576106719 11652805625823075864160079)
        ·
          refine ⟨17479208438734613796240119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11652805625823075864160079 17479208438734613796240119)
          ·
            refine ⟨26218812658101920694360179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17479208438734613796240119 26218812658101920694360179)
            ·
              refine ⟨39328218987152881041540269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26218812658101920694360179 39328218987152881041540269)
              ·
                refine ⟨14748082120182330390577601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39328218987152881041540269 14748082120182330390577601)
                ·
                  refine ⟨11061061590136747792933201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748082120182330390577601 11061061590136747792933201)
                  ·
                    refine ⟨8295796192602560844699901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11061061590136747792933201 8295796192602560844699901)
                    ·
                      refine ⟨3110923572225960316762463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295796192602560844699901 3110923572225960316762463)
                      ·
                        rfl

theorem cell23_6058502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6058502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058502 prefixEnd_6058502 := by exact prefixLift 6058502
  have htrace : WordTrace (prefixWord ++ tailWord_6058502) baseStart_6058502 baseEnd_6058502 := by
    simpa [prefixWord, tailWord_6058502, baseEnd_6058502] using wordTrace_append hprefix tailTrace_6058502
  have hstable : (prefixWord ++ tailWord_6058502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058502).length < 2 ^ (prefixWord ++ tailWord_6058502).sum := by decide
  have hdescent : baseEnd_6058502 < baseStart_6058502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058508 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 2, 3, 2]
def baseStart_6058508 : Nat := 118140960795 + 6058508 * 2 ^ 59
def prefixEnd_6058508 : Nat := 4983230072969 + 3 ^ 40 * 6058508 * 2
def baseEnd_6058508 : Nat := 3110926653109887293287435

theorem tailTrace_6058508 : CollatzResearch.WordTrace tailWord_6058508 prefixEnd_6058508 3110926653109887293287435 := by
  unfold tailWord_6058508
  simp only [CollatzResearch.WordTrace]
  refine ⟨110485970167533850816988089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147314626890045134422650785 110485970167533850816988089)
  ·
    refine ⟨82864477625650388112741067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110485970167533850816988089 82864477625650388112741067)
    ·
      refine ⟨124296716438475582169111601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82864477625650388112741067 124296716438475582169111601)
      ·
        refine ⟨93222537328856686626833701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124296716438475582169111601 93222537328856686626833701)
        ·
          refine ⟨17479225749160628742531319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93222537328856686626833701 17479225749160628742531319)
          ·
            refine ⟨26218838623740943113796979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17479225749160628742531319 26218838623740943113796979)
            ·
              refine ⟨39328257935611414670695469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26218838623740943113796979 39328257935611414670695469)
              ·
                refine ⟨14748096725854280501510801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39328257935611414670695469 14748096725854280501510801)
                ·
                  refine ⟨11061072544390710376133101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748096725854280501510801 11061072544390710376133101)
                  ·
                    refine ⟨4147902204146516391049913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11061072544390710376133101 4147902204146516391049913)
                    ·
                      refine ⟨3110926653109887293287435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147902204146516391049913 3110926653109887293287435)
                      ·
                        rfl

theorem cell23_6058508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_6058508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058508 prefixEnd_6058508 := by exact prefixLift 6058508
  have htrace : WordTrace (prefixWord ++ tailWord_6058508) baseStart_6058508 baseEnd_6058508 := by
    simpa [prefixWord, tailWord_6058508, baseEnd_6058508] using wordTrace_append hprefix tailTrace_6058508
  have hstable : (prefixWord ++ tailWord_6058508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058508).length < 2 ^ (prefixWord ++ tailWord_6058508).sum := by decide
  have hdescent : baseEnd_6058508 < baseStart_6058508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058544 : List Nat := [2, 1, 1, 1, 2, 3, 5, 8]
def baseStart_6058544 : Nat := 118140960795 + 6058544 * 2 ^ 59
def prefixEnd_6058544 : Nat := 4983230072969 + 3 ^ 40 * 6058544 * 2
def baseEnd_6058544 : Nat := 115220190311609227868047

theorem tailTrace_6058544 : CollatzResearch.WordTrace tailWord_6058544 prefixEnd_6058544 115220190311609227868047 := by
  unfold tailWord_6058544
  simp only [CollatzResearch.WordTrace]
  refine ⟨110486626681468639891143343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147315502241958186521524457 110486626681468639891143343)
  ·
    refine ⟨165729940022202959836715015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110486626681468639891143343 165729940022202959836715015)
    ·
      refine ⟨248594910033304439755072523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165729940022202959836715015 248594910033304439755072523)
      ·
        refine ⟨372892365049956659632608785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248594910033304439755072523 372892365049956659632608785)
        ·
          refine ⟨279669273787467494724456589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372892365049956659632608785 279669273787467494724456589)
          ·
            refine ⟨104875977670300310521671221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279669273787467494724456589 104875977670300310521671221)
            ·
              refine ⟨9832122906590654111406677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104875977670300310521671221 9832122906590654111406677)
              ·
                refine ⟨115220190311609227868047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9832122906590654111406677 115220190311609227868047)
                ·
                  rfl

theorem cell23_6058544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_6058544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058544 prefixEnd_6058544 := by exact prefixLift 6058544
  have htrace : WordTrace (prefixWord ++ tailWord_6058544) baseStart_6058544 baseEnd_6058544 := by
    simpa [prefixWord, tailWord_6058544, baseEnd_6058544] using wordTrace_append hprefix tailTrace_6058544
  have hstable : (prefixWord ++ tailWord_6058544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058544).length < 2 ^ (prefixWord ++ tailWord_6058544).sum := by decide
  have hdescent : baseEnd_6058544 < baseStart_6058544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058551 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_6058551 : Nat := 118140960795 + 6058551 * 2 ^ 59
def prefixEnd_6058551 : Nat := 4983230072969 + 3 ^ 40 * 6058551 * 2
def baseEnd_6058551 : Nat := 3110948732778030625049737

theorem tailTrace_6058551 : CollatzResearch.WordTrace tailWord_6058551 prefixEnd_6058551 3110948732778030625049737 := by
  unfold tailWord_6058551
  simp only [CollatzResearch.WordTrace]
  refine ⟨220973508673911919977791507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147315672449274613318527671 220973508673911919977791507)
  ·
    refine ⟨331460263010867879966687261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220973508673911919977791507 331460263010867879966687261)
    ·
      refine ⟨124297598629075454987507723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331460263010867879966687261 124297598629075454987507723)
      ·
        refine ⟨186446397943613182481261585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124297598629075454987507723 186446397943613182481261585)
        ·
          refine ⟨139834798457709886860946189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186446397943613182481261585 139834798457709886860946189)
          ·
            refine ⟨52438049421641207572854821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139834798457709886860946189 52438049421641207572854821)
            ·
              refine ⟨9832134266557726419910279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52438049421641207572854821 9832134266557726419910279)
              ·
                refine ⟨14748201399836589629865419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832134266557726419910279 14748201399836589629865419)
                ·
                  refine ⟨22122302099754884444798129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14748201399836589629865419 22122302099754884444798129)
                  ·
                    refine ⟨16591726574816163333598597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22122302099754884444798129 16591726574816163333598597)
                    ·
                      refine ⟨3110948732778030625049737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16591726574816163333598597 3110948732778030625049737)
                      ·
                        rfl

theorem cell23_6058551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_6058551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058551 prefixEnd_6058551 := by exact prefixLift 6058551
  have htrace : WordTrace (prefixWord ++ tailWord_6058551) baseStart_6058551 baseEnd_6058551 := by
    simpa [prefixWord, tailWord_6058551, baseEnd_6058551] using wordTrace_append hprefix tailTrace_6058551
  have hstable : (prefixWord ++ tailWord_6058551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058551).length < 2 ^ (prefixWord ++ tailWord_6058551).sum := by decide
  have hdescent : baseEnd_6058551 < baseStart_6058551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058571 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3]
def baseStart_6058571 : Nat := 118140960795 + 6058571 * 2 ^ 59
def prefixEnd_6058571 : Nat := 4983230072969 + 3 ^ 40 * 6058571 * 2
def baseEnd_6058571 : Nat := 3110959002391120546799645

theorem tailTrace_6058571 : CollatzResearch.WordTrace tailWord_6058571 prefixEnd_6058571 3110959002391120546799645 := by
  unfold tailWord_6058571
  simp only [CollatzResearch.WordTrace]
  refine ⟨220974238133839463393519567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147316158755892975595679711 220974238133839463393519567)
  ·
    refine ⟨331461357200759195090279351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220974238133839463393519567 331461357200759195090279351)
    ·
      refine ⟨497192035801138792635419027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331461357200759195090279351 497192035801138792635419027)
      ·
        refine ⟨745788053701708188953128541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497192035801138792635419027 745788053701708188953128541)
        ·
          refine ⟨279670520138140570857423203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745788053701708188953128541 279670520138140570857423203)
          ·
            refine ⟨419505780207210856286134805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279670520138140570857423203 419505780207210856286134805)
            ·
              refine ⟨19664333447213008888412569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 419505780207210856286134805 19664333447213008888412569)
              ·
                refine ⟨14748250085409756666309427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19664333447213008888412569 14748250085409756666309427)
                ·
                  refine ⟨22122375128114634999464141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14748250085409756666309427 22122375128114634999464141)
                  ·
                    refine ⟨8295890673042988124799053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22122375128114634999464141 8295890673042988124799053)
                    ·
                      refine ⟨3110959002391120546799645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295890673042988124799053 3110959002391120546799645)
                      ·
                        rfl

theorem cell23_6058571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].length) (baseStart_6058571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058571 prefixEnd_6058571 := by exact prefixLift 6058571
  have htrace : WordTrace (prefixWord ++ tailWord_6058571) baseStart_6058571 baseEnd_6058571 := by
    simpa [prefixWord, tailWord_6058571, baseEnd_6058571] using wordTrace_append hprefix tailTrace_6058571
  have hstable : (prefixWord ++ tailWord_6058571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058571).length < 2 ^ (prefixWord ++ tailWord_6058571).sum := by decide
  have hdescent : baseEnd_6058571 < baseStart_6058571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058572 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6058572 : Nat := 118140960795 + 6058572 * 2 ^ 59
def prefixEnd_6058572 : Nat := 4983230072969 + 3 ^ 40 * 6058572 * 2
def baseEnd_6058572 : Nat := 3110959515871775042887141

theorem tailTrace_6058572 : CollatzResearch.WordTrace tailWord_6058572 prefixEnd_6058572 3110959515871775042887141 := by
  unfold tailWord_6058572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110487137303417920282152985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147316183071223893709537313 110487137303417920282152985)
  ·
    refine ⟨82865352977563440211614739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110487137303417920282152985 82865352977563440211614739)
    ·
      refine ⟨124298029466345160317422109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82865352977563440211614739 124298029466345160317422109)
      ·
        refine ⟨46611761049879435119033291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124298029466345160317422109 46611761049879435119033291)
        ·
          refine ⟨69917641574819152678549937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46611761049879435119033291 69917641574819152678549937)
          ·
            refine ⟨52438231181114364508912453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69917641574819152678549937 52438231181114364508912453)
            ·
              refine ⟨9832168346458943345421085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52438231181114364508912453 9832168346458943345421085)
              ·
                refine ⟨3687063129922103754532907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9832168346458943345421085 3687063129922103754532907)
                ·
                  refine ⟨5530594694883155631799361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687063129922103754532907 5530594694883155631799361)
                  ·
                    refine ⟨4147946021162366723849521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530594694883155631799361 4147946021162366723849521)
                    ·
                      refine ⟨3110959515871775042887141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4147946021162366723849521 3110959515871775042887141)
                      ·
                        rfl

theorem cell23_6058572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6058572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058572 prefixEnd_6058572 := by exact prefixLift 6058572
  have htrace : WordTrace (prefixWord ++ tailWord_6058572) baseStart_6058572 baseEnd_6058572 := by
    simpa [prefixWord, tailWord_6058572, baseEnd_6058572] using wordTrace_append hprefix tailTrace_6058572
  have hstable : (prefixWord ++ tailWord_6058572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058572).length < 2 ^ (prefixWord ++ tailWord_6058572).sum := by decide
  have hdescent : baseEnd_6058572 < baseStart_6058572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058605 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6058605 : Nat := 118140960795 + 6058605 * 2 ^ 59
def prefixEnd_6058605 : Nat := 4983230072969 + 3 ^ 40 * 6058605 * 2
def baseEnd_6058605 : Nat := 3110976460733373413774489

theorem tailTrace_6058605 : CollatzResearch.WordTrace tailWord_6058605 prefixEnd_6058605 3110976460733373413774489 := by
  unfold tailWord_6058605
  simp only [CollatzResearch.WordTrace]
  refine ⟨220975478215716287200257269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147316985477144191466838179 220975478215716287200257269)
  ·
    refine ⟨20716451082723401925024119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220975478215716287200257269 20716451082723401925024119)
    ·
      refine ⟨31074676624085102887536179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20716451082723401925024119 31074676624085102887536179)
      ·
        refine ⟨46612014936127654331304269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31074676624085102887536179 46612014936127654331304269)
        ·
          refine ⟨17479505601047870374239101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46612014936127654331304269 17479505601047870374239101)
          ·
            refine ⟨6554814600392951390339663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17479505601047870374239101 6554814600392951390339663)
            ·
              refine ⟨9832221900589427085509495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554814600392951390339663 9832221900589427085509495)
              ·
                refine ⟨14748332850884140628264243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832221900589427085509495 14748332850884140628264243)
                ·
                  refine ⟨22122499276326210942396365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14748332850884140628264243 22122499276326210942396365)
                  ·
                    refine ⟨8295937228622329103398637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22122499276326210942396365 8295937228622329103398637)
                    ·
                      refine ⟨3110976460733373413774489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8295937228622329103398637 3110976460733373413774489)
                      ·
                        rfl

theorem cell23_6058605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6058605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058605 prefixEnd_6058605 := by exact prefixLift 6058605
  have htrace : WordTrace (prefixWord ++ tailWord_6058605) baseStart_6058605 baseEnd_6058605 := by
    simpa [prefixWord, tailWord_6058605, baseEnd_6058605] using wordTrace_append hprefix tailTrace_6058605
  have hstable : (prefixWord ++ tailWord_6058605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058605).length < 2 ^ (prefixWord ++ tailWord_6058605).sum := by decide
  have hdescent : baseEnd_6058605 < baseStart_6058605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058631 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_6058631 : Nat := 118140960795 + 6058631 * 2 ^ 59
def prefixEnd_6058631 : Nat := 4983230072969 + 3 ^ 40 * 6058631 * 2
def baseEnd_6058631 : Nat := 3110989811230390312049369

theorem tailTrace_6058631 : CollatzResearch.WordTrace tailWord_6058631 prefixEnd_6058631 3110989811230390312049369 := by
  unfold tailWord_6058631
  simp only [CollatzResearch.WordTrace]
  refine ⟨220976426513622093640703747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147317617675748062427135831 220976426513622093640703747)
  ·
    refine ⟨331464639770433140461055621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220976426513622093640703747 331464639770433140461055621)
    ·
      refine ⟨62149619956956213836447929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331464639770433140461055621 62149619956956213836447929)
      ·
        refine ⟨46612214967717160377335947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62149619956956213836447929 46612214967717160377335947)
        ·
          refine ⟨69918322451575740566003921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46612214967717160377335947 69918322451575740566003921)
          ·
            refine ⟨52438741838681805424502941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69918322451575740566003921 52438741838681805424502941)
            ·
              refine ⟨19664528189505677034188603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52438741838681805424502941 19664528189505677034188603)
              ·
                refine ⟨29496792284258515551282905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19664528189505677034188603 29496792284258515551282905)
                ·
                  refine ⟨22122594213193886663462179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29496792284258515551282905 22122594213193886663462179)
                  ·
                    refine ⟨33183891319790829995193269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22122594213193886663462179 33183891319790829995193269)
                    ·
                      refine ⟨3110989811230390312049369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33183891319790829995193269 3110989811230390312049369)
                      ·
                        rfl

theorem cell23_6058631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_6058631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058631 prefixEnd_6058631 := by exact prefixLift 6058631
  have htrace : WordTrace (prefixWord ++ tailWord_6058631) baseStart_6058631 baseEnd_6058631 := by
    simpa [prefixWord, tailWord_6058631, baseEnd_6058631] using wordTrace_append hprefix tailTrace_6058631
  have hstable : (prefixWord ++ tailWord_6058631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058631).length < 2 ^ (prefixWord ++ tailWord_6058631).sum := by decide
  have hdescent : baseEnd_6058631 < baseStart_6058631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058661 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_6058661 : Nat := 118140960795 + 6058661 * 2 ^ 59
def prefixEnd_6058661 : Nat := 4983230072969 + 3 ^ 40 * 6058661 * 2
def baseEnd_6058661 : Nat := 3111005215650025194674231

theorem tailTrace_6058661 : CollatzResearch.WordTrace tailWord_6058661 prefixEnd_6058661 3111005215650025194674231 := by
  unfold tailWord_6058661
  simp only [CollatzResearch.WordTrace]
  refine ⟨220977520703513408764295837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147318347135675605842863891 220977520703513408764295837)
  ·
    refine ⟨82866570263817528286610939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220977520703513408764295837 82866570263817528286610939)
    ·
      refine ⟨124299855395726292429916409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82866570263817528286610939 124299855395726292429916409)
      ·
        refine ⟨93224891546794719322437307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124299855395726292429916409 93224891546794719322437307)
        ·
          refine ⟨139837337320192078983655961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93224891546794719322437307 139837337320192078983655961)
          ·
            refine ⟨104878002990144059237741971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139837337320192078983655961 104878002990144059237741971)
            ·
              refine ⟨157317004485216088856612957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104878002990144059237741971 157317004485216088856612957)
              ·
                refine ⟨58993876681956033321229859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157317004485216088856612957 58993876681956033321229859)
                ·
                  refine ⟨88490815022934049981844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58993876681956033321229859 88490815022934049981844789)
                  ·
                    refine ⟨8296013908400067185797949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88490815022934049981844789 8296013908400067185797949)
                    ·
                      refine ⟨3111005215650025194674231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296013908400067185797949 3111005215650025194674231)
                      ·
                        rfl

theorem cell23_6058661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_6058661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058661 prefixEnd_6058661 := by exact prefixLift 6058661
  have htrace : WordTrace (prefixWord ++ tailWord_6058661) baseStart_6058661 baseEnd_6058661 := by
    simpa [prefixWord, tailWord_6058661, baseEnd_6058661] using wordTrace_append hprefix tailTrace_6058661
  have hstable : (prefixWord ++ tailWord_6058661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058661).length < 2 ^ (prefixWord ++ tailWord_6058661).sum := by decide
  have hdescent : baseEnd_6058661 < baseStart_6058661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058666 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6058666 : Nat := 118140960795 + 6058666 * 2 ^ 59
def prefixEnd_6058666 : Nat := 4983230072969 + 3 ^ 40 * 6058666 * 2
def baseEnd_6058666 : Nat := 3111007783053297675111709

theorem tailTrace_6058666 : CollatzResearch.WordTrace tailWord_6058666 prefixEnd_6058666 3111007783053297675111709 := by
  unfold tailWord_6058666
  simp only [CollatzResearch.WordTrace]
  refine ⟨55244425767123823654556963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147318468712330196412151901 55244425767123823654556963)
  ·
    refine ⟨82866638650685735481835445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55244425767123823654556963 82866638650685735481835445)
    ·
      refine ⟨7768747373501787701422073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82866638650685735481835445 7768747373501787701422073)
      ·
        refine ⟨5826560530126340776066555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768747373501787701422073 5826560530126340776066555)
        ·
          refine ⟨8739840795189511164099833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826560530126340776066555 8739840795189511164099833)
          ·
            refine ⟨6554880596392133373074875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8739840795189511164099833 6554880596392133373074875)
            ·
              refine ⟨9832320894588200059612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554880596392133373074875 9832320894588200059612313)
              ·
                refine ⟨7374240670941150044709235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9832320894588200059612313 7374240670941150044709235)
                ·
                  refine ⟨11061361006411725067063853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374240670941150044709235 11061361006411725067063853)
                  ·
                    refine ⟨4148010377404396900148945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11061361006411725067063853 4148010377404396900148945)
                    ·
                      refine ⟨3111007783053297675111709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148010377404396900148945 3111007783053297675111709)
                      ·
                        rfl

theorem cell23_6058666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6058666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058666 prefixEnd_6058666 := by exact prefixLift 6058666
  have htrace : WordTrace (prefixWord ++ tailWord_6058666) baseStart_6058666 baseEnd_6058666 := by
    simpa [prefixWord, tailWord_6058666, baseEnd_6058666] using wordTrace_append hprefix tailTrace_6058666
  have hstable : (prefixWord ++ tailWord_6058666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058666).length < 2 ^ (prefixWord ++ tailWord_6058666).sum := by decide
  have hdescent : baseEnd_6058666 < baseStart_6058666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058698 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_6058698 : Nat := 118140960795 + 6058698 * 2 ^ 59
def prefixEnd_6058698 : Nat := 4983230072969 + 3 ^ 40 * 6058698 * 2
def baseEnd_6058698 : Nat := 1037008071478080516637187

theorem tailTrace_6058698 : CollatzResearch.WordTrace tailWord_6058698 prefixEnd_6058698 1037008071478080516637187 := by
  unfold tailWord_6058698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55244717551094841020848187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147319246802919576055595165 55244717551094841020848187)
  ·
    refine ⟨82867076326642261531272281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55244717551094841020848187 82867076326642261531272281)
    ·
      refine ⟨62150307244981696148454211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82867076326642261531272281 62150307244981696148454211)
      ·
        refine ⟨93225460867472544222681317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62150307244981696148454211 93225460867472544222681317)
        ·
          refine ⟨17479773912651102041752747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93225460867472544222681317 17479773912651102041752747)
          ·
            refine ⟨26219660868976653062629121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17479773912651102041752747 26219660868976653062629121)
            ·
              refine ⟨19664745651732489796971841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26219660868976653062629121 19664745651732489796971841)
              ·
                refine ⟨14748559238799367347728881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19664745651732489796971841 14748559238799367347728881)
                ·
                  refine ⟨11061419429099525510796661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748559238799367347728881 11061419429099525510796661)
                  ·
                    refine ⟨1037008071478080516637187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11061419429099525510796661 1037008071478080516637187)
                    ·
                      rfl

theorem cell23_6058698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_6058698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058698 prefixEnd_6058698 := by exact prefixLift 6058698
  have htrace : WordTrace (prefixWord ++ tailWord_6058698) baseStart_6058698 baseEnd_6058698 := by
    simpa [prefixWord, tailWord_6058698, baseEnd_6058698] using wordTrace_append hprefix tailTrace_6058698
  have hstable : (prefixWord ++ tailWord_6058698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058698).length < 2 ^ (prefixWord ++ tailWord_6058698).sum := by decide
  have hdescent : baseEnd_6058698 < baseStart_6058698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058702 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_6058702 : Nat := 118140960795 + 6058702 * 2 ^ 59
def prefixEnd_6058702 : Nat := 4983230072969 + 3 ^ 40 * 6058702 * 2
def baseEnd_6058702 : Nat := 345669585372984392695727

theorem tailTrace_6058702 : CollatzResearch.WordTrace tailWord_6058702 prefixEnd_6058702 345669585372984392695727 := by
  unfold tailWord_6058702
  simp only [CollatzResearch.WordTrace]
  refine ⟨27622377012045609095817295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147319344064243248511025573 27622377012045609095817295)
  ·
    refine ⟨41433565518068413643725943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27622377012045609095817295 41433565518068413643725943)
    ·
      refine ⟨62150348277102620465588915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41433565518068413643725943 62150348277102620465588915)
      ·
        refine ⟨93225522415653930698383373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62150348277102620465588915 93225522415653930698383373)
        ·
          refine ⟨34959570905870224011893765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93225522415653930698383373 34959570905870224011893765)
          ·
            refine ⟨6554919544850667002230081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34959570905870224011893765 6554919544850667002230081)
            ·
              refine ⟨4916189658638000251672561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6554919544850667002230081 4916189658638000251672561)
              ·
                refine ⟨3687142243978500188754421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916189658638000251672561 3687142243978500188754421)
                ·
                  refine ⟨345669585372984392695727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3687142243978500188754421 345669585372984392695727)
                  ·
                    rfl

theorem cell23_6058702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_6058702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058702 prefixEnd_6058702 := by exact prefixLift 6058702
  have htrace : WordTrace (prefixWord ++ tailWord_6058702) baseStart_6058702 baseEnd_6058702 := by
    simpa [prefixWord, tailWord_6058702, baseEnd_6058702] using wordTrace_append hprefix tailTrace_6058702
  have hstable : (prefixWord ++ tailWord_6058702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058702).length < 2 ^ (prefixWord ++ tailWord_6058702).sum := by decide
  have hdescent : baseEnd_6058702 < baseStart_6058702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058735 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_6058735 : Nat := 118140960795 + 6058735 * 2 ^ 59
def prefixEnd_6058735 : Nat := 4983230072969 + 3 ^ 40 * 6058735 * 2
def baseEnd_6058735 : Nat := 3111043213218457905148891

theorem tailTrace_6058735 : CollatzResearch.WordTrace tailWord_6058735 prefixEnd_6058735 3111043213218457905148891 := by
  unfold tailWord_6058735
  simp only [CollatzResearch.WordTrace]
  refine ⟨220980219705245319402489659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147320146470163546268326439 220980219705245319402489659)
  ·
    refine ⟨331470329557867979103734489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220980219705245319402489659 331470329557867979103734489)
    ·
      refine ⟨248602747168400984327800867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331470329557867979103734489 248602747168400984327800867)
      ·
        refine ⟨372904120752601476491701301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248602747168400984327800867 372904120752601476491701301)
        ·
          refine ⟨34959761320556388421096997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 372904120752601476491701301 34959761320556388421096997)
          ·
            refine ⟨6554955247604322828955687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34959761320556388421096997 6554955247604322828955687)
            ·
              refine ⟨9832432871406484243433531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554955247604322828955687 9832432871406484243433531)
              ·
                refine ⟨14748649307109726365150297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832432871406484243433531 14748649307109726365150297)
                ·
                  refine ⟨11061486980332294773862723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14748649307109726365150297 11061486980332294773862723)
                  ·
                    refine ⟨16592230470498442160794085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11061486980332294773862723 16592230470498442160794085)
                    ·
                      refine ⟨3111043213218457905148891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16592230470498442160794085 3111043213218457905148891)
                      ·
                        rfl

theorem cell23_6058735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_6058735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058735 prefixEnd_6058735 := by exact prefixLift 6058735
  have htrace : WordTrace (prefixWord ++ tailWord_6058735) baseStart_6058735 baseEnd_6058735 := by
    simpa [prefixWord, tailWord_6058735, baseEnd_6058735] using wordTrace_append hprefix tailTrace_6058735
  have hstable : (prefixWord ++ tailWord_6058735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058735).length < 2 ^ (prefixWord ++ tailWord_6058735).sum := by decide
  have hdescent : baseEnd_6058735 < baseStart_6058735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058761 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_6058761 : Nat := 118140960795 + 6058761 * 2 ^ 59
def prefixEnd_6058761 : Nat := 4983230072969 + 3 ^ 40 * 6058761 * 2
def baseEnd_6058761 : Nat := 3111056563715474803423771

theorem tailTrace_6058761 : CollatzResearch.WordTrace tailWord_6058761 prefixEnd_6058761 3111056563715474803423771 := by
  unfold tailWord_6058761
  simp only [CollatzResearch.WordTrace]
  refine ⟨220981168003151125842936137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147320778668767417228624091 220981168003151125842936137)
  ·
    refine ⟨165735876002363344382202103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220981168003151125842936137 165735876002363344382202103)
    ·
      refine ⟨248603814003545016573303155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165735876002363344382202103 248603814003545016573303155)
      ·
        refine ⟨372905721005317524859954733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248603814003545016573303155 372905721005317524859954733)
        ·
          refine ⟨139839645376994071822483025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372905721005317524859954733 139839645376994071822483025)
          ·
            refine ⟨104879734032745553866862269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139839645376994071822483025 104879734032745553866862269)
            ·
              refine ⟨39329900262279582700073351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104879734032745553866862269 39329900262279582700073351)
              ·
                refine ⟨58994850393419374050110027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39329900262279582700073351 58994850393419374050110027)
                ·
                  refine ⟨88492275590129061075165041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58994850393419374050110027 88492275590129061075165041)
                  ·
                    refine ⟨66369206692596795806373781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88492275590129061075165041 66369206692596795806373781)
                    ·
                      refine ⟨3111056563715474803423771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66369206692596795806373781 3111056563715474803423771)
                      ·
                        rfl

theorem cell23_6058761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_6058761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058761 prefixEnd_6058761 := by exact prefixLift 6058761
  have htrace : WordTrace (prefixWord ++ tailWord_6058761) baseStart_6058761 baseEnd_6058761 := by
    simpa [prefixWord, tailWord_6058761, baseEnd_6058761] using wordTrace_append hprefix tailTrace_6058761
  have hstable : (prefixWord ++ tailWord_6058761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058761).length < 2 ^ (prefixWord ++ tailWord_6058761).sum := by decide
  have hdescent : baseEnd_6058761 < baseStart_6058761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058785 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6058785 : Nat := 118140960795 + 6058785 * 2 ^ 59
def prefixEnd_6058785 : Nat := 4983230072969 + 3 ^ 40 * 6058785 * 2
def baseEnd_6058785 : Nat := 3111068887251182709523661

theorem tailTrace_6058785 : CollatzResearch.WordTrace tailWord_6058785 prefixEnd_6058785 3111068887251182709523661 := by
  unfold tailWord_6058785
  simp only [CollatzResearch.WordTrace]
  refine ⟨220982043355064177941809809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147321362236709451961206539 220982043355064177941809809)
  ·
    refine ⟨165736532516298133456357357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220982043355064177941809809 165736532516298133456357357)
    ·
      refine ⟨62151199693611800046134009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165736532516298133456357357 62151199693611800046134009)
      ·
        refine ⟨46613399770208850034600507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62151199693611800046134009 46613399770208850034600507)
        ·
          refine ⟨69920099655313275051900761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46613399770208850034600507 69920099655313275051900761)
          ·
            refine ⟨52440074741484956288925571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69920099655313275051900761 52440074741484956288925571)
            ·
              refine ⟨78660112112227434433388357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52440074741484956288925571 78660112112227434433388357)
              ·
                refine ⟨14748771021042643956260317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78660112112227434433388357 14748771021042643956260317)
                ·
                  refine ⟨5530789132890991483597619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14748771021042643956260317 5530789132890991483597619)
                  ·
                    refine ⟨8296183699336487225396429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530789132890991483597619 8296183699336487225396429)
                    ·
                      refine ⟨3111068887251182709523661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296183699336487225396429 3111068887251182709523661)
                      ·
                        rfl

theorem cell23_6058785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6058785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058785 prefixEnd_6058785 := by exact prefixLift 6058785
  have htrace : WordTrace (prefixWord ++ tailWord_6058785) baseStart_6058785 baseEnd_6058785 := by
    simpa [prefixWord, tailWord_6058785, baseEnd_6058785] using wordTrace_append hprefix tailTrace_6058785
  have hstable : (prefixWord ++ tailWord_6058785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058785).length < 2 ^ (prefixWord ++ tailWord_6058785).sum := by decide
  have hdescent : baseEnd_6058785 < baseStart_6058785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058805 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_6058805 : Nat := 118140960795 + 6058805 * 2 ^ 59
def prefixEnd_6058805 : Nat := 4983230072969 + 3 ^ 40 * 6058805 * 2
def baseEnd_6058805 : Nat := 1037026385621424210424523

theorem tailTrace_6058805 : CollatzResearch.WordTrace tailWord_6058805 prefixEnd_6058805 1037026385621424210424523 := by
  unfold tailWord_6058805
  simp only [CollatzResearch.WordTrace]
  refine ⟨220982772814991721357537869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147321848543327814238358579 220982772814991721357537869)
  ·
    refine ⟨82868539805621895509076701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220982772814991721357537869 82868539805621895509076701)
    ·
      refine ⟨31075702427108210815903763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82868539805621895509076701 31075702427108210815903763)
      ·
        refine ⟨46613553640662316223855645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31075702427108210815903763 46613553640662316223855645)
        ·
          refine ⟨17480082615248368583945867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46613553640662316223855645 17480082615248368583945867)
          ·
            refine ⟨26220123922872552875918801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17480082615248368583945867 26220123922872552875918801)
            ·
              refine ⟨19665092942154414656939101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26220123922872552875918801 19665092942154414656939101)
              ·
                refine ⟨7374409853307905496352163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19665092942154414656939101 7374409853307905496352163)
                ·
                  refine ⟨11061614779961858244528245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374409853307905496352163 11061614779961858244528245)
                  ·
                    refine ⟨1037026385621424210424523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11061614779961858244528245 1037026385621424210424523)
                    ·
                      rfl

theorem cell23_6058805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_6058805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058805 prefixEnd_6058805 := by exact prefixLift 6058805
  have htrace : WordTrace (prefixWord ++ tailWord_6058805) baseStart_6058805 baseEnd_6058805 := by
    simpa [prefixWord, tailWord_6058805, baseEnd_6058805] using wordTrace_append hprefix tailTrace_6058805
  have hstable : (prefixWord ++ tailWord_6058805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058805).length < 2 ^ (prefixWord ++ tailWord_6058805).sum := by decide
  have hdescent : baseEnd_6058805 < baseStart_6058805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058819 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 1, 1, 3]
def baseStart_6058819 : Nat := 118140960795 + 6058819 * 2 ^ 59
def prefixEnd_6058819 : Nat := 4983230072969 + 3 ^ 40 * 6058819 * 2
def baseEnd_6058819 : Nat := 3111086345593435576498505

theorem tailTrace_6058819 : CollatzResearch.WordTrace tailWord_6058819 prefixEnd_6058819 3111086345593435576498505 := by
  unfold tailWord_6058819
  simp only [CollatzResearch.WordTrace]
  refine ⟨220983283436941001748547511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147322188957960667832365007 220983283436941001748547511)
  ·
    refine ⟨331474925155411502622821267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220983283436941001748547511 331474925155411502622821267)
    ·
      refine ⟨497212387733117253934231901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331474925155411502622821267 497212387733117253934231901)
      ·
        refine ⟨186454645399918970225336963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497212387733117253934231901 186454645399918970225336963)
        ·
          refine ⟨279681968099878455338005445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186454645399918970225336963 279681968099878455338005445)
          ·
            refine ⟨52440369018727210375876021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 279681968099878455338005445 52440369018727210375876021)
            ·
              refine ⟨4916284595505675972738377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52440369018727210375876021 4916284595505675972738377)
              ·
                refine ⟨3687213446629256979553783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916284595505675972738377 3687213446629256979553783)
                ·
                  refine ⟨5530820169943885469330675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687213446629256979553783 5530820169943885469330675)
                  ·
                    refine ⟨8296230254915828203996013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530820169943885469330675 8296230254915828203996013)
                    ·
                      refine ⟨3111086345593435576498505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296230254915828203996013 3111086345593435576498505)
                      ·
                        rfl

theorem cell23_6058819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_6058819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058819 prefixEnd_6058819 := by exact prefixLift 6058819
  have htrace : WordTrace (prefixWord ++ tailWord_6058819) baseStart_6058819 baseEnd_6058819 := by
    simpa [prefixWord, tailWord_6058819, baseEnd_6058819] using wordTrace_append hprefix tailTrace_6058819
  have hstable : (prefixWord ++ tailWord_6058819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058819).length < 2 ^ (prefixWord ++ tailWord_6058819).sum := by decide
  have hdescent : baseEnd_6058819 < baseStart_6058819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058842 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_6058842 : Nat := 118140960795 + 6058842 * 2 ^ 59
def prefixEnd_6058842 : Nat := 4983230072969 + 3 ^ 40 * 6058842 * 2
def baseEnd_6058842 : Nat := 3111098155648488986510899

theorem tailTrace_6058842 : CollatzResearch.WordTrace tailWord_6058842 prefixEnd_6058842 3111098155648488986510899 := by
  unfold tailWord_6058842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55246030578964419169158695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147322748210571784451089853 55246030578964419169158695)
  ·
    refine ⟨82869045868446628753738043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55246030578964419169158695 82869045868446628753738043)
    ·
      refine ⟨124303568802669943130607065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82869045868446628753738043 124303568802669943130607065)
      ·
        refine ⟨93227676602002457347955299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124303568802669943130607065 93227676602002457347955299)
        ·
          refine ⟨139841514903003686021932949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93227676602002457347955299 139841514903003686021932949)
          ·
            refine ⟨6555071011078297782278107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139841514903003686021932949 6555071011078297782278107)
            ·
              refine ⟨9832606516617446673417161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555071011078297782278107 9832606516617446673417161)
              ·
                refine ⟨7374454887463085005062871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9832606516617446673417161 7374454887463085005062871)
                ·
                  refine ⟨11061682331194627507594307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7374454887463085005062871 11061682331194627507594307)
                  ·
                    refine ⟨16592523496791941261391461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11061682331194627507594307 16592523496791941261391461)
                    ·
                      refine ⟨3111098155648488986510899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16592523496791941261391461 3111098155648488986510899)
                      ·
                        rfl

theorem cell23_6058842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_6058842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058842 prefixEnd_6058842 := by exact prefixLift 6058842
  have htrace : WordTrace (prefixWord ++ tailWord_6058842) baseStart_6058842 baseEnd_6058842 := by
    simpa [prefixWord, tailWord_6058842, baseEnd_6058842] using wordTrace_append hprefix tailTrace_6058842
  have hstable : (prefixWord ++ tailWord_6058842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058842).length < 2 ^ (prefixWord ++ tailWord_6058842).sum := by decide
  have hdescent : baseEnd_6058842 < baseStart_6058842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058855 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6058855 : Nat := 118140960795 + 6058855 * 2 ^ 59
def prefixEnd_6058855 : Nat := 4983230072969 + 3 ^ 40 * 6058855 * 2
def baseEnd_6058855 : Nat := 3111104830896997435648339

theorem tailTrace_6058855 : CollatzResearch.WordTrace tailWord_6058855 prefixEnd_6058855 3111104830896997435648339 := by
  unfold tailWord_6058855
  simp only [CollatzResearch.WordTrace]
  refine ⟨220984596464810579896858019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147323064309873719931238679 220984596464810579896858019)
  ·
    refine ⟨331476894697215869845287029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220984596464810579896858019 331476894697215869845287029)
    ·
      refine ⟨31075958877863987797995659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331476894697215869845287029 31075958877863987797995659)
      ·
        refine ⟨46613938316795981696993489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31075958877863987797995659 46613938316795981696993489)
        ·
          refine ⟨34960453737596986272745117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46613938316795981696993489 34960453737596986272745117)
          ·
            refine ⟨13110170151598869852279419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34960453737596986272745117 13110170151598869852279419)
            ·
              refine ⟨19665255227398304778419129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13110170151598869852279419 19665255227398304778419129)
              ·
                refine ⟨14748941420548728583814347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19665255227398304778419129 14748941420548728583814347)
                ·
                  refine ⟨22123412130823092875721521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14748941420548728583814347 22123412130823092875721521)
                  ·
                    refine ⟨16592559098117319656791141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22123412130823092875721521 16592559098117319656791141)
                    ·
                      refine ⟨3111104830896997435648339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16592559098117319656791141 3111104830896997435648339)
                      ·
                        rfl

theorem cell23_6058855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6058855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058855 prefixEnd_6058855 := by exact prefixLift 6058855
  have htrace : WordTrace (prefixWord ++ tailWord_6058855) baseStart_6058855 baseEnd_6058855 := by
    simpa [prefixWord, tailWord_6058855, baseEnd_6058855] using wordTrace_append hprefix tailTrace_6058855
  have hstable : (prefixWord ++ tailWord_6058855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058855).length < 2 ^ (prefixWord ++ tailWord_6058855).sum := by decide
  have hdescent : baseEnd_6058855 < baseStart_6058855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058875 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 3]
def baseStart_6058875 : Nat := 118140960795 + 6058875 * 2 ^ 59
def prefixEnd_6058875 : Nat := 4983230072969 + 3 ^ 40 * 6058875 * 2
def baseEnd_6058875 : Nat := 3111115100510087357398247

theorem tailTrace_6058875 : CollatzResearch.WordTrace tailWord_6058875 prefixEnd_6058875 3111115100510087357398247 := by
  unfold tailWord_6058875
  simp only [CollatzResearch.WordTrace]
  refine ⟨220985325924738123312586079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147323550616492082208390719 220985325924738123312586079)
  ·
    refine ⟨331477988887107184968879119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220985325924738123312586079 331477988887107184968879119)
    ·
      refine ⟨497216983330660777453318679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331477988887107184968879119 497216983330660777453318679)
      ·
        refine ⟨745825474995991166179978019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497216983330660777453318679 745825474995991166179978019)
        ·
          refine ⟨1118738212493986749269967029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745825474995991166179978019 1118738212493986749269967029)
          ·
            refine ⟨104881707421311257744059409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1118738212493986749269967029 104881707421311257744059409)
            ·
              refine ⟨78661280565983443308044557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104881707421311257744059409 78661280565983443308044557)
              ·
                refine ⟨29497980212243791240516709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78661280565983443308044557 29497980212243791240516709)
                ·
                  refine ⟨5530871289795710857596883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29497980212243791240516709 5530871289795710857596883)
                  ·
                    refine ⟨8296306934693566286395325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530871289795710857596883 8296306934693566286395325)
                    ·
                      refine ⟨3111115100510087357398247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296306934693566286395325 3111115100510087357398247)
                      ·
                        rfl

theorem cell23_6058875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 3].length) (baseStart_6058875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058875 prefixEnd_6058875 := by exact prefixLift 6058875
  have htrace : WordTrace (prefixWord ++ tailWord_6058875) baseStart_6058875 baseEnd_6058875 := by
    simpa [prefixWord, tailWord_6058875, baseEnd_6058875] using wordTrace_append hprefix tailTrace_6058875
  have hstable : (prefixWord ++ tailWord_6058875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058875).length < 2 ^ (prefixWord ++ tailWord_6058875).sum := by decide
  have hdescent : baseEnd_6058875 < baseStart_6058875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058892 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 2, 1, 3]
def baseStart_6058892 : Nat := 118140960795 + 6058892 * 2 ^ 59
def prefixEnd_6058892 : Nat := 4983230072969 + 3 ^ 40 * 6058892 * 2
def baseEnd_6058892 : Nat := 3111123829681213790885669

theorem tailTrace_6058892 : CollatzResearch.WordTrace tailWord_6058892 prefixEnd_6058892 3111123829681213790885669 := by
  unfold tailWord_6058892
  simp only [CollatzResearch.WordTrace]
  refine ⟨110492972982838267607977465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147323963977117690143969953 110492972982838267607977465)
  ·
    refine ⟨82869729737128700705983099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110492972982838267607977465 82869729737128700705983099)
    ·
      refine ⟨124304594605693051058974649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82869729737128700705983099 124304594605693051058974649)
      ·
        refine ⟨93228445954269788294230987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124304594605693051058974649 93228445954269788294230987)
        ·
          refine ⟨139842668931404682441346481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93228445954269788294230987 139842668931404682441346481)
          ·
            refine ⟨104882001698553511831009861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139842668931404682441346481 104882001698553511831009861)
            ·
              refine ⟨19665375318478783468314349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104882001698553511831009861 19665375318478783468314349)
              ·
                refine ⟨7374515744429543800617881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19665375318478783468314349 7374515744429543800617881)
                ·
                  refine ⟨5530886808322157850463411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7374515744429543800617881 5530886808322157850463411)
                  ·
                    refine ⟨8296330212483236775695117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5530886808322157850463411 8296330212483236775695117)
                    ·
                      refine ⟨3111123829681213790885669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296330212483236775695117 3111123829681213790885669)
                      ·
                        rfl

theorem cell23_6058892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_6058892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058892 prefixEnd_6058892 := by exact prefixLift 6058892
  have htrace : WordTrace (prefixWord ++ tailWord_6058892) baseStart_6058892 baseEnd_6058892 := by
    simpa [prefixWord, tailWord_6058892, baseEnd_6058892] using wordTrace_append hprefix tailTrace_6058892
  have hstable : (prefixWord ++ tailWord_6058892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058892).length < 2 ^ (prefixWord ++ tailWord_6058892).sum := by decide
  have hdescent : baseEnd_6058892 < baseStart_6058892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058950 : List Nat := [6, 1, 3, 1, 2, 1, 2, 7]
def baseStart_6058950 : Nat := 118140960795 + 6058950 * 2 ^ 59
def prefixEnd_6058950 : Nat := 4983230072969 + 3 ^ 40 * 6058950 * 2
def baseEnd_6058950 : Nat := 115227911539228687554089

theorem tailTrace_6058950 : CollatzResearch.WordTrace tailWord_6058950 prefixEnd_6058950 115227911539228687554089 := by
  unfold tailWord_6058950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905876918733325347548947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147325374266310940747710869 6905876918733325347548947)
  ·
    refine ⟨10358815378099988021323421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6905876918733325347548947 10358815378099988021323421)
    ·
      refine ⟨3884555766787495507996283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10358815378099988021323421 3884555766787495507996283)
      ·
        refine ⟨5826833650181243261994425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884555766787495507996283 5826833650181243261994425)
        ·
          refine ⟨4370125237635932446495819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5826833650181243261994425 4370125237635932446495819)
          ·
            refine ⟨6555187856453898669743729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370125237635932446495819 6555187856453898669743729)
            ·
              refine ⟨4916390892340424002307797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6555187856453898669743729 4916390892340424002307797)
              ·
                refine ⟨115227911539228687554089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4916390892340424002307797 115227911539228687554089)
                ·
                  rfl

theorem cell23_6058950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_6058950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058950 prefixEnd_6058950 := by exact prefixLift 6058950
  have htrace : WordTrace (prefixWord ++ tailWord_6058950) baseStart_6058950 baseEnd_6058950 := by
    simpa [prefixWord, tailWord_6058950, baseEnd_6058950] using wordTrace_append hprefix tailTrace_6058950
  have hstable : (prefixWord ++ tailWord_6058950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058950).length < 2 ^ (prefixWord ++ tailWord_6058950).sum := by decide
  have hdescent : baseEnd_6058950 < baseStart_6058950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058966 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6058966 : Nat := 118140960795 + 6058966 * 2 ^ 59
def prefixEnd_6058966 : Nat := 4983230072969 + 3 ^ 40 * 6058966 * 2
def baseEnd_6058966 : Nat := 3111161827249646501360329

theorem tailTrace_6058966 : CollatzResearch.WordTrace tailWord_6058966 prefixEnd_6058966 3111161827249646501360329 := by
  unfold tailWord_6058966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811790310463027865884297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147325763311605630569432501 13811790310463027865884297)
  ·
    refine ⟨10358842732847270899413223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13811790310463027865884297 10358842732847270899413223)
    ·
      refine ⟨15538264099270906349119835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10358842732847270899413223 15538264099270906349119835)
      ·
        refine ⟨23307396148906359523679753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15538264099270906349119835 23307396148906359523679753)
        ·
          refine ⟨17480547111679769642759815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23307396148906359523679753 17480547111679769642759815)
          ·
            refine ⟨26220820667519654464139723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17480547111679769642759815 26220820667519654464139723)
            ·
              refine ⟨39331231001279481696209585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26220820667519654464139723 39331231001279481696209585)
              ·
                refine ⟨29498423250959611272157189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39331231001279481696209585 29498423250959611272157189)
                ·
                  refine ⟨5530954359554927113529473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29498423250959611272157189 5530954359554927113529473)
                  ·
                    refine ⟨4148215769666195335147105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5530954359554927113529473 4148215769666195335147105)
                    ·
                      refine ⟨3111161827249646501360329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148215769666195335147105 3111161827249646501360329)
                      ·
                        rfl

theorem cell23_6058966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6058966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058966 prefixEnd_6058966 := by exact prefixLift 6058966
  have htrace : WordTrace (prefixWord ++ tailWord_6058966) baseStart_6058966 baseEnd_6058966 := by
    simpa [prefixWord, tailWord_6058966, baseEnd_6058966] using wordTrace_append hprefix tailTrace_6058966
  have hstable : (prefixWord ++ tailWord_6058966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058966).length < 2 ^ (prefixWord ++ tailWord_6058966).sum := by decide
  have hdescent : baseEnd_6058966 < baseStart_6058966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6058988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6058988 : Nat := 118140960795 + 6058988 * 2 ^ 59
def prefixEnd_6058988 : Nat := 4983230072969 + 3 ^ 40 * 6058988 * 2
def baseEnd_6058988 : Nat := 3111173123824045415285227

theorem tailTrace_6058988 : CollatzResearch.WordTrace tailWord_6058988 prefixEnd_6058988 3111173123824045415285227 := by
  unfold tailWord_6058988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110494723686664371805724809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147326298248885829074299745 110494723686664371805724809)
  ·
    refine ⟨82871042764998278854293607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110494723686664371805724809 82871042764998278854293607)
    ·
      refine ⟨124306564147497418281440411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82871042764998278854293607 124306564147497418281440411)
      ·
        refine ⟨186459846221246127422160617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124306564147497418281440411 186459846221246127422160617)
        ·
          refine ⟨139844884665934595566620463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186459846221246127422160617 139844884665934595566620463)
          ·
            refine ⟨209767326998901893349930695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139844884665934595566620463 209767326998901893349930695)
            ·
              refine ⟨314650990498352840024896043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209767326998901893349930695 314650990498352840024896043)
              ·
                refine ⟨471976485747529260037344065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314650990498352840024896043 471976485747529260037344065)
                ·
                  refine ⟨353982364310646945028008049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471976485747529260037344065 353982364310646945028008049)
                  ·
                    refine ⟨265486773232985208771006037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353982364310646945028008049 265486773232985208771006037)
                    ·
                      refine ⟨3111173123824045415285227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265486773232985208771006037 3111173123824045415285227)
                      ·
                        rfl

theorem cell23_6058988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6058988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6058988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6058988 prefixEnd_6058988 := by exact prefixLift 6058988
  have htrace : WordTrace (prefixWord ++ tailWord_6058988) baseStart_6058988 baseEnd_6058988 := by
    simpa [prefixWord, tailWord_6058988, baseEnd_6058988] using wordTrace_append hprefix tailTrace_6058988
  have hstable : (prefixWord ++ tailWord_6058988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6058988).length < 2 ^ (prefixWord ++ tailWord_6058988).sum := by decide
  have hdescent : baseEnd_6058988 < baseStart_6058988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6058988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059005 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_6059005 : Nat := 118140960795 + 6059005 * 2 ^ 59
def prefixEnd_6059005 : Nat := 4983230072969 + 3 ^ 40 * 6059005 * 2
def baseEnd_6059005 : Nat := 3111181852995171848772649

theorem tailTrace_6059005 : CollatzResearch.WordTrace tailWord_6059005 prefixEnd_6059005 3111181852995171848772649 := by
  unfold tailWord_6059005
  simp only [CollatzResearch.WordTrace]
  refine ⟨220990067414267155514818469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147326711609511437009878979 220990067414267155514818469)
  ·
    refine ⟨41435637640175091659028463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220990067414267155514818469 41435637640175091659028463)
    ·
      refine ⟨62153456460262637488542695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41435637640175091659028463 62153456460262637488542695)
      ·
        refine ⟨93230184690393956232814043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62153456460262637488542695 93230184690393956232814043)
        ·
          refine ⟨139845277035590934349221065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93230184690393956232814043 139845277035590934349221065)
          ·
            refine ⟨104883957776693200761915799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139845277035590934349221065 104883957776693200761915799)
            ·
              refine ⟨157325936665039801142873699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104883957776693200761915799 157325936665039801142873699)
              ·
                refine ⟨235988904997559701714310549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157325936665039801142873699 235988904997559701714310549)
                ·
                  refine ⟨11061979921760611017858307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235988904997559701714310549 11061979921760611017858307)
                  ·
                    refine ⟨16592969882640916526787461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11061979921760611017858307 16592969882640916526787461)
                    ·
                      refine ⟨3111181852995171848772649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16592969882640916526787461 3111181852995171848772649)
                      ·
                        rfl

theorem cell23_6059005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_6059005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059005 prefixEnd_6059005 := by exact prefixLift 6059005
  have htrace : WordTrace (prefixWord ++ tailWord_6059005) baseStart_6059005 baseEnd_6059005 := by
    simpa [prefixWord, tailWord_6059005, baseEnd_6059005] using wordTrace_append hprefix tailTrace_6059005
  have hstable : (prefixWord ++ tailWord_6059005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059005).length < 2 ^ (prefixWord ++ tailWord_6059005).sum := by decide
  have hdescent : baseEnd_6059005 < baseStart_6059005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059008 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_6059008 : Nat := 118140960795 + 6059008 * 2 ^ 59
def prefixEnd_6059008 : Nat := 4983230072969 + 3 ^ 40 * 6059008 * 2
def baseEnd_6059008 : Nat := 3111183393437135337035135

theorem tailTrace_6059008 : CollatzResearch.WordTrace tailWord_6059008 prefixEnd_6059008 3111183393437135337035135 := by
  unfold tailWord_6059008
  simp only [CollatzResearch.WordTrace]
  refine ⟨110495088416628143513588839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147326784555504191351451785 110495088416628143513588839)
  ·
    refine ⟨165742632624942215270383259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110495088416628143513588839 165742632624942215270383259)
    ·
      refine ⟨248613948937413322905574889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165742632624942215270383259 248613948937413322905574889)
      ·
        refine ⟨186460461703059992179181167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248613948937413322905574889 186460461703059992179181167)
        ·
          refine ⟨279690692554589988268771751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186460461703059992179181167 279690692554589988268771751)
          ·
            refine ⟨419536038831884982403157627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279690692554589988268771751 419536038831884982403157627)
            ·
              refine ⟨629304058247827473604736441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419536038831884982403157627 629304058247827473604736441)
              ·
                refine ⟨471978043685870605203552331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629304058247827473604736441 471978043685870605203552331)
                ·
                  refine ⟨707967065528805907805328497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471978043685870605203552331 707967065528805907805328497)
                  ·
                    refine ⟨530975299146604430853996373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707967065528805907805328497 530975299146604430853996373)
                    ·
                      refine ⟨3111183393437135337035135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 530975299146604430853996373 3111183393437135337035135)
                      ·
                        rfl

theorem cell23_6059008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_6059008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059008 prefixEnd_6059008 := by exact prefixLift 6059008
  have htrace : WordTrace (prefixWord ++ tailWord_6059008) baseStart_6059008 baseEnd_6059008 := by
    simpa [prefixWord, tailWord_6059008, baseEnd_6059008] using wordTrace_append hprefix tailTrace_6059008
  have hstable : (prefixWord ++ tailWord_6059008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059008).length < 2 ^ (prefixWord ++ tailWord_6059008).sum := by decide
  have hdescent : baseEnd_6059008 < baseStart_6059008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059022 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6059022 : Nat := 118140960795 + 6059022 * 2 ^ 59
def prefixEnd_6059022 : Nat := 4983230072969 + 3 ^ 40 * 6059022 * 2
def baseEnd_6059022 : Nat := 3111190582166298282260071

theorem tailTrace_6059022 : CollatzResearch.WordTrace tailWord_6059022 prefixEnd_6059022 3111190582166298282260071 := by
  unfold tailWord_6059022
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623835931900695927273415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147327124970137044945458213 27623835931900695927273415)
  ·
    refine ⟨41435753897851043890910123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623835931900695927273415 41435753897851043890910123)
    ·
      refine ⟨62153630846776565836365185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41435753897851043890910123 62153630846776565836365185)
      ·
        refine ⟨46615223135082424377273889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62153630846776565836365185 46615223135082424377273889)
        ·
          refine ⟨34961417351311818282955417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46615223135082424377273889 34961417351311818282955417)
          ·
            refine ⟨26221063013483863712216563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34961417351311818282955417 26221063013483863712216563)
            ·
              refine ⟨39331594520225795568324845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26221063013483863712216563 39331594520225795568324845)
              ·
                refine ⟨14749347945084673338121817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39331594520225795568324845 14749347945084673338121817)
                ·
                  refine ⟨11062010958813505003591363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14749347945084673338121817 11062010958813505003591363)
                  ·
                    refine ⟨16593016438220257505387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11062010958813505003591363 16593016438220257505387045)
                    ·
                      refine ⟨3111190582166298282260071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16593016438220257505387045 3111190582166298282260071)
                      ·
                        rfl

theorem cell23_6059022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6059022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059022 prefixEnd_6059022 := by exact prefixLift 6059022
  have htrace : WordTrace (prefixWord ++ tailWord_6059022) baseStart_6059022 baseEnd_6059022 := by
    simpa [prefixWord, tailWord_6059022, baseEnd_6059022] using wordTrace_append hprefix tailTrace_6059022
  have hstable : (prefixWord ++ tailWord_6059022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059022).length < 2 ^ (prefixWord ++ tailWord_6059022).sum := by decide
  have hdescent : baseEnd_6059022 < baseStart_6059022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059025 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_6059025 : Nat := 118140960795 + 6059025 * 2 ^ 59
def prefixEnd_6059025 : Nat := 4983230072969 + 3 ^ 40 * 6059025 * 2
def baseEnd_6059025 : Nat := 3111192122608261770522557

theorem tailTrace_6059025 : CollatzResearch.WordTrace tailWord_6059025 prefixEnd_6059025 3111192122608261770522557 := by
  unfold tailWord_6059025
  simp only [CollatzResearch.WordTrace]
  refine ⟨220990796874194698930546529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147327197916129799287031019 220990796874194698930546529)
  ·
    refine ⟨165743097655646024197909897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220990796874194698930546529 165743097655646024197909897)
    ·
      refine ⟨124307323241734518148432423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165743097655646024197909897 124307323241734518148432423)
      ·
        refine ⟨186460984862601777222648635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124307323241734518148432423 186460984862601777222648635)
        ·
          refine ⟨279691477293902665833972953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186460984862601777222648635 279691477293902665833972953)
          ·
            refine ⟨209768607970426999375479715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279691477293902665833972953 209768607970426999375479715)
            ·
              refine ⟨314652911955640499063219573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209768607970426999375479715 314652911955640499063219573)
              ·
                refine ⟨29498710495841296787176835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314652911955640499063219573 29498710495841296787176835)
                ·
                  refine ⟨44248065743761945180765253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29498710495841296787176835 44248065743761945180765253)
                  ·
                    refine ⟨8296512326955364721393485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44248065743761945180765253 8296512326955364721393485)
                    ·
                      refine ⟨3111192122608261770522557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296512326955364721393485 3111192122608261770522557)
                      ·
                        rfl

theorem cell23_6059025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_6059025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059025 prefixEnd_6059025 := by exact prefixLift 6059025
  have htrace : WordTrace (prefixWord ++ tailWord_6059025) baseStart_6059025 baseEnd_6059025 := by
    simpa [prefixWord, tailWord_6059025, baseEnd_6059025] using wordTrace_append hprefix tailTrace_6059025
  have hstable : (prefixWord ++ tailWord_6059025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059025).length < 2 ^ (prefixWord ++ tailWord_6059025).sum := by decide
  have hdescent : baseEnd_6059025 < baseStart_6059025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059075 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 3, 5]
def baseStart_6059075 : Nat := 118140960795 + 6059075 * 2 ^ 59
def prefixEnd_6059075 : Nat := 4983230072969 + 3 ^ 40 * 6059075 * 2
def baseEnd_6059075 : Nat := 1037072598880328858299109

theorem tailTrace_6059075 : CollatzResearch.WordTrace tailWord_6059075 prefixEnd_6059075 1037072598880328858299109 := by
  unfold tailWord_6059075
  simp only [CollatzResearch.WordTrace]
  refine ⟨220992620524013557469866679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147328413682675704979911119 220992620524013557469866679)
  ·
    refine ⟨331488930786020336204800019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220992620524013557469866679 331488930786020336204800019)
    ·
      refine ⟨497233396179030504307200029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331488930786020336204800019 497233396179030504307200029)
      ·
        refine ⟨186462523567136439115200011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497233396179030504307200029 186462523567136439115200011)
        ·
          refine ⟨279693785350704658672800017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186462523567136439115200011 279693785350704658672800017)
          ·
            refine ⟨209770339013028494004600013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279693785350704658672800017 209770339013028494004600013)
            ·
              refine ⟨78663877129885685251725005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209770339013028494004600013 78663877129885685251725005)
              ·
                refine ⟨29498953923707131969396877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78663877129885685251725005 29498953923707131969396877)
                ·
                  refine ⟨11062107721390174488523829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29498953923707131969396877 11062107721390174488523829)
                  ·
                    refine ⟨1037072598880328858299109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11062107721390174488523829 1037072598880328858299109)
                    ·
                      rfl

theorem cell23_6059075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].length) (baseStart_6059075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059075 prefixEnd_6059075 := by exact prefixLift 6059075
  have htrace : WordTrace (prefixWord ++ tailWord_6059075) baseStart_6059075 baseEnd_6059075 := by
    simpa [prefixWord, tailWord_6059075, baseEnd_6059075] using wordTrace_append hprefix tailTrace_6059075
  have hstable : (prefixWord ++ tailWord_6059075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059075).length < 2 ^ (prefixWord ++ tailWord_6059075).sum := by decide
  have hdescent : baseEnd_6059075 < baseStart_6059075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059105 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_6059105 : Nat := 118140960795 + 6059105 * 2 ^ 59
def prefixEnd_6059105 : Nat := 4983230072969 + 3 ^ 40 * 6059105 * 2
def baseEnd_6059105 : Nat := 1037077733686873819174063

theorem tailTrace_6059105 : CollatzResearch.WordTrace tailWord_6059105 prefixEnd_6059105 1037077733686873819174063 := by
  unfold tailWord_6059105
  simp only [CollatzResearch.WordTrace]
  refine ⟨220993714713904872593458769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147329143142603248395639179 220993714713904872593458769)
  ·
    refine ⟨165745286035428654445094077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220993714713904872593458769 165745286035428654445094077)
    ·
      refine ⟨62154482263285745416910279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165745286035428654445094077 62154482263285745416910279)
      ·
        refine ⟨93231723394928618125365419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62154482263285745416910279 93231723394928618125365419)
        ·
          refine ⟨139847585092392927188048129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93231723394928618125365419 139847585092392927188048129)
          ·
            refine ⟨104885688819294695391036097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139847585092392927188048129 104885688819294695391036097)
            ·
              refine ⟨78664266614471021543277073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104885688819294695391036097 78664266614471021543277073)
              ·
                refine ⟨58998199960853266157457805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78664266614471021543277073 58998199960853266157457805)
                ·
                  refine ⟨22124324985319974809046677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58998199960853266157457805 22124324985319974809046677)
                  ·
                    refine ⟨1037077733686873819174063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22124324985319974809046677 1037077733686873819174063)
                    ·
                      rfl

theorem cell23_6059105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_6059105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059105 prefixEnd_6059105 := by exact prefixLift 6059105
  have htrace : WordTrace (prefixWord ++ tailWord_6059105) baseStart_6059105 baseEnd_6059105 := by
    simpa [prefixWord, tailWord_6059105, baseEnd_6059105] using wordTrace_append hprefix tailTrace_6059105
  have hstable : (prefixWord ++ tailWord_6059105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059105).length < 2 ^ (prefixWord ++ tailWord_6059105).sum := by decide
  have hdescent : baseEnd_6059105 < baseStart_6059105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059106 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6059106 : Nat := 118140960795 + 6059106 * 2 ^ 59
def prefixEnd_6059106 : Nat := 4983230072969 + 3 ^ 40 * 6059106 * 2
def baseEnd_6059106 : Nat := 3111233714541275953609685

theorem tailTrace_6059106 : CollatzResearch.WordTrace tailWord_6059106 prefixEnd_6059106 3111233714541275953609685 := by
  unfold tailWord_6059106
  simp only [CollatzResearch.WordTrace]
  refine ⟨55248437796725312441061293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147329167457934166509496781 55248437796725312441061293)
  ·
    refine ⟨20718164173771992165397985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55248437796725312441061293 20718164173771992165397985)
    ·
      refine ⟨15538623130328994124048489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20718164173771992165397985 15538623130328994124048489)
      ·
        refine ⟨11653967347746745593036367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15538623130328994124048489 11653967347746745593036367)
        ·
          refine ⟨17480951021620118389554551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11653967347746745593036367 17480951021620118389554551)
          ·
            refine ⟨26221426532430177584331827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17480951021620118389554551 26221426532430177584331827)
            ·
              refine ⟨39332139798645266376497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26221426532430177584331827 39332139798645266376497741)
              ·
                refine ⟨14749552424491974891186653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39332139798645266376497741 14749552424491974891186653)
                ·
                  refine ⟨5531082159184490584194995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14749552424491974891186653 5531082159184490584194995)
                  ·
                    refine ⟨8296623238776735876292493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531082159184490584194995 8296623238776735876292493)
                    ·
                      refine ⟨3111233714541275953609685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8296623238776735876292493 3111233714541275953609685)
                      ·
                        rfl

theorem cell23_6059106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6059106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059106 prefixEnd_6059106 := by exact prefixLift 6059106
  have htrace : WordTrace (prefixWord ++ tailWord_6059106) baseStart_6059106 baseEnd_6059106 := by
    simpa [prefixWord, tailWord_6059106, baseEnd_6059106] using wordTrace_append hprefix tailTrace_6059106
  have hstable : (prefixWord ++ tailWord_6059106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059106).length < 2 ^ (prefixWord ++ tailWord_6059106).sum := by decide
  have hdescent : baseEnd_6059106 < baseStart_6059106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059134 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6059134 : Nat := 118140960795 + 6059134 * 2 ^ 59
def prefixEnd_6059134 : Nat := 4983230072969 + 3 ^ 40 * 6059134 * 2
def baseEnd_6059134 : Nat := 1037082697333200614686519

theorem tailTrace_6059134 : CollatzResearch.WordTrace tailWord_6059134 prefixEnd_6059134 1037082697333200614686519 := by
  unfold tailWord_6059134
  simp only [CollatzResearch.WordTrace]
  refine ⟨27624346553849976318283057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147329848287199873697509637 27624346553849976318283057)
  ·
    refine ⟨20718259915387482238712293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27624346553849976318283057 20718259915387482238712293)
    ·
      refine ⟨3884673734135152919758555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20718259915387482238712293 3884673734135152919758555)
      ·
        refine ⟨5827010601202729379637833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884673734135152919758555 5827010601202729379637833)
        ·
          refine ⟨4370257950902047034728375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827010601202729379637833 4370257950902047034728375)
          ·
            refine ⟨6555386926353070552092563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370257950902047034728375 6555386926353070552092563)
            ·
              refine ⟨9833080389529605828138845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555386926353070552092563 9833080389529605828138845)
              ·
                refine ⟨3687405146073602185552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9833080389529605828138845 3687405146073602185552067)
                ·
                  refine ⟨5531107719110403278328101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687405146073602185552067 5531107719110403278328101)
                  ·
                    refine ⟨1037082697333200614686519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5531107719110403278328101 1037082697333200614686519)
                    ·
                      rfl

theorem cell23_6059134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6059134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059134 prefixEnd_6059134 := by exact prefixLift 6059134
  have htrace : WordTrace (prefixWord ++ tailWord_6059134) baseStart_6059134 baseEnd_6059134 := by
    simpa [prefixWord, tailWord_6059134, baseEnd_6059134] using wordTrace_append hprefix tailTrace_6059134
  have hstable : (prefixWord ++ tailWord_6059134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059134).length < 2 ^ (prefixWord ++ tailWord_6059134).sum := by decide
  have hdescent : baseEnd_6059134 < baseStart_6059134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059195 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 8]
def baseStart_6059195 : Nat := 118140960795 + 6059195 * 2 ^ 59
def prefixEnd_6059195 : Nat := 4983230072969 + 3 ^ 40 * 6059195 * 2
def baseEnd_6059195 : Nat := 1037093138106508701798925

theorem tailTrace_6059195 : CollatzResearch.WordTrace tailWord_6059195 prefixEnd_6059195 1037093138106508701798925 := by
  unfold tailWord_6059195
  simp only [CollatzResearch.WordTrace]
  refine ⟨220996997283578817964235039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147331331522385878642823359 220996997283578817964235039)
  ·
    refine ⟨331495495925368226946352559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220996997283578817964235039 331495495925368226946352559)
    ·
      refine ⟨497243243888052340419528839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331495495925368226946352559 497243243888052340419528839)
      ·
        refine ⟨745864865832078510629293259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497243243888052340419528839 745864865832078510629293259)
        ·
          refine ⟨1118797298748117765943939889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745864865832078510629293259 1118797298748117765943939889)
          ·
            refine ⟨839097974061088324457954917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118797298748117765943939889 839097974061088324457954917)
            ·
              refine ⟨157330870136454060835866547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 839097974061088324457954917 157330870136454060835866547)
              ·
                refine ⟨235996305204681091253799821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157330870136454060835866547 235996305204681091253799821)
                ·
                  refine ⟨88498614451755409220174933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235996305204681091253799821 88498614451755409220174933)
                  ·
                    refine ⟨1037093138106508701798925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88498614451755409220174933 1037093138106508701798925)
                    ·
                      rfl

theorem cell23_6059195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_6059195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059195 prefixEnd_6059195 := by exact prefixLift 6059195
  have htrace : WordTrace (prefixWord ++ tailWord_6059195) baseStart_6059195 baseEnd_6059195 := by
    simpa [prefixWord, tailWord_6059195, baseEnd_6059195] using wordTrace_append hprefix tailTrace_6059195
  have hstable : (prefixWord ++ tailWord_6059195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059195).length < 2 ^ (prefixWord ++ tailWord_6059195).sum := by decide
  have hdescent : baseEnd_6059195 < baseStart_6059195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059214 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_6059214 : Nat := 118140960795 + 6059214 * 2 ^ 59
def prefixEnd_6059214 : Nat := 4983230072969 + 3 ^ 40 * 6059214 * 2
def baseEnd_6059214 : Nat := 3111289170451961531059189

theorem tailTrace_6059214 : CollatzResearch.WordTrace tailWord_6059214 prefixEnd_6059214 3111289170451961531059189 := by
  unfold tailWord_6059214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27624711283813748026147087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147331793513673322806117797 27624711283813748026147087)
  ·
    refine ⟨41437066925720622039220631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27624711283813748026147087 41437066925720622039220631)
    ·
      refine ⟨62155600388580933058830947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41437066925720622039220631 62155600388580933058830947)
      ·
        refine ⟨93233400582871399588246421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62155600388580933058830947 93233400582871399588246421)
        ·
          refine ⟨4370315652322096855699051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 93233400582871399588246421 4370315652322096855699051)
          ·
            refine ⟨6555473478483145283548577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370315652322096855699051 6555473478483145283548577)
            ·
              refine ⟨4916605108862358962661433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6555473478483145283548577 4916605108862358962661433)
              ·
                refine ⟨3687453831646769221996075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916605108862358962661433 3687453831646769221996075)
                ·
                  refine ⟨5531180747470153832994113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687453831646769221996075 5531180747470153832994113)
                  ·
                    refine ⟨4148385560602615374745585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5531180747470153832994113 4148385560602615374745585)
                    ·
                      refine ⟨3111289170451961531059189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148385560602615374745585 3111289170451961531059189)
                      ·
                        rfl

theorem cell23_6059214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_6059214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059214 prefixEnd_6059214 := by exact prefixLift 6059214
  have htrace : WordTrace (prefixWord ++ tailWord_6059214) baseStart_6059214 baseEnd_6059214 := by
    simpa [prefixWord, tailWord_6059214, baseEnd_6059214] using wordTrace_append hprefix tailTrace_6059214
  have hstable : (prefixWord ++ tailWord_6059214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059214).length < 2 ^ (prefixWord ++ tailWord_6059214).sum := by decide
  have hdescent : baseEnd_6059214 < baseStart_6059214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059232 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_6059232 : Nat := 118140960795 + 6059232 * 2 ^ 59
def prefixEnd_6059232 : Nat := 4983230072969 + 3 ^ 40 * 6059232 * 2
def baseEnd_6059232 : Nat := 3111298413103742460634105

theorem tailTrace_6059232 : CollatzResearch.WordTrace tailWord_6059232 prefixEnd_6059232 3111298413103742460634105 := by
  unfold tailWord_6059232
  simp only [CollatzResearch.WordTrace]
  refine ⟨110499173392222386641665975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147332231189629848855554633 110499173392222386641665975)
  ·
    refine ⟨165748760088333579962498963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110499173392222386641665975 165748760088333579962498963)
    ·
      refine ⟨248623140132500369943748445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165748760088333579962498963 248623140132500369943748445)
      ·
        refine ⟨93233677549687638728905667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248623140132500369943748445 93233677549687638728905667)
        ·
          refine ⟨139850516324531458093358501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93233677549687638728905667 139850516324531458093358501)
          ·
            refine ⟨26221971810849648392504719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139850516324531458093358501 26221971810849648392504719)
            ·
              refine ⟨39332957716274472588757079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26221971810849648392504719 39332957716274472588757079)
              ·
                refine ⟨58999436574411708883135619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39332957716274472588757079 58999436574411708883135619)
                ·
                  refine ⟨88499154861617563324703429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58999436574411708883135619 88499154861617563324703429)
                  ·
                    refine ⟨16593591536553293123381893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88499154861617563324703429 16593591536553293123381893)
                    ·
                      refine ⟨3111298413103742460634105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16593591536553293123381893 3111298413103742460634105)
                      ·
                        rfl

theorem cell23_6059232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_6059232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059232 prefixEnd_6059232 := by exact prefixLift 6059232
  have htrace : WordTrace (prefixWord ++ tailWord_6059232) baseStart_6059232 baseEnd_6059232 := by
    simpa [prefixWord, tailWord_6059232, baseEnd_6059232] using wordTrace_append hprefix tailTrace_6059232
  have hstable : (prefixWord ++ tailWord_6059232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059232).length < 2 ^ (prefixWord ++ tailWord_6059232).sum := by decide
  have hdescent : baseEnd_6059232 < baseStart_6059232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059242 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_6059242 : Nat := 118140960795 + 6059242 * 2 ^ 59
def prefixEnd_6059242 : Nat := 4983230072969 + 3 ^ 40 * 6059242 * 2
def baseEnd_6059242 : Nat := 345700394212254157945451

theorem tailTrace_6059242 : CollatzResearch.WordTrace tailWord_6059242 prefixEnd_6059242 345700394212254157945451 := by
  unfold tailWord_6059242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55249677878602136247798995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147332474342939029994130653 55249677878602136247798995)
  ·
    refine ⟨82874516817903204371698493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55249677878602136247798995 82874516817903204371698493)
    ·
      refine ⟨31077943806713701639386935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82874516817903204371698493 31077943806713701639386935)
      ·
        refine ⟨46616915710070552459080403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31077943806713701639386935 46616915710070552459080403)
        ·
          refine ⟨69925373565105828688620605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46616915710070552459080403 69925373565105828688620605)
          ·
            refine ⟨26222015086914685758232727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69925373565105828688620605 26222015086914685758232727)
            ·
              refine ⟨39333022630372028637349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26222015086914685758232727 39333022630372028637349091)
              ·
                refine ⟨58999533945558042956023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39333022630372028637349091 58999533945558042956023637)
                ·
                  refine ⟨345700394212254157945451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58999533945558042956023637 345700394212254157945451)
                  ·
                    rfl

theorem cell23_6059242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_6059242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059242 prefixEnd_6059242 := by exact prefixLift 6059242
  have htrace : WordTrace (prefixWord ++ tailWord_6059242) baseStart_6059242 baseEnd_6059242 := by
    simpa [prefixWord, tailWord_6059242, baseEnd_6059242] using wordTrace_append hprefix tailTrace_6059242
  have hstable : (prefixWord ++ tailWord_6059242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059242).length < 2 ^ (prefixWord ++ tailWord_6059242).sum := by decide
  have hdescent : baseEnd_6059242 < baseStart_6059242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059326 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6059326 : Nat := 118140960795 + 6059326 * 2 ^ 59
def prefixEnd_6059326 : Nat := 4983230072969 + 3 ^ 40 * 6059326 * 2
def baseEnd_6059326 : Nat := 3111346680285265092858673

theorem tailTrace_6059326 : CollatzResearch.WordTrace tailWord_6059326 prefixEnd_6059326 3111346680285265092858673 := by
  unfold tailWord_6059326
  simp only [CollatzResearch.WordTrace]
  refine ⟨27625221905763028417156729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147334516830736151558169221 27625221905763028417156729)
  ·
    refine ⟨20718916429322271312867547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27625221905763028417156729 20718916429322271312867547)
    ·
      refine ⟨31078374643983406969301321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20718916429322271312867547 31078374643983406969301321)
      ·
        refine ⟨23308780982987555226975991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31078374643983406969301321 23308780982987555226975991)
        ·
          refine ⟨34963171474481332840463987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23308780982987555226975991 34963171474481332840463987)
          ·
            refine ⟨52444757211721999260695981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34963171474481332840463987 52444757211721999260695981)
            ·
              refine ⟨19666783954395749722760993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52444757211721999260695981 19666783954395749722760993)
              ·
                refine ⟨14750087965796812292070745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19666783954395749722760993 14750087965796812292070745)
                ·
                  refine ⟨11062565974347609219053059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14750087965796812292070745 11062565974347609219053059)
                  ·
                    refine ⟨16593848961521413828579589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11062565974347609219053059 16593848961521413828579589)
                    ·
                      refine ⟨3111346680285265092858673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16593848961521413828579589 3111346680285265092858673)
                      ·
                        rfl

theorem cell23_6059326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6059326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059326 prefixEnd_6059326 := by exact prefixLift 6059326
  have htrace : WordTrace (prefixWord ++ tailWord_6059326) baseStart_6059326 baseEnd_6059326 := by
    simpa [prefixWord, tailWord_6059326, baseEnd_6059326] using wordTrace_append hprefix tailTrace_6059326
  have hstable : (prefixWord ++ tailWord_6059326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059326).length < 2 ^ (prefixWord ++ tailWord_6059326).sum := by decide
  have hdescent : baseEnd_6059326 < baseStart_6059326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059420 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6059420 : Nat := 118140960795 + 6059420 * 2 ^ 59
def prefixEnd_6059420 : Nat := 4983230072969 + 3 ^ 40 * 6059420 * 2
def baseEnd_6059420 : Nat := 3111394947466787725083241

theorem tailTrace_6059420 : CollatzResearch.WordTrace tailWord_6059420 prefixEnd_6059420 3111394947466787725083241 := by
  unfold tailWord_6059420
  simp only [CollatzResearch.WordTrace]
  refine ⟨110502601853881840695587857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147336802471842454260783809 110502601853881840695587857)
  ·
    refine ⟨82876951390411380521690893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110502601853881840695587857 82876951390411380521690893)
    ·
      refine ⟨31078856771404267695634085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82876951390411380521690893 31078856771404267695634085)
      ·
        refine ⟨5827285644638300192931391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31078856771404267695634085 5827285644638300192931391)
        ·
          refine ⟨8740928466957450289397087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827285644638300192931391 8740928466957450289397087)
          ·
            refine ⟨13111392700436175434095631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740928466957450289397087 13111392700436175434095631)
            ·
              refine ⟨19667089050654263151143447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13111392700436175434095631 19667089050654263151143447)
              ·
                refine ⟨29500633575981394726715171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19667089050654263151143447 29500633575981394726715171)
                ·
                  refine ⟨44250950363972092090072757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29500633575981394726715171 44250950363972092090072757)
                  ·
                    refine ⟨4148526596622383633444321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44250950363972092090072757 4148526596622383633444321)
                    ·
                      refine ⟨3111394947466787725083241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148526596622383633444321 3111394947466787725083241)
                      ·
                        rfl

theorem cell23_6059420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6059420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059420 prefixEnd_6059420 := by exact prefixLift 6059420
  have htrace : WordTrace (prefixWord ++ tailWord_6059420) baseStart_6059420 baseEnd_6059420 := by
    simpa [prefixWord, tailWord_6059420, baseEnd_6059420] using wordTrace_append hprefix tailTrace_6059420
  have hstable : (prefixWord ++ tailWord_6059420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059420).length < 2 ^ (prefixWord ++ tailWord_6059420).sum := by decide
  have hdescent : baseEnd_6059420 < baseStart_6059420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059426 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6059426 : Nat := 118140960795 + 6059426 * 2 ^ 59
def prefixEnd_6059426 : Nat := 4983230072969 + 3 ^ 40 * 6059426 * 2
def baseEnd_6059426 : Nat := 1037132676116904900536071

theorem tailTrace_6059426 : CollatzResearch.WordTrace tailWord_6059426 prefixEnd_6059426 1037132676116904900536071 := by
  unfold tailWord_6059426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55251355636435486103973533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147336948363827962943929421 55251355636435486103973533)
  ·
    refine ⟨20719258363663307288990075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55251355636435486103973533 20719258363663307288990075)
    ·
      refine ⟨31078887545494960933485113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20719258363663307288990075 31078887545494960933485113)
      ·
        refine ⟨23309165659121220700113835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31078887545494960933485113 23309165659121220700113835)
        ·
          refine ⟨34963748488681831050170753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23309165659121220700113835 34963748488681831050170753)
          ·
            refine ⟨26222811366511373287628065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34963748488681831050170753 26222811366511373287628065)
            ·
              refine ⟨19667108524883529965721049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26222811366511373287628065 19667108524883529965721049)
              ·
                refine ⟨14750331393662647474290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19667108524883529965721049 14750331393662647474290787)
                ·
                  refine ⟨22125497090493971211436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14750331393662647474290787 22125497090493971211436181)
                  ·
                    refine ⟨1037132676116904900536071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22125497090493971211436181 1037132676116904900536071)
                    ·
                      rfl

theorem cell23_6059426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6059426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059426 prefixEnd_6059426 := by exact prefixLift 6059426
  have htrace : WordTrace (prefixWord ++ tailWord_6059426) baseStart_6059426 baseEnd_6059426 := by
    simpa [prefixWord, tailWord_6059426, baseEnd_6059426] using wordTrace_append hprefix tailTrace_6059426
  have hstable : (prefixWord ++ tailWord_6059426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059426).length < 2 ^ (prefixWord ++ tailWord_6059426).sum := by decide
  have hdescent : baseEnd_6059426 < baseStart_6059426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059429 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_6059429 : Nat := 118140960795 + 6059429 * 2 ^ 59
def prefixEnd_6059429 : Nat := 4983230072969 + 3 ^ 40 * 6059429 * 2
def baseEnd_6059429 : Nat := 3111399568792678189870699

theorem tailTrace_6059429 : CollatzResearch.WordTrace tailWord_6059429 prefixEnd_6059429 3111399568792678189870699 := by
  unfold tailWord_6059429
  simp only [CollatzResearch.WordTrace]
  refine ⟨221005531964731075928253341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147337021309820717285502227 221005531964731075928253341)
  ·
    refine ⟨82877074486774153473095003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221005531964731075928253341 82877074486774153473095003)
    ·
      refine ⟨124315611730161230209642505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82877074486774153473095003 124315611730161230209642505)
      ·
        refine ⟨93236708797620922657231879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124315611730161230209642505 93236708797620922657231879)
        ·
          refine ⟨139855063196431383985847819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93236708797620922657231879 139855063196431383985847819)
          ·
            refine ⟨209782594794647075978771729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139855063196431383985847819 209782594794647075978771729)
            ·
              refine ⟨157336946095985306984078797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209782594794647075978771729 157336946095985306984078797)
              ·
                refine ⟨59001354785994490119029549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157336946095985306984078797 59001354785994490119029549)
                ·
                  refine ⟨22125508044747933794636081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59001354785994490119029549 22125508044747933794636081)
                  ·
                    refine ⟨16594131033560950345977061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22125508044747933794636081 16594131033560950345977061)
                    ·
                      refine ⟨3111399568792678189870699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16594131033560950345977061 3111399568792678189870699)
                      ·
                        rfl

theorem cell23_6059429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_6059429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059429 prefixEnd_6059429 := by exact prefixLift 6059429
  have htrace : WordTrace (prefixWord ++ tailWord_6059429) baseStart_6059429 baseEnd_6059429 := by
    simpa [prefixWord, tailWord_6059429, baseEnd_6059429] using wordTrace_append hprefix tailTrace_6059429
  have hstable : (prefixWord ++ tailWord_6059429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059429).length < 2 ^ (prefixWord ++ tailWord_6059429).sum := by decide
  have hdescent : baseEnd_6059429 < baseStart_6059429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059499 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 6]
def baseStart_6059499 : Nat := 118140960795 + 6059499 * 2 ^ 59
def prefixEnd_6059499 : Nat := 4983230072969 + 3 ^ 40 * 6059499 * 2
def baseEnd_6059499 : Nat := 1037145170812830971998459

theorem tailTrace_6059499 : CollatzResearch.WordTrace tailWord_6059499 prefixEnd_6059499 1037145170812830971998459 := by
  unfold tailWord_6059499
  simp only [CollatzResearch.WordTrace]
  refine ⟨221008085074477477883301551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147338723382984985255534367 221008085074477477883301551)
  ·
    refine ⟨331512127611716216824952327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221008085074477477883301551 331512127611716216824952327)
    ·
      refine ⟨497268191417574325237428491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331512127611716216824952327 497268191417574325237428491)
      ·
        refine ⟨745902287126361487856142737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497268191417574325237428491 745902287126361487856142737)
        ·
          refine ⟨559426715344771115892107053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745902287126361487856142737 559426715344771115892107053)
          ·
            refine ⟨209785018254289168459540145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559426715344771115892107053 209785018254289168459540145)
            ·
              refine ⟨157338763690716876344655109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209785018254289168459540145 157338763690716876344655109)
              ·
                refine ⟨29501018192009414314622833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157338763690716876344655109 29501018192009414314622833)
                ·
                  refine ⟨22125763644007060735967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29501018192009414314622833 22125763644007060735967125)
                  ·
                    refine ⟨1037145170812830971998459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22125763644007060735967125 1037145170812830971998459)
                    ·
                      rfl

theorem cell23_6059499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_6059499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059499 prefixEnd_6059499 := by exact prefixLift 6059499
  have htrace : WordTrace (prefixWord ++ tailWord_6059499) baseStart_6059499 baseEnd_6059499 := by
    simpa [prefixWord, tailWord_6059499, baseEnd_6059499] using wordTrace_append hprefix tailTrace_6059499
  have hstable : (prefixWord ++ tailWord_6059499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059499).length < 2 ^ (prefixWord ++ tailWord_6059499).sum := by decide
  have hdescent : baseEnd_6059499 < baseStart_6059499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059501 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6059501 : Nat := 118140960795 + 6059501 * 2 ^ 59
def prefixEnd_6059501 : Nat := 4983230072969 + 3 ^ 40 * 6059501 * 2
def baseEnd_6059501 : Nat := 3111436539399801908170369

theorem tailTrace_6059501 : CollatzResearch.WordTrace tailWord_6059501 prefixEnd_6059501 3111436539399801908170369 := by
  unfold tailWord_6059501
  simp only [CollatzResearch.WordTrace]
  refine ⟨221008158020470232224874357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147338772013646821483249571 221008158020470232224874357)
  ·
    refine ⟨20719514814419084271081971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221008158020470232224874357 20719514814419084271081971)
    ·
      refine ⟨31079272221628626406622957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20719514814419084271081971 31079272221628626406622957)
      ·
        refine ⟨11654727083110734902483609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31079272221628626406622957 11654727083110734902483609)
        ·
          refine ⟨8741045312333051176862707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11654727083110734902483609 8741045312333051176862707)
          ·
            refine ⟨13111567968499576765294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741045312333051176862707 13111567968499576765294061)
            ·
              refine ⟨4916837988187341286985273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13111567968499576765294061 4916837988187341286985273)
              ·
                refine ⟨3687628491140505965238955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916837988187341286985273 3687628491140505965238955)
                ·
                  refine ⟨5531442736710758947858433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687628491140505965238955 5531442736710758947858433)
                  ·
                    refine ⟨4148582052533069210893825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5531442736710758947858433 4148582052533069210893825)
                    ·
                      refine ⟨3111436539399801908170369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148582052533069210893825 3111436539399801908170369)
                      ·
                        rfl

theorem cell23_6059501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6059501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059501 prefixEnd_6059501 := by exact prefixLift 6059501
  have htrace : WordTrace (prefixWord ++ tailWord_6059501) baseStart_6059501 baseEnd_6059501 := by
    simpa [prefixWord, tailWord_6059501, baseEnd_6059501] using wordTrace_append hprefix tailTrace_6059501
  have hstable : (prefixWord ++ tailWord_6059501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059501).length < 2 ^ (prefixWord ++ tailWord_6059501).sum := by decide
  have hdescent : baseEnd_6059501 < baseStart_6059501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059517 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_6059517 : Nat := 118140960795 + 6059517 * 2 ^ 59
def prefixEnd_6059517 : Nat := 4983230072969 + 3 ^ 40 * 6059517 * 2
def baseEnd_6059517 : Nat := 3111444755090273845570295

theorem tailTrace_6059517 : CollatzResearch.WordTrace tailWord_6059517 prefixEnd_6059517 3111444755090273845570295 := by
  unfold tailWord_6059517
  simp only [CollatzResearch.WordTrace]
  refine ⟨221008741588412266957456805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147339161058941511304971203 221008741588412266957456805)
  ·
    refine ⟨41439139047827300054523151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221008741588412266957456805 41439139047827300054523151)
    ·
      refine ⟨62158708571740950081784727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41439139047827300054523151 62158708571740950081784727)
      ·
        refine ⟨93238062857611425122677091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62158708571740950081784727 93238062857611425122677091)
        ·
          refine ⟨139857094286417137684015637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93238062857611425122677091 139857094286417137684015637)
          ·
            refine ⟨6555801294675803328938233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139857094286417137684015637 6555801294675803328938233)
            ·
              refine ⟨4916850971006852496703675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6555801294675803328938233 4916850971006852496703675)
              ·
                refine ⟨7375276456510278745055513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916850971006852496703675 7375276456510278745055513)
                ·
                  refine ⟨5531457342382709058791635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375276456510278745055513 5531457342382709058791635)
                  ·
                    refine ⟨8297186013574063588187453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531457342382709058791635 8297186013574063588187453)
                    ·
                      refine ⟨3111444755090273845570295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297186013574063588187453 3111444755090273845570295)
                      ·
                        rfl

theorem cell23_6059517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_6059517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059517 prefixEnd_6059517 := by exact prefixLift 6059517
  have htrace : WordTrace (prefixWord ++ tailWord_6059517) baseStart_6059517 baseEnd_6059517 := by
    simpa [prefixWord, tailWord_6059517, baseEnd_6059517] using wordTrace_append hprefix tailTrace_6059517
  have hstable : (prefixWord ++ tailWord_6059517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059517).length < 2 ^ (prefixWord ++ tailWord_6059517).sum := by decide
  have hdescent : baseEnd_6059517 < baseStart_6059517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059523 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 6, 2, 2]
def baseStart_6059523 : Nat := 118140960795 + 6059523 * 2 ^ 59
def prefixEnd_6059523 : Nat := 4983230072969 + 3 ^ 40 * 6059523 * 2
def baseEnd_6059523 : Nat := 3111447835974200822095267

theorem tailTrace_6059523 : CollatzResearch.WordTrace tailWord_6059523 prefixEnd_6059523 3111447835974200822095267 := by
  unfold tailWord_6059523
  simp only [CollatzResearch.WordTrace]
  refine ⟨221008960426390529982175223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147339306950927019988116815 221008960426390529982175223)
  ·
    refine ⟨331513440639585794973262835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221008960426390529982175223 331513440639585794973262835)
    ·
      refine ⟨497270160959378692459894253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331513440639585794973262835 497270160959378692459894253)
      ·
        refine ⟨186476310359767009672460345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497270160959378692459894253 186476310359767009672460345)
        ·
          refine ⟨139857232769825257254345259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186476310359767009672460345 139857232769825257254345259)
          ·
            refine ⟨209785849154737885881517889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139857232769825257254345259 209785849154737885881517889)
            ·
              refine ⟨157339386866053414411138417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209785849154737885881517889 157339386866053414411138417)
              ·
                refine ⟨118004540149540060808353813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157339386866053414411138417 118004540149540060808353813)
                ·
                  refine ⟨5531462819509690350391585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118004540149540060808353813 5531462819509690350391585)
                  ·
                    refine ⟨4148597114632267762793689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5531462819509690350391585 4148597114632267762793689)
                    ·
                      refine ⟨3111447835974200822095267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148597114632267762793689 3111447835974200822095267)
                      ·
                        rfl

theorem cell23_6059523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_6059523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059523 prefixEnd_6059523 := by exact prefixLift 6059523
  have htrace : WordTrace (prefixWord ++ tailWord_6059523) baseStart_6059523 baseEnd_6059523 := by
    simpa [prefixWord, tailWord_6059523, baseEnd_6059523] using wordTrace_append hprefix tailTrace_6059523
  have hstable : (prefixWord ++ tailWord_6059523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059523).length < 2 ^ (prefixWord ++ tailWord_6059523).sum := by decide
  have hdescent : baseEnd_6059523 < baseStart_6059523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059527 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6059527 : Nat := 118140960795 + 6059527 * 2 ^ 59
def prefixEnd_6059527 : Nat := 4983230072969 + 3 ^ 40 * 6059527 * 2
def baseEnd_6059527 : Nat := 3111449889896818806445249

theorem tailTrace_6059527 : CollatzResearch.WordTrace tailWord_6059527 prefixEnd_6059527 3111449889896818806445249 := by
  unfold tailWord_6059527
  simp only [CollatzResearch.WordTrace]
  refine ⟨221009106318376038665320835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147339404212250692443547223 221009106318376038665320835)
  ·
    refine ⟨331513659477564057997981253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221009106318376038665320835 331513659477564057997981253)
    ·
      refine ⟨62158811152043260874621485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331513659477564057997981253 62158811152043260874621485)
      ·
        refine ⟨23309554182016222827983057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62158811152043260874621485 23309554182016222827983057)
        ·
          refine ⟨17482165636512167120987293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23309554182016222827983057 17482165636512167120987293)
          ·
            refine ⟨6555812113692062670370235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17482165636512167120987293 6555812113692062670370235)
            ·
              refine ⟨9833718170538094005555353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555812113692062670370235 9833718170538094005555353)
              ·
                refine ⟨7375288627903570504166515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9833718170538094005555353 7375288627903570504166515)
                ·
                  refine ⟨11062932941855355756249773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375288627903570504166515 11062932941855355756249773)
                  ·
                    refine ⟨4148599853195758408593665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11062932941855355756249773 4148599853195758408593665)
                    ·
                      refine ⟨3111449889896818806445249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148599853195758408593665 3111449889896818806445249)
                      ·
                        rfl

theorem cell23_6059527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6059527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059527 prefixEnd_6059527 := by exact prefixLift 6059527
  have htrace : WordTrace (prefixWord ++ tailWord_6059527) baseStart_6059527 baseEnd_6059527 := by
    simpa [prefixWord, tailWord_6059527, baseEnd_6059527] using wordTrace_append hprefix tailTrace_6059527
  have hstable : (prefixWord ++ tailWord_6059527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059527).length < 2 ^ (prefixWord ++ tailWord_6059527).sum := by decide
  have hdescent : baseEnd_6059527 < baseStart_6059527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059529 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 9]
def baseStart_6059529 : Nat := 118140960795 + 6059529 * 2 ^ 59
def prefixEnd_6059529 : Nat := 4983230072969 + 3 ^ 40 * 6059529 * 2
def baseEnd_6059529 : Nat := 345716768539791977624471

theorem tailTrace_6059529 : CollatzResearch.WordTrace tailWord_6059529 prefixEnd_6059529 345716768539791977624471 := by
  unfold tailWord_6059529
  simp only [CollatzResearch.WordTrace]
  refine ⟨221009179264368793006893641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147339452842912528671262427 221009179264368793006893641)
  ·
    refine ⟨165756884448276594755170231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221009179264368793006893641 165756884448276594755170231)
    ·
      refine ⟨248635326672414892132755347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165756884448276594755170231 248635326672414892132755347)
      ·
        refine ⟨372952990008622338199133021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248635326672414892132755347 372952990008622338199133021)
        ·
          refine ⟨139857371253233376824674883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372952990008622338199133021 139857371253233376824674883)
          ·
            refine ⟨209786056879850065237012325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139857371253233376824674883 209786056879850065237012325)
            ·
              refine ⟨39334885664971887231939811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209786056879850065237012325 39334885664971887231939811)
              ·
                refine ⟨59002328497457830847909717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39334885664971887231939811 59002328497457830847909717)
                ·
                  refine ⟨345716768539791977624471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59002328497457830847909717 345716768539791977624471)
                  ·
                    rfl

theorem cell23_6059529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_6059529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059529 prefixEnd_6059529 := by exact prefixLift 6059529
  have htrace : WordTrace (prefixWord ++ tailWord_6059529) baseStart_6059529 baseEnd_6059529 := by
    simpa [prefixWord, tailWord_6059529, baseEnd_6059529] using wordTrace_append hprefix tailTrace_6059529
  have hstable : (prefixWord ++ tailWord_6059529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059529).length < 2 ^ (prefixWord ++ tailWord_6059529).sum := by decide
  have hdescent : baseEnd_6059529 < baseStart_6059529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059573 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_6059573 : Nat := 118140960795 + 6059573 * 2 ^ 59
def prefixEnd_6059573 : Nat := 4983230072969 + 3 ^ 40 * 6059573 * 2
def baseEnd_6059573 : Nat := 3111473510006925626470037

theorem tailTrace_6059573 : CollatzResearch.WordTrace tailWord_6059573 prefixEnd_6059573 3111473510006925626470037 := by
  unfold tailWord_6059573
  simp only [CollatzResearch.WordTrace]
  refine ⟨221010784076209388521495373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147340522717472925680996915 221010784076209388521495373)
  ·
    refine ⟨82879044028578520695560765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221010784076209388521495373 82879044028578520695560765)
    ·
      refine ⟨31079641510716945260835287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82879044028578520695560765 31079641510716945260835287)
      ·
        refine ⟨46619462266075417891252931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079641510716945260835287 46619462266075417891252931)
        ·
          refine ⟨69929193399113126836879397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46619462266075417891252931 69929193399113126836879397)
          ·
            refine ⟨13111723762333711281914887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69929193399113126836879397 13111723762333711281914887)
            ·
              refine ⟨19667585643500566922872331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13111723762333711281914887 19667585643500566922872331)
              ·
                refine ⟨29501378465250850384308497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19667585643500566922872331 29501378465250850384308497)
                ·
                  refine ⟨22126033848938137788231373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29501378465250850384308497 22126033848938137788231373)
                  ·
                    refine ⟨8297262693351801670586765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22126033848938137788231373 8297262693351801670586765)
                    ·
                      refine ⟨3111473510006925626470037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297262693351801670586765 3111473510006925626470037)
                      ·
                        rfl

theorem cell23_6059573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_6059573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059573 prefixEnd_6059573 := by exact prefixLift 6059573
  have htrace : WordTrace (prefixWord ++ tailWord_6059573) baseStart_6059573 baseEnd_6059573 := by
    simpa [prefixWord, tailWord_6059573, baseEnd_6059573] using wordTrace_append hprefix tailTrace_6059573
  have hstable : (prefixWord ++ tailWord_6059573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059573).length < 2 ^ (prefixWord ++ tailWord_6059573).sum := by decide
  have hdescent : baseEnd_6059573 < baseStart_6059573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059579 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_6059579 : Nat := 118140960795 + 6059579 * 2 ^ 59
def prefixEnd_6059579 : Nat := 4983230072969 + 3 ^ 40 * 6059579 * 2
def baseEnd_6059579 : Nat := 3111476590890852602995009

theorem tailTrace_6059579 : CollatzResearch.WordTrace tailWord_6059579 prefixEnd_6059579 3111476590890852602995009 := by
  unfold tailWord_6059579
  simp only [CollatzResearch.WordTrace]
  refine ⟨221011002914187651546213791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147340668609458434364142527 221011002914187651546213791)
  ·
    refine ⟨331516504371281477319320687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221011002914187651546213791 331516504371281477319320687)
    ·
      refine ⟨497274756556922215978981031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331516504371281477319320687 497274756556922215978981031)
      ·
        refine ⟨745912134835383323968471547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497274756556922215978981031 745912134835383323968471547)
        ·
          refine ⟨1118868202253074985952707321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745912134835383323968471547 1118868202253074985952707321)
          ·
            refine ⟨839151151689806239464530491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118868202253074985952707321 839151151689806239464530491)
            ·
              refine ⟨1258726727534709359196795737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839151151689806239464530491 1258726727534709359196795737)
              ·
                refine ⟨944045045651032019397596803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258726727534709359196795737 944045045651032019397596803)
                ·
                  refine ⟨1416067568476548029096395205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944045045651032019397596803 1416067568476548029096395205)
                  ·
                    refine ⟨265512669089352755455574101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1416067568476548029096395205 265512669089352755455574101)
                    ·
                      refine ⟨3111476590890852602995009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265512669089352755455574101 3111476590890852602995009)
                      ·
                        rfl

theorem cell23_6059579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_6059579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059579 prefixEnd_6059579 := by exact prefixLift 6059579
  have htrace : WordTrace (prefixWord ++ tailWord_6059579) baseStart_6059579 baseEnd_6059579 := by
    simpa [prefixWord, tailWord_6059579, baseEnd_6059579] using wordTrace_append hprefix tailTrace_6059579
  have hstable : (prefixWord ++ tailWord_6059579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059579).length < 2 ^ (prefixWord ++ tailWord_6059579).sum := by decide
  have hdescent : baseEnd_6059579 < baseStart_6059579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059597 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 5]
def baseStart_6059597 : Nat := 118140960795 + 6059597 * 2 ^ 59
def prefixEnd_6059597 : Nat := 4983230072969 + 3 ^ 40 * 6059597 * 2
def baseEnd_6059597 : Nat := 345720648171403725841103

theorem tailTrace_6059597 : CollatzResearch.WordTrace tailWord_6059597 prefixEnd_6059597 345720648171403725841103 := by
  unfold tailWord_6059597
  simp only [CollatzResearch.WordTrace]
  refine ⟨221011659428122440620369045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147341106285414960413579363 221011659428122440620369045)
  ·
    refine ⟨10359921535693239404079799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221011659428122440620369045 10359921535693239404079799)
    ·
      refine ⟨15539882303539859106119699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10359921535693239404079799 15539882303539859106119699)
      ·
        refine ⟨23309823455309788659179549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15539882303539859106119699 23309823455309788659179549)
        ·
          refine ⟨8741183795741170747192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23309823455309788659179549 8741183795741170747192331)
          ·
            refine ⟨13111775693611756120788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741183795741170747192331 13111775693611756120788497)
            ·
              refine ⟨9833831770208817090591373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13111775693611756120788497 9833831770208817090591373)
              ·
                refine ⟨3687686913828306408971765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9833831770208817090591373 3687686913828306408971765)
                ·
                  refine ⟨345720648171403725841103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3687686913828306408971765 345720648171403725841103)
                  ·
                    rfl

theorem cell23_6059597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_6059597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059597 prefixEnd_6059597 := by exact prefixLift 6059597
  have htrace : WordTrace (prefixWord ++ tailWord_6059597) baseStart_6059597 baseEnd_6059597 := by
    simpa [prefixWord, tailWord_6059597, baseEnd_6059597] using wordTrace_append hprefix tailTrace_6059597
  have hstable : (prefixWord ++ tailWord_6059597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059597).length < 2 ^ (prefixWord ++ tailWord_6059597).sum := by decide
  have hdescent : baseEnd_6059597 < baseStart_6059597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059623 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 3, 4]
def baseStart_6059623 : Nat := 118140960795 + 6059623 * 2 ^ 59
def prefixEnd_6059623 : Nat := 4983230072969 + 3 ^ 40 * 6059623 * 2
def baseEnd_6059623 : Nat := 1037166394679883476948269

theorem tailTrace_6059623 : CollatzResearch.WordTrace tailWord_6059623 prefixEnd_6059623 1037166394679883476948269 := by
  unfold tailWord_6059623
  simp only [CollatzResearch.WordTrace]
  refine ⟨221012607726028247060815523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147341738484018831373877015 221012607726028247060815523)
  ·
    refine ⟨331518911589042370591223285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221012607726028247060815523 331518911589042370591223285)
    ·
      refine ⟨31079897961472722242927183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331518911589042370591223285 31079897961472722242927183)
      ·
        refine ⟨46619846942209083364390775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079897961472722242927183 46619846942209083364390775)
        ·
          refine ⟨69929770413313625046586163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46619846942209083364390775 69929770413313625046586163)
          ·
            refine ⟨104894655619970437569879245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69929770413313625046586163 104894655619970437569879245)
            ·
              refine ⟨39335495857488914088704717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104894655619970437569879245 39335495857488914088704717)
              ·
                refine ⟨14750810946558342783264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39335495857488914088704717 14750810946558342783264269)
                ·
                  refine ⟨5531554104959378543724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14750810946558342783264269 5531554104959378543724101)
                  ·
                    refine ⟨1037166394679883476948269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5531554104959378543724101 1037166394679883476948269)
                    ·
                      rfl

theorem cell23_6059623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_6059623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059623 prefixEnd_6059623 := by exact prefixLift 6059623
  have htrace : WordTrace (prefixWord ++ tailWord_6059623) baseStart_6059623 baseEnd_6059623 := by
    simpa [prefixWord, tailWord_6059623, baseEnd_6059623] using wordTrace_append hprefix tailTrace_6059623
  have hstable : (prefixWord ++ tailWord_6059623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059623).length < 2 ^ (prefixWord ++ tailWord_6059623).sum := by decide
  have hdescent : baseEnd_6059623 < baseStart_6059623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059673 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 5, 2]
def baseStart_6059673 : Nat := 118140960795 + 6059673 * 2 ^ 59
def prefixEnd_6059673 : Nat := 4983230072969 + 3 ^ 40 * 6059673 * 2
def baseEnd_6059673 : Nat := 3111524858072375235219577

theorem tailTrace_6059673 : CollatzResearch.WordTrace tailWord_6059673 prefixEnd_6059673 3111524858072375235219577 := by
  unfold tailWord_6059673
  simp only [CollatzResearch.WordTrace]
  refine ⟨221014431375847105600135673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147342954250564737066757115 221014431375847105600135673)
  ·
    refine ⟨165760823531885329200101755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221014431375847105600135673 165760823531885329200101755)
    ·
      refine ⟨248641235297827993800152633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165760823531885329200101755 248641235297827993800152633)
      ·
        refine ⟨186480926473370995350114475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248641235297827993800152633 186480926473370995350114475)
        ·
          refine ⟨279721389710056493025171713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186480926473370995350114475 279721389710056493025171713)
          ·
            refine ⟨209791042282542369768878785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279721389710056493025171713 209791042282542369768878785)
            ·
              refine ⟨157343281711906777326659089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209791042282542369768878785 157343281711906777326659089)
              ·
                refine ⟨118007461283930082994994317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157343281711906777326659089 118007461283930082994994317)
                ·
                  refine ⟨44252797981473781123122869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118007461283930082994994317 44252797981473781123122869)
                  ·
                    refine ⟨4148699810763166980292769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44252797981473781123122869 4148699810763166980292769)
                    ·
                      refine ⟨3111524858072375235219577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148699810763166980292769 3111524858072375235219577)
                      ·
                        rfl

theorem cell23_6059673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_6059673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059673 prefixEnd_6059673 := by exact prefixLift 6059673
  have htrace : WordTrace (prefixWord ++ tailWord_6059673) baseStart_6059673 baseEnd_6059673 := by
    simpa [prefixWord, tailWord_6059673, baseEnd_6059673] using wordTrace_append hprefix tailTrace_6059673
  have hstable : (prefixWord ++ tailWord_6059673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059673).length < 2 ^ (prefixWord ++ tailWord_6059673).sum := by decide
  have hdescent : baseEnd_6059673 < baseStart_6059673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059770 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_6059770 : Nat := 118140960795 + 6059770 * 2 ^ 59
def prefixEnd_6059770 : Nat := 4983230072969 + 3 ^ 40 * 6059770 * 2
def baseEnd_6059770 : Nat := 3111574665695861355706631

theorem tailTrace_6059770 : CollatzResearch.WordTrace tailWord_6059770 prefixEnd_6059770 3111574665695861355706631 := by
  unfold tailWord_6059770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55254492314123922791604191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147345312837663794110944509 55254492314123922791604191)
  ·
    refine ⟨82881738471185884187406287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55254492314123922791604191 82881738471185884187406287)
    ·
      refine ⟨124322607706778826281109431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82881738471185884187406287 124322607706778826281109431)
      ·
        refine ⟨186483911560168239421664147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124322607706778826281109431 186483911560168239421664147)
        ·
          refine ⟨279725867340252359132496221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186483911560168239421664147 279725867340252359132496221)
          ·
            refine ⟨104897200252594634674686083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279725867340252359132496221 104897200252594634674686083)
            ·
              refine ⟨157345800378891952012029125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104897200252594634674686083 157345800378891952012029125)
              ·
                refine ⟨29502337571042241002255461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157345800378891952012029125 29502337571042241002255461)
                ·
                  refine ⟨5531688294570420187922899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29502337571042241002255461 5531688294570420187922899)
                  ·
                    refine ⟨8297532441855630281884349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531688294570420187922899 8297532441855630281884349)
                    ·
                      refine ⟨3111574665695861355706631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297532441855630281884349 3111574665695861355706631)
                      ·
                        rfl

theorem cell23_6059770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_6059770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059770 prefixEnd_6059770 := by exact prefixLift 6059770
  have htrace : WordTrace (prefixWord ++ tailWord_6059770) baseStart_6059770 baseEnd_6059770 := by
    simpa [prefixWord, tailWord_6059770, baseEnd_6059770] using wordTrace_append hprefix tailTrace_6059770
  have hstable : (prefixWord ++ tailWord_6059770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059770).length < 2 ^ (prefixWord ++ tailWord_6059770).sum := by decide
  have hdescent : baseEnd_6059770 < baseStart_6059770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059774 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_6059774 : Nat := 118140960795 + 6059774 * 2 ^ 59
def prefixEnd_6059774 : Nat := 4983230072969 + 3 ^ 40 * 6059774 * 2
def baseEnd_6059774 : Nat := 3111576719618479340056613

theorem tailTrace_6059774 : CollatzResearch.WordTrace tailWord_6059774 prefixEnd_6059774 3111576719618479340056613 := by
  unfold tailWord_6059774
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627264393560149981195297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147345410098987466566374917 27627264393560149981195297)
  ·
    refine ⟨20720448295170112485896473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27627264393560149981195297 20720448295170112485896473)
    ·
      refine ⟨15540336221377584364422355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20720448295170112485896473 15540336221377584364422355)
      ·
        refine ⟨23310504332066376546633533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15540336221377584364422355 23310504332066376546633533)
        ·
          refine ⟨8741439124524891204987575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23310504332066376546633533 8741439124524891204987575)
          ·
            refine ⟨13112158686787336807481363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741439124524891204987575 13112158686787336807481363)
            ·
              refine ⟨19668238030181005211222045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112158686787336807481363 19668238030181005211222045)
              ·
                refine ⟨7375589261317876954208267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19668238030181005211222045 7375589261317876954208267)
                ·
                  refine ⟨11063383891976815431312401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375589261317876954208267 11063383891976815431312401)
                  ·
                    refine ⟨8297537918982611573484301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11063383891976815431312401 8297537918982611573484301)
                    ·
                      refine ⟨3111576719618479340056613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297537918982611573484301 3111576719618479340056613)
                      ·
                        rfl

theorem cell23_6059774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_6059774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059774 prefixEnd_6059774 := by exact prefixLift 6059774
  have htrace : WordTrace (prefixWord ++ tailWord_6059774) baseStart_6059774 baseEnd_6059774 := by
    simpa [prefixWord, tailWord_6059774, baseEnd_6059774] using wordTrace_append hprefix tailTrace_6059774
  have hstable : (prefixWord ++ tailWord_6059774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059774).length < 2 ^ (prefixWord ++ tailWord_6059774).sum := by decide
  have hdescent : baseEnd_6059774 < baseStart_6059774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059787 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 3]
def baseStart_6059787 : Nat := 118140960795 + 6059787 * 2 ^ 59
def prefixEnd_6059787 : Nat := 4983230072969 + 3 ^ 40 * 6059787 * 2
def baseEnd_6059787 : Nat := 3111583394866987789194053

theorem tailTrace_6059787 : CollatzResearch.WordTrace tailWord_6059787 prefixEnd_6059787 3111583394866987789194053 := by
  unfold tailWord_6059787
  simp only [CollatzResearch.WordTrace]
  refine ⟨221018589297434103069785615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147345726198289402046523743 221018589297434103069785615)
  ·
    refine ⟨331527883946151154604678423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221018589297434103069785615 331527883946151154604678423)
    ·
      refine ⟨497291825919226731907017635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331527883946151154604678423 497291825919226731907017635)
      ·
        refine ⟨745937738878840097860526453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497291825919226731907017635 745937738878840097860526453)
        ·
          refine ⟨69931663019891259174424355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 745937738878840097860526453 69931663019891259174424355)
          ·
            refine ⟨104897494529836888761636533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69931663019891259174424355 104897494529836888761636533)
            ·
              refine ⟨9834140112172208321403425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104897494529836888761636533 9834140112172208321403425)
              ·
                refine ⟨7375605084129156241052569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9834140112172208321403425 7375605084129156241052569)
                ·
                  refine ⟨5531703813096867180789427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375605084129156241052569 5531703813096867180789427)
                  ·
                    refine ⟨8297555719645300771184141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531703813096867180789427 8297555719645300771184141)
                    ·
                      refine ⟨3111583394866987789194053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297555719645300771184141 3111583394866987789194053)
                      ·
                        rfl

theorem cell23_6059787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 3].length) (baseStart_6059787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059787 prefixEnd_6059787 := by exact prefixLift 6059787
  have htrace : WordTrace (prefixWord ++ tailWord_6059787) baseStart_6059787 baseEnd_6059787 := by
    simpa [prefixWord, tailWord_6059787, baseEnd_6059787] using wordTrace_append hprefix tailTrace_6059787
  have hstable : (prefixWord ++ tailWord_6059787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059787).length < 2 ^ (prefixWord ++ tailWord_6059787).sum := by decide
  have hdescent : baseEnd_6059787 < baseStart_6059787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059804 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6059804 : Nat := 118140960795 + 6059804 * 2 ^ 59
def prefixEnd_6059804 : Nat := 4983230072969 + 3 ^ 40 * 6059804 * 2
def baseEnd_6059804 : Nat := 3111592124038114222681475

theorem tailTrace_6059804 : CollatzResearch.WordTrace tailWord_6059804 prefixEnd_6059804 3111592124038114222681475 := by
  unfold tailWord_6059804
  simp only [CollatzResearch.WordTrace]
  refine ⟨110509604669186257486577233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147346139558915009982102977 110509604669186257486577233)
  ·
    refine ⟨82882203501889693114932925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110509604669186257486577233 82882203501889693114932925)
    ·
      refine ⟨31080826313208634918099847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82882203501889693114932925 31080826313208634918099847)
      ·
        refine ⟨46621239469812952377149771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31080826313208634918099847 46621239469812952377149771)
        ·
          refine ⟨69931859204719428565724657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46621239469812952377149771 69931859204719428565724657)
          ·
            refine ⟨52448894403539571424293493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69931859204719428565724657 52448894403539571424293493)
            ·
              refine ⟨4917083850331834821027515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52448894403539571424293493 4917083850331834821027515)
              ·
                refine ⟨7375625775497752231541273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917083850331834821027515 7375625775497752231541273)
                ·
                  refine ⟨5531719331623314173655955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375625775497752231541273 5531719331623314173655955)
                  ·
                    refine ⟨8297578997434971260483933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531719331623314173655955 8297578997434971260483933)
                    ·
                      refine ⟨3111592124038114222681475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297578997434971260483933 3111592124038114222681475)
                      ·
                        rfl

theorem cell23_6059804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6059804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059804 prefixEnd_6059804 := by exact prefixLift 6059804
  have htrace : WordTrace (prefixWord ++ tailWord_6059804) baseStart_6059804 baseEnd_6059804 := by
    simpa [prefixWord, tailWord_6059804, baseEnd_6059804] using wordTrace_append hprefix tailTrace_6059804
  have hstable : (prefixWord ++ tailWord_6059804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059804).length < 2 ^ (prefixWord ++ tailWord_6059804).sum := by decide
  have hdescent : baseEnd_6059804 < baseStart_6059804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059861 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6059861 : Nat := 118140960795 + 6059861 * 2 ^ 59
def prefixEnd_6059861 : Nat := 4983230072969 + 3 ^ 40 * 6059861 * 2
def baseEnd_6059861 : Nat := 3111621392435420499668713

theorem tailTrace_6059861 : CollatzResearch.WordTrace tailWord_6059861 prefixEnd_6059861 3111621392435420499668713 := by
  unfold tailWord_6059861
  simp only [CollatzResearch.WordTrace]
  refine ⟨221021288299166013707979437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147347525532777342471986291 221021288299166013707979437)
  ·
    refine ⟨82882983112187255140492289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221021288299166013707979437 82882983112187255140492289)
    ·
      refine ⟨62162237334140441355369217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82882983112187255140492289 62162237334140441355369217)
      ·
        refine ⟨46621678000605331016526913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62162237334140441355369217 46621678000605331016526913)
        ·
          refine ⟨34966258500453998262395185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46621678000605331016526913 34966258500453998262395185)
          ·
            refine ⟨26224693875340498696796389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34966258500453998262395185 26224693875340498696796389)
            ·
              refine ⟨4917130101626343505649323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26224693875340498696796389 4917130101626343505649323)
              ·
                refine ⟨7375695152439515258473985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917130101626343505649323 7375695152439515258473985)
                ·
                  refine ⟨5531771364329636443855489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7375695152439515258473985 5531771364329636443855489)
                  ·
                    refine ⟨4148828523247227332891617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5531771364329636443855489 4148828523247227332891617)
                    ·
                      refine ⟨3111621392435420499668713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148828523247227332891617 3111621392435420499668713)
                      ·
                        rfl

theorem cell23_6059861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6059861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059861 prefixEnd_6059861 := by exact prefixLift 6059861
  have htrace : WordTrace (prefixWord ++ tailWord_6059861) baseStart_6059861 baseEnd_6059861 := by
    simpa [prefixWord, tailWord_6059861, baseEnd_6059861] using wordTrace_append hprefix tailTrace_6059861
  have hstable : (prefixWord ++ tailWord_6059861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059861).length < 2 ^ (prefixWord ++ tailWord_6059861).sum := by decide
  have hdescent : baseEnd_6059861 < baseStart_6059861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059873 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6059873 : Nat := 118140960795 + 6059873 * 2 ^ 59
def prefixEnd_6059873 : Nat := 4983230072969 + 3 ^ 40 * 6059873 * 2
def baseEnd_6059873 : Nat := 3111627554203274452718657

theorem tailTrace_6059873 : CollatzResearch.WordTrace tailWord_6059873 prefixEnd_6059873 3111627554203274452718657 := by
  unfold tailWord_6059873
  simp only [CollatzResearch.WordTrace]
  refine ⟨221021725975122539757416273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147347817316748359838277515 221021725975122539757416273)
  ·
    refine ⟨165766294481341904818062205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221021725975122539757416273 165766294481341904818062205)
    ·
      refine ⟨62162360430503214306773327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165766294481341904818062205 62162360430503214306773327)
      ·
        refine ⟨93243540645754821460159991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62162360430503214306773327 93243540645754821460159991)
        ·
          refine ⟨139865310968632232190239987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93243540645754821460159991 139865310968632232190239987)
          ·
            refine ⟨209797966452948348285359981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139865310968632232190239987 209797966452948348285359981)
            ·
              refine ⟨78674237419855630607009993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209797966452948348285359981 78674237419855630607009993)
              ·
                refine ⟨59005678064891722955257495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78674237419855630607009993 59005678064891722955257495)
                ·
                  refine ⟨88508517097337584432886243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59005678064891722955257495 88508517097337584432886243)
                  ·
                    refine ⟨132762775646006376649329365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88508517097337584432886243 132762775646006376649329365)
                    ·
                      refine ⟨3111627554203274452718657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132762775646006376649329365 3111627554203274452718657)
                      ·
                        rfl

theorem cell23_6059873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6059873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059873 prefixEnd_6059873 := by exact prefixLift 6059873
  have htrace : WordTrace (prefixWord ++ tailWord_6059873) baseStart_6059873 baseEnd_6059873 := by
    simpa [prefixWord, tailWord_6059873, baseEnd_6059873] using wordTrace_append hprefix tailTrace_6059873
  have hstable : (prefixWord ++ tailWord_6059873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059873).length < 2 ^ (prefixWord ++ tailWord_6059873).sum := by decide
  have hdescent : baseEnd_6059873 < baseStart_6059873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059903 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_6059903 : Nat := 118140960795 + 6059903 * 2 ^ 59
def prefixEnd_6059903 : Nat := 4983230072969 + 3 ^ 40 * 6059903 * 2
def baseEnd_6059903 : Nat := 3111642958622909335343519

theorem tailTrace_6059903 : CollatzResearch.WordTrace tailWord_6059903 prefixEnd_6059903 3111642958622909335343519 := by
  unfold tailWord_6059903
  simp only [CollatzResearch.WordTrace]
  refine ⟨221022820165013854881008363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147348546776675903254005575 221022820165013854881008363)
  ·
    refine ⟨331534230247520782321512545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221022820165013854881008363 331534230247520782321512545)
    ·
      refine ⟨248650672685640586741134409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331534230247520782321512545 248650672685640586741134409)
      ·
        refine ⟨186488004514230440055850807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248650672685640586741134409 186488004514230440055850807)
        ·
          refine ⟨279732006771345660083776211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186488004514230440055850807 279732006771345660083776211)
          ·
            refine ⟨419598010157018490125664317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279732006771345660083776211 419598010157018490125664317)
            ·
              refine ⟨157349253808881933797124119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419598010157018490125664317 157349253808881933797124119)
              ·
                refine ⟨236023880713322900695686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157349253808881933797124119 236023880713322900695686179)
                ·
                  refine ⟨354035821069984351043529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236023880713322900695686179 354035821069984351043529269)
                  ·
                    refine ⟨33190858225311032910330869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 354035821069984351043529269 33190858225311032910330869)
                    ·
                      refine ⟨3111642958622909335343519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33190858225311032910330869 3111642958622909335343519)
                      ·
                        rfl

theorem cell23_6059903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_6059903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059903 prefixEnd_6059903 := by exact prefixLift 6059903
  have htrace : WordTrace (prefixWord ++ tailWord_6059903) baseStart_6059903 baseEnd_6059903 := by
    simpa [prefixWord, tailWord_6059903, baseEnd_6059903] using wordTrace_append hprefix tailTrace_6059903
  have hstable : (prefixWord ++ tailWord_6059903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059903).length < 2 ^ (prefixWord ++ tailWord_6059903).sum := by decide
  have hdescent : baseEnd_6059903 < baseStart_6059903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_6059920 : Nat := 118140960795 + 6059920 * 2 ^ 59
def prefixEnd_6059920 : Nat := 4983230072969 + 3 ^ 40 * 6059920 * 2
def baseEnd_6059920 : Nat := 3111651687794035768830941

theorem tailTrace_6059920 : CollatzResearch.WordTrace tailWord_6059920 prefixEnd_6059920 3111651687794035768830941 := by
  unfold tailWord_6059920
  simp only [CollatzResearch.WordTrace]
  refine ⟨110511720102976133392188607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147348960137301511189584809 110511720102976133392188607)
  ·
    refine ⟨165767580154464200088282911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110511720102976133392188607 165767580154464200088282911)
    ·
      refine ⟨248651370231696300132424367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165767580154464200088282911 248651370231696300132424367)
      ·
        refine ⟨372977055347544450198636551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248651370231696300132424367 372977055347544450198636551)
        ·
          refine ⟨559465583021316675297954827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372977055347544450198636551 559465583021316675297954827)
          ·
            refine ⟨839198374531975012946932241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559465583021316675297954827 839198374531975012946932241)
            ·
              refine ⟨629398780898981259710199181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839198374531975012946932241 629398780898981259710199181)
              ·
                refine ⟨236024542837117972391324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629398780898981259710199181 236024542837117972391324693)
                ·
                  refine ⟨11063650445489904955843345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236024542837117972391324693 11063650445489904955843345)
                  ·
                    refine ⟨8297737834117428716882509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11063650445489904955843345 8297737834117428716882509)
                    ·
                      refine ⟨3111651687794035768830941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297737834117428716882509 3111651687794035768830941)
                      ·
                        rfl

theorem cell23_6059920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_6059920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059920 prefixEnd_6059920 := by exact prefixLift 6059920
  have htrace : WordTrace (prefixWord ++ tailWord_6059920) baseStart_6059920 baseEnd_6059920 := by
    simpa [prefixWord, tailWord_6059920, baseEnd_6059920] using wordTrace_append hprefix tailTrace_6059920
  have hstable : (prefixWord ++ tailWord_6059920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059920).length < 2 ^ (prefixWord ++ tailWord_6059920).sum := by decide
  have hdescent : baseEnd_6059920 < baseStart_6059920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059927 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 3, 4]
def baseStart_6059927 : Nat := 118140960795 + 6059927 * 2 ^ 59
def prefixEnd_6059927 : Nat := 4983230072969 + 3 ^ 40 * 6059927 * 2
def baseEnd_6059927 : Nat := 1037218427386205747147803

theorem tailTrace_6059927 : CollatzResearch.WordTrace tailWord_6059927 prefixEnd_6059927 1037218427386205747147803 := by
  unfold tailWord_6059927
  simp only [CollatzResearch.WordTrace]
  refine ⟨221023695516926906979882035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147349130344617937986588023 221023695516926906979882035)
  ·
    refine ⟨331535543275390360469823053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221023695516926906979882035 331535543275390360469823053)
    ·
      refine ⟨124325828728271385176183645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331535543275390360469823053 124325828728271385176183645)
      ·
        refine ⟨46622185773101769441068867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124325828728271385176183645 46622185773101769441068867)
        ·
          refine ⟨69933278659652654161603301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46622185773101769441068867 69933278659652654161603301)
          ·
            refine ⟨13112489748684872655300619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69933278659652654161603301 13112489748684872655300619)
            ·
              refine ⟨19668734623027308982950929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112489748684872655300619 19668734623027308982950929)
              ·
                refine ⟨14751550967270481737213197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19668734623027308982950929 14751550967270481737213197)
                ·
                  refine ⟨5531831612726430651454949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14751550967270481737213197 5531831612726430651454949)
                  ·
                    refine ⟨1037218427386205747147803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5531831612726430651454949 1037218427386205747147803)
                    ·
                      rfl

theorem cell23_6059927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_6059927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059927 prefixEnd_6059927 := by exact prefixLift 6059927
  have htrace : WordTrace (prefixWord ++ tailWord_6059927) baseStart_6059927 baseEnd_6059927 := by
    simpa [prefixWord, tailWord_6059927, baseEnd_6059927] using wordTrace_append hprefix tailTrace_6059927
  have hstable : (prefixWord ++ tailWord_6059927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059927).length < 2 ^ (prefixWord ++ tailWord_6059927).sum := by decide
  have hdescent : baseEnd_6059927 < baseStart_6059927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059957 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 6]
def baseStart_6059957 : Nat := 118140960795 + 6059957 * 2 ^ 59
def prefixEnd_6059957 : Nat := 4983230072969 + 3 ^ 40 * 6059957 * 2
def baseEnd_6059957 : Nat := 345741187397583569340919

theorem tailTrace_6059957 : CollatzResearch.WordTrace tailWord_6059957 prefixEnd_6059957 345741187397583569340919 := by
  unfold tailWord_6059957
  simp only [CollatzResearch.WordTrace]
  refine ⟨221024789706818222103474125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147349859804545481402316083 221024789706818222103474125)
  ·
    refine ⟨82884296140056833288802797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221024789706818222103474125 82884296140056833288802797)
    ·
      refine ⟨31081611052521312483301049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82884296140056833288802797 31081611052521312483301049)
      ·
        refine ⟨23311208289390984362475787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31081611052521312483301049 23311208289390984362475787)
        ·
          refine ⟨34966812434086476543713681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23311208289390984362475787 34966812434086476543713681)
          ·
            refine ⟨26225109325564857407785261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34966812434086476543713681 26225109325564857407785261)
            ·
              refine ⟨9834415997086821527919473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26225109325564857407785261 9834415997086821527919473)
              ·
                refine ⟨7375811997815116145939605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9834415997086821527919473 7375811997815116145939605)
                ·
                  refine ⟨345741187397583569340919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7375811997815116145939605 345741187397583569340919)
                  ·
                    rfl

theorem cell23_6059957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_6059957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059957 prefixEnd_6059957 := by exact prefixLift 6059957
  have htrace : WordTrace (prefixWord ++ tailWord_6059957) baseStart_6059957 baseEnd_6059957 := by
    simpa [prefixWord, tailWord_6059957, baseEnd_6059957] using wordTrace_append hprefix tailTrace_6059957
  have hstable : (prefixWord ++ tailWord_6059957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059957).length < 2 ^ (prefixWord ++ tailWord_6059957).sum := by decide
  have hdescent : baseEnd_6059957 < baseStart_6059957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6059977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 4, 3, 2]
def baseStart_6059977 : Nat := 118140960795 + 6059977 * 2 ^ 59
def prefixEnd_6059977 : Nat := 4983230072969 + 3 ^ 40 * 6059977 * 2
def baseEnd_6059977 : Nat := 3111680956191342045818179

theorem tailTrace_6059977 : CollatzResearch.WordTrace tailWord_6059977 prefixEnd_6059977 3111680956191342045818179 := by
  unfold tailWord_6059977
  simp only [CollatzResearch.WordTrace]
  refine ⟨221025519166745765519202185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147350346111163843679468123 221025519166745765519202185)
  ·
    refine ⟨165769139375059324139401639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221025519166745765519202185 165769139375059324139401639)
    ·
      refine ⟨248653709062588986209102459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165769139375059324139401639 248653709062588986209102459)
      ·
        refine ⟨372980563593883479313653689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248653709062588986209102459 372980563593883479313653689)
        ·
          refine ⟨279735422695412609485240267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372980563593883479313653689 279735422695412609485240267)
          ·
            refine ⟨419603134043118914227860401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279735422695412609485240267 419603134043118914227860401)
            ·
              refine ⟨314702350532339185670895301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419603134043118914227860401 314702350532339185670895301)
              ·
                refine ⟨59006690724813597313292869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314702350532339185670895301 59006690724813597313292869)
                ·
                  refine ⟨11063754510902549496242413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59006690724813597313292869 11063754510902549496242413)
                  ·
                    refine ⟨4148907941588456061090905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11063754510902549496242413 4148907941588456061090905)
                    ·
                      refine ⟨3111680956191342045818179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4148907941588456061090905 3111680956191342045818179)
                      ·
                        rfl

theorem cell23_6059977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3, 2].length) (baseStart_6059977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6059977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6059977 prefixEnd_6059977 := by exact prefixLift 6059977
  have htrace : WordTrace (prefixWord ++ tailWord_6059977) baseStart_6059977 baseEnd_6059977 := by
    simpa [prefixWord, tailWord_6059977, baseEnd_6059977] using wordTrace_append hprefix tailTrace_6059977
  have hstable : (prefixWord ++ tailWord_6059977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6059977).length < 2 ^ (prefixWord ++ tailWord_6059977).sum := by decide
  have hdescent : baseEnd_6059977 < baseStart_6059977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6059977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060000 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_6060000 : Nat := 118140960795 + 6060000 * 2 ^ 59
def prefixEnd_6060000 : Nat := 4983230072969 + 3 ^ 40 * 6060000 * 2
def baseEnd_6060000 : Nat := 1037230922082131818610191

theorem tailTrace_6060000 : CollatzResearch.WordTrace tailWord_6060000 prefixEnd_6060000 1037230922082131818610191 := by
  unfold tailWord_6060000
  simp only [CollatzResearch.WordTrace]
  refine ⟨110513179022831220223644727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147350905363774960298192969 110513179022831220223644727)
  ·
    refine ⟨165769768534246830335467091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110513179022831220223644727 165769768534246830335467091)
    ·
      refine ⟨248654652801370245503200637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165769768534246830335467091 248654652801370245503200637)
      ·
        refine ⟨93245494800513842063700239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248654652801370245503200637 93245494800513842063700239)
        ·
          refine ⟨139868242200770763095550359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93245494800513842063700239 139868242200770763095550359)
          ·
            refine ⟨209802363301156144643325539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139868242200770763095550359 209802363301156144643325539)
            ·
              refine ⟨314703544951734216964988309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209802363301156144643325539 314703544951734216964988309)
              ·
                refine ⟨14751728669612541420233827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 314703544951734216964988309 14751728669612541420233827)
                ·
                  refine ⟨22127593004418812130350741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14751728669612541420233827 22127593004418812130350741)
                  ·
                    refine ⟨1037230922082131818610191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22127593004418812130350741 1037230922082131818610191)
                    ·
                      rfl

theorem cell23_6060000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_6060000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060000 prefixEnd_6060000 := by exact prefixLift 6060000
  have htrace : WordTrace (prefixWord ++ tailWord_6060000) baseStart_6060000 baseEnd_6060000 := by
    simpa [prefixWord, tailWord_6060000, baseEnd_6060000] using wordTrace_append hprefix tailTrace_6060000
  have hstable : (prefixWord ++ tailWord_6060000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060000).length < 2 ^ (prefixWord ++ tailWord_6060000).sum := by decide
  have hdescent : baseEnd_6060000 < baseStart_6060000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060001 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_6060001 : Nat := 118140960795 + 6060001 * 2 ^ 59
def prefixEnd_6060001 : Nat := 4983230072969 + 3 ^ 40 * 6060001 * 2
def baseEnd_6060001 : Nat := 3111693279727049951918069

theorem tailTrace_6060001 : CollatzResearch.WordTrace tailWord_6060001 prefixEnd_6060001 3111693279727049951918069 := by
  unfold tailWord_6060001
  simp only [CollatzResearch.WordTrace]
  refine ⟨221026394518658817618075857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147350929679105878412050571 221026394518658817618075857)
  ·
    refine ⟨165769795888994113213556893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221026394518658817618075857 165769795888994113213556893)
    ·
      refine ⟨62163673458372792455083835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165769795888994113213556893 62163673458372792455083835)
      ·
        refine ⟨93245510187559188682625753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62163673458372792455083835 93245510187559188682625753)
        ·
          refine ⟨69934132640669391511969315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93245510187559188682625753 69934132640669391511969315)
          ·
            refine ⟨104901198961004087267953973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69934132640669391511969315 104901198961004087267953973)
            ·
              refine ⟨9834487402594133181370685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104901198961004087267953973 9834487402594133181370685)
              ·
                refine ⟨3687932775972799943014007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9834487402594133181370685 3687932775972799943014007)
                ·
                  refine ⟨5531899163959199914521011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687932775972799943014007 5531899163959199914521011)
                  ·
                    refine ⟨8297848745938799871781517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531899163959199914521011 8297848745938799871781517)
                    ·
                      refine ⟨3111693279727049951918069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8297848745938799871781517 3111693279727049951918069)
                      ·
                        rfl

theorem cell23_6060001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_6060001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060001 prefixEnd_6060001 := by exact prefixLift 6060001
  have htrace : WordTrace (prefixWord ++ tailWord_6060001) baseStart_6060001 baseEnd_6060001 := by
    simpa [prefixWord, tailWord_6060001, baseEnd_6060001] using wordTrace_append hprefix tailTrace_6060001
  have hstable : (prefixWord ++ tailWord_6060001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060001).length < 2 ^ (prefixWord ++ tailWord_6060001).sum := by decide
  have hdescent : baseEnd_6060001 < baseStart_6060001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060125 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6060125 : Nat := 118140960795 + 6060125 * 2 ^ 59
def prefixEnd_6060125 : Nat := 4983230072969 + 3 ^ 40 * 6060125 * 2
def baseEnd_6060125 : Nat := 3111756951328207466767499

theorem tailTrace_6060125 : CollatzResearch.WordTrace tailWord_6060125 prefixEnd_6060125 3111756951328207466767499 := by
  unfold tailWord_6060125
  simp only [CollatzResearch.WordTrace]
  refine ⟨221030917170209586795589829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147353944780139724530393219 221030917170209586795589829)
  ·
    refine ⟨41443296969414297524173093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221030917170209586795589829 41443296969414297524173093)
    ·
      refine ⟨7770618181765180785782455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41443296969414297524173093 7770618181765180785782455)
      ·
        refine ⟨11655927272647771178673683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7770618181765180785782455 11655927272647771178673683)
        ·
          refine ⟨17483890908971656768010525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11655927272647771178673683 17483890908971656768010525)
          ·
            refine ⟨6556459090864371288003947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17483890908971656768010525 6556459090864371288003947)
            ·
              refine ⟨9834688636296556932005921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556459090864371288003947 9834688636296556932005921)
              ·
                refine ⟨7376016477222417699004441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9834688636296556932005921 7376016477222417699004441)
                ·
                  refine ⟨5532012357916813274253331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7376016477222417699004441 5532012357916813274253331)
                  ·
                    refine ⟨8298018536875219911379997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5532012357916813274253331 8298018536875219911379997)
                    ·
                      refine ⟨3111756951328207466767499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298018536875219911379997 3111756951328207466767499)
                      ·
                        rfl

theorem cell23_6060125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6060125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060125 prefixEnd_6060125 := by exact prefixLift 6060125
  have htrace : WordTrace (prefixWord ++ tailWord_6060125) baseStart_6060125 baseEnd_6060125 := by
    simpa [prefixWord, tailWord_6060125, baseEnd_6060125] using wordTrace_append hprefix tailTrace_6060125
  have hstable : (prefixWord ++ tailWord_6060125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060125).length < 2 ^ (prefixWord ++ tailWord_6060125).sum := by decide
  have hdescent : baseEnd_6060125 < baseStart_6060125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060137 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 7]
def baseStart_6060137 : Nat := 118140960795 + 6060137 * 2 ^ 59
def prefixEnd_6060137 : Nat := 4983230072969 + 3 ^ 40 * 6060137 * 2
def baseEnd_6060137 : Nat := 345751457010673491090827

theorem tailTrace_6060137 : CollatzResearch.WordTrace tailWord_6060137 prefixEnd_6060137 345751457010673491090827 := by
  unfold tailWord_6060137
  simp only [CollatzResearch.WordTrace]
  refine ⟨221031354846166112845026665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147354236564110741896684443 221031354846166112845026665)
  ·
    refine ⟨165773516134624584633769999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221031354846166112845026665 165773516134624584633769999)
    ·
      refine ⟨248660274201936876950654999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165773516134624584633769999 248660274201936876950654999)
      ·
        refine ⟨372990411302905315425982499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248660274201936876950654999 372990411302905315425982499)
        ·
          refine ⟨559485616954357973138973749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372990411302905315425982499 559485616954357973138973749)
          ·
            refine ⟨52451776589471059981778789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 559485616954357973138973749 52451776589471059981778789)
            ·
              refine ⟨9834708110525823746583523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52451776589471059981778789 9834708110525823746583523)
              ·
                refine ⟨14752062165788735619875285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9834708110525823746583523 14752062165788735619875285)
                ·
                  refine ⟨345751457010673491090827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14752062165788735619875285 345751457010673491090827)
                  ·
                    rfl

theorem cell23_6060137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_6060137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060137 prefixEnd_6060137 := by exact prefixLift 6060137
  have htrace : WordTrace (prefixWord ++ tailWord_6060137) baseStart_6060137 baseEnd_6060137 := by
    simpa [prefixWord, tailWord_6060137, baseEnd_6060137] using wordTrace_append hprefix tailTrace_6060137
  have hstable : (prefixWord ++ tailWord_6060137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060137).length < 2 ^ (prefixWord ++ tailWord_6060137).sum := by decide
  have hdescent : baseEnd_6060137 < baseStart_6060137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060167 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 7]
def baseStart_6060167 : Nat := 118140960795 + 6060167 * 2 ^ 59
def prefixEnd_6060167 : Nat := 4983230072969 + 3 ^ 40 * 6060167 * 2
def baseEnd_6060167 : Nat := 1037259505838565434147435

theorem tailTrace_6060167 : CollatzResearch.WordTrace tailWord_6060167 prefixEnd_6060167 1037259505838565434147435 := by
  unfold tailWord_6060167
  simp only [CollatzResearch.WordTrace]
  refine ⟨221032449036057427968618755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147354966024038285312412503 221032449036057427968618755)
  ·
    refine ⟨331548673554086141952928133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221032449036057427968618755 331548673554086141952928133)
    ·
      refine ⟨62165376291391151616174025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331548673554086141952928133 62165376291391151616174025)
      ·
        refine ⟨46624032218543363712130519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62165376291391151616174025 46624032218543363712130519)
        ·
          refine ⟨69936048327815045568195779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46624032218543363712130519 69936048327815045568195779)
          ·
            refine ⟨104904072491722568352293669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69936048327815045568195779 104904072491722568352293669)
            ·
              refine ⟨19669513592197981566055063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104904072491722568352293669 19669513592197981566055063)
              ·
                refine ⟨29504270388296972349082595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19669513592197981566055063 29504270388296972349082595)
                ·
                  refine ⟨44256405582445458523623893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29504270388296972349082595 44256405582445458523623893)
                  ·
                    refine ⟨1037259505838565434147435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44256405582445458523623893 1037259505838565434147435)
                    ·
                      rfl

theorem cell23_6060167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_6060167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060167 prefixEnd_6060167 := by exact prefixLift 6060167
  have htrace : WordTrace (prefixWord ++ tailWord_6060167) baseStart_6060167 baseEnd_6060167 := by
    simpa [prefixWord, tailWord_6060167, baseEnd_6060167] using wordTrace_append hprefix tailTrace_6060167
  have hstable : (prefixWord ++ tailWord_6060167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060167).length < 2 ^ (prefixWord ++ tailWord_6060167).sum := by decide
  have hdescent : baseEnd_6060167 < baseStart_6060167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060194 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6060194 : Nat := 118140960795 + 6060194 * 2 ^ 59
def prefixEnd_6060194 : Nat := 4983230072969 + 3 ^ 40 * 6060194 * 2
def baseEnd_6060194 : Nat := 3111792381493367696804681

theorem tailTrace_6060194 : CollatzResearch.WordTrace tailWord_6060194 prefixEnd_6060194 3111792381493367696804681 := by
  unfold tailWord_6060194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55258358451739902894962909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147355622537973074386567757 55258358451739902894962909)
  ·
    refine ⟨20721884419402463585611091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55258358451739902894962909 20721884419402463585611091)
    ·
      refine ⟨31082826629103695378416637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20721884419402463585611091 31082826629103695378416637)
      ·
        refine ⟨11656059985913885766906239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31082826629103695378416637 11656059985913885766906239)
        ·
          refine ⟨17484089978870828650359359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11656059985913885766906239 17484089978870828650359359)
          ·
            refine ⟨26226134968306242975539039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17484089978870828650359359 26226134968306242975539039)
            ·
              refine ⟨39339202452459364463308559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26226134968306242975539039 39339202452459364463308559)
              ·
                refine ⟨59008803678689046694962839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39339202452459364463308559 59008803678689046694962839)
                ·
                  refine ⟨88513205518033570042444259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59008803678689046694962839 88513205518033570042444259)
                  ·
                    refine ⟨132769808277050355063666389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88513205518033570042444259 132769808277050355063666389)
                    ·
                      refine ⟨3111792381493367696804681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132769808277050355063666389 3111792381493367696804681)
                      ·
                        rfl

theorem cell23_6060194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6060194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060194 prefixEnd_6060194 := by exact prefixLift 6060194
  have htrace : WordTrace (prefixWord ++ tailWord_6060194) baseStart_6060194 baseEnd_6060194 := by
    simpa [prefixWord, tailWord_6060194, baseEnd_6060194] using wordTrace_append hprefix tailTrace_6060194
  have hstable : (prefixWord ++ tailWord_6060194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060194).length < 2 ^ (prefixWord ++ tailWord_6060194).sum := by decide
  have hdescent : baseEnd_6060194 < baseStart_6060194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060199 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6060199 : Nat := 118140960795 + 6060199 * 2 ^ 59
def prefixEnd_6060199 : Nat := 4983230072969 + 3 ^ 40 * 6060199 * 2
def baseEnd_6060199 : Nat := 3111794948896640177242159

theorem tailTrace_6060199 : CollatzResearch.WordTrace tailWord_6060199 prefixEnd_6060199 3111794948896640177242159 := by
  unfold tailWord_6060199
  simp only [CollatzResearch.WordTrace]
  refine ⟨221033616171941497433783651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147355744114627664955855767 221033616171941497433783651)
  ·
    refine ⟨331550424257912246150675477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221033616171941497433783651 331550424257912246150675477)
    ·
      refine ⟨15541426137089636538312913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 331550424257912246150675477 15541426137089636538312913)
      ·
        refine ⟨11656069602817227403734685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15541426137089636538312913 11656069602817227403734685)
        ·
          refine ⟨4371026101056460276400507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11656069602817227403734685 4371026101056460276400507)
          ·
            refine ⟨6556539151584690414600761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371026101056460276400507 6556539151584690414600761)
            ·
              refine ⟨4917404363688517810950571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6556539151584690414600761 4917404363688517810950571)
              ·
                refine ⟨7376106545532776716425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4917404363688517810950571 7376106545532776716425857)
                ·
                  refine ⟨5532079909149582537319393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7376106545532776716425857 5532079909149582537319393)
                  ·
                    refine ⟨4149059931862186902989545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5532079909149582537319393 4149059931862186902989545)
                    ·
                      refine ⟨3111794948896640177242159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149059931862186902989545 3111794948896640177242159)
                      ·
                        rfl

theorem cell23_6060199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6060199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060199 prefixEnd_6060199 := by exact prefixLift 6060199
  have htrace : WordTrace (prefixWord ++ tailWord_6060199) baseStart_6060199 baseEnd_6060199 := by
    simpa [prefixWord, tailWord_6060199, baseEnd_6060199] using wordTrace_append hprefix tailTrace_6060199
  have hstable : (prefixWord ++ tailWord_6060199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060199).length < 2 ^ (prefixWord ++ tailWord_6060199).sum := by decide
  have hdescent : baseEnd_6060199 < baseStart_6060199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060204 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 4, 2]
def baseStart_6060204 : Nat := 118140960795 + 6060204 * 2 ^ 59
def prefixEnd_6060204 : Nat := 4983230072969 + 3 ^ 40 * 6060204 * 2
def baseEnd_6060204 : Nat := 3111797516299912657679635

theorem tailTrace_6060204 : CollatzResearch.WordTrace tailWord_6060204 prefixEnd_6060204 3111797516299912657679635 := by
  unfold tailWord_6060204
  simp only [CollatzResearch.WordTrace]
  refine ⟨110516899268461691643857833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147355865691282255525143777 110516899268461691643857833)
  ·
    refine ⟨82887674451346268732893375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110516899268461691643857833 82887674451346268732893375)
    ·
      refine ⟨124331511677019403099340063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82887674451346268732893375 124331511677019403099340063)
      ·
        refine ⟨186497267515529104649010095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124331511677019403099340063 186497267515529104649010095)
        ·
          refine ⟨279745901273293656973515143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186497267515529104649010095 279745901273293656973515143)
          ·
            refine ⟨419618851909940485460272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279745901273293656973515143 419618851909940485460272715)
            ·
              refine ⟨629428277864910728190409073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419618851909940485460272715 629428277864910728190409073)
              ·
                refine ⟨472071208398683046142806805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629428277864910728190409073 472071208398683046142806805)
                ·
                  refine ⟨22128337893688267787944069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 472071208398683046142806805 22128337893688267787944069)
                  ·
                    refine ⟨4149063355066550210239513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22128337893688267787944069 4149063355066550210239513)
                    ·
                      refine ⟨3111797516299912657679635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149063355066550210239513 3111797516299912657679635)
                      ·
                        rfl

theorem cell23_6060204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_6060204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060204 prefixEnd_6060204 := by exact prefixLift 6060204
  have htrace : WordTrace (prefixWord ++ tailWord_6060204) baseStart_6060204 baseEnd_6060204 := by
    simpa [prefixWord, tailWord_6060204, baseEnd_6060204] using wordTrace_append hprefix tailTrace_6060204
  have hstable : (prefixWord ++ tailWord_6060204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060204).length < 2 ^ (prefixWord ++ tailWord_6060204).sum := by decide
  have hdescent : baseEnd_6060204 < baseStart_6060204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060247 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_6060247 : Nat := 118140960795 + 6060247 * 2 ^ 59
def prefixEnd_6060247 : Nat := 4983230072969 + 3 ^ 40 * 6060247 * 2
def baseEnd_6060247 : Nat := 3111819595968055989441937

theorem tailTrace_6060247 : CollatzResearch.WordTrace tailWord_6060247 prefixEnd_6060247 3111819595968055989441937 := by
  unfold tailWord_6060247
  simp only [CollatzResearch.WordTrace]
  refine ⟨221035366875767601631530995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147356911250511734421020663 221035366875767601631530995)
  ·
    refine ⟨331553050313651402447296493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221035366875767601631530995 331553050313651402447296493)
    ·
      refine ⟨124332393867619275917736185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331553050313651402447296493 124332393867619275917736185)
      ·
        refine ⟨93249295400714456938302139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124332393867619275917736185 93249295400714456938302139)
        ·
          refine ⟨139873943101071685407453209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93249295400714456938302139 139873943101071685407453209)
          ·
            refine ⟨104905457325803764055589907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139873943101071685407453209 104905457325803764055589907)
            ·
              refine ⟨157358185988705646083384861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104905457325803764055589907 157358185988705646083384861)
              ·
                refine ⟨59009319745764617281269323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157358185988705646083384861 59009319745764617281269323)
                ·
                  refine ⟨88513979618646925921903985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59009319745764617281269323 88513979618646925921903985)
                  ·
                    refine ⟨66385484713985194441427989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88513979618646925921903985 66385484713985194441427989)
                    ·
                      refine ⟨3111819595968055989441937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66385484713985194441427989 3111819595968055989441937)
                      ·
                        rfl

theorem cell23_6060247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_6060247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060247 prefixEnd_6060247 := by exact prefixLift 6060247
  have htrace : WordTrace (prefixWord ++ tailWord_6060247) baseStart_6060247 baseEnd_6060247 := by
    simpa [prefixWord, tailWord_6060247, baseEnd_6060247] using wordTrace_append hprefix tailTrace_6060247
  have hstable : (prefixWord ++ tailWord_6060247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060247).length < 2 ^ (prefixWord ++ tailWord_6060247).sum := by decide
  have hdescent : baseEnd_6060247 < baseStart_6060247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060248 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 1, 4]
def baseStart_6060248 : Nat := 118140960795 + 6060248 * 2 ^ 59
def prefixEnd_6060248 : Nat := 4983230072969 + 3 ^ 40 * 6060248 * 2
def baseEnd_6060248 : Nat := 1037273369816236828509811

theorem tailTrace_6060248 : CollatzResearch.WordTrace tailWord_6060248 prefixEnd_6060248 1037273369816236828509811 := by
  unfold tailWord_6060248
  simp only [CollatzResearch.WordTrace]
  refine ⟨110517701674381989401158699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147356935565842652534878265 110517701674381989401158699)
  ·
    refine ⟨165776552511572984101738049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110517701674381989401158699 165776552511572984101738049)
    ·
      refine ⟨124332414383679738076303537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165776552511572984101738049 124332414383679738076303537)
      ·
        refine ⟨93249310787759803557227653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124332414383679738076303537 93249310787759803557227653)
        ·
          refine ⟨17484245772704963166980185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93249310787759803557227653 17484245772704963166980185)
          ·
            refine ⟨13113184329528722375235139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17484245772704963166980185 13113184329528722375235139)
            ·
              refine ⟨19669776494293083562852709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13113184329528722375235139 19669776494293083562852709)
              ·
                refine ⟨3688083092679953168034883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19669776494293083562852709 3688083092679953168034883)
                ·
                  refine ⟨5532124639019929752052325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688083092679953168034883 5532124639019929752052325)
                  ·
                    refine ⟨1037273369816236828509811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532124639019929752052325 1037273369816236828509811)
                    ·
                      rfl

theorem cell23_6060248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_6060248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060248 prefixEnd_6060248 := by exact prefixLift 6060248
  have htrace : WordTrace (prefixWord ++ tailWord_6060248) baseStart_6060248 baseEnd_6060248 := by
    simpa [prefixWord, tailWord_6060248, baseEnd_6060248] using wordTrace_append hprefix tailTrace_6060248
  have hstable : (prefixWord ++ tailWord_6060248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060248).length < 2 ^ (prefixWord ++ tailWord_6060248).sum := by decide
  have hdescent : baseEnd_6060248 < baseStart_6060248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060267 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_6060267 : Nat := 118140960795 + 6060267 * 2 ^ 59
def prefixEnd_6060267 : Nat := 4983230072969 + 3 ^ 40 * 6060267 * 2
def baseEnd_6060267 : Nat := 3111829865581145911191845

theorem tailTrace_6060267 : CollatzResearch.WordTrace tailWord_6060267 prefixEnd_6060267 3111829865581145911191845 := by
  unfold tailWord_6060267
  simp only [CollatzResearch.WordTrace]
  refine ⟨221036096335695145047259055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147357397557130096698172703 221036096335695145047259055)
  ·
    refine ⟨331554144503542717570888583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221036096335695145047259055 331554144503542717570888583)
    ·
      refine ⟨497331216755314076356332875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331554144503542717570888583 497331216755314076356332875)
      ·
        refine ⟨745996825132971114534499313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497331216755314076356332875 745996825132971114534499313)
        ·
          refine ⟨559497618849728335900874485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745996825132971114534499313 559497618849728335900874485)
          ·
            refine ⟨52452901767162031490706983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 559497618849728335900874485 52452901767162031490706983)
            ·
              refine ⟨78679352650743047236060475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52452901767162031490706983 78679352650743047236060475)
              ·
                refine ⟨118019028976114570854090713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78679352650743047236060475 118019028976114570854090713)
                ·
                  refine ⟨88514271732085928140568035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118019028976114570854090713 88514271732085928140568035)
                  ·
                    refine ⟨132771407598128892210852053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88514271732085928140568035 132771407598128892210852053)
                    ·
                      refine ⟨3111829865581145911191845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132771407598128892210852053 3111829865581145911191845)
                      ·
                        rfl

theorem cell23_6060267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_6060267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060267 prefixEnd_6060267 := by exact prefixLift 6060267
  have htrace : WordTrace (prefixWord ++ tailWord_6060267) baseStart_6060267 baseEnd_6060267 := by
    simpa [prefixWord, tailWord_6060267, baseEnd_6060267] using wordTrace_append hprefix tailTrace_6060267
  have hstable : (prefixWord ++ tailWord_6060267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060267).length < 2 ^ (prefixWord ++ tailWord_6060267).sum := by decide
  have hdescent : baseEnd_6060267 < baseStart_6060267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060271 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_6060271 : Nat := 118140960795 + 6060271 * 2 ^ 59
def prefixEnd_6060271 : Nat := 4983230072969 + 3 ^ 40 * 6060271 * 2
def baseEnd_6060271 : Nat := 3111831919503763895541827

theorem tailTrace_6060271 : CollatzResearch.WordTrace tailWord_6060271 prefixEnd_6060271 3111831919503763895541827 := by
  unfold tailWord_6060271
  simp only [CollatzResearch.WordTrace]
  refine ⟨221036242227680653730404667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147357494818453769153603111 221036242227680653730404667)
  ·
    refine ⟨331554363341520980595607001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221036242227680653730404667 331554363341520980595607001)
    ·
      refine ⟨248665772506140735446705251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331554363341520980595607001 248665772506140735446705251)
      ·
        refine ⟨372998658759211103170057877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248665772506140735446705251 372998658759211103170057877)
        ·
          refine ⟨17484312129338020461096463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 372998658759211103170057877 17484312129338020461096463)
          ·
            refine ⟨26226468194007030691644695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17484312129338020461096463 26226468194007030691644695)
            ·
              refine ⟨39339702291010546037467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26226468194007030691644695 39339702291010546037467043)
              ·
                refine ⟨59009553436515819056200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39339702291010546037467043 59009553436515819056200565)
                ·
                  refine ⟨5532145634673358036518803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59009553436515819056200565 5532145634673358036518803)
                  ·
                    refine ⟨8298218452010037054778205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5532145634673358036518803 8298218452010037054778205)
                    ·
                      refine ⟨3111831919503763895541827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298218452010037054778205 3111831919503763895541827)
                      ·
                        rfl

theorem cell23_6060271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_6060271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060271 prefixEnd_6060271 := by exact prefixLift 6060271
  have htrace : WordTrace (prefixWord ++ tailWord_6060271) baseStart_6060271 baseEnd_6060271 := by
    simpa [prefixWord, tailWord_6060271, baseEnd_6060271] using wordTrace_append hprefix tailTrace_6060271
  have hstable : (prefixWord ++ tailWord_6060271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060271).length < 2 ^ (prefixWord ++ tailWord_6060271).sum := by decide
  have hdescent : baseEnd_6060271 < baseStart_6060271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060281 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 2, 3, 2]
def baseStart_6060281 : Nat := 118140960795 + 6060281 * 2 ^ 59
def prefixEnd_6060281 : Nat := 4983230072969 + 3 ^ 40 * 6060281 * 2
def baseEnd_6060281 : Nat := 3111837054310308856416781

theorem tailTrace_6060281 : CollatzResearch.WordTrace tailWord_6060281 prefixEnd_6060281 3111837054310308856416781 := by
  unfold tailWord_6060281
  simp only [CollatzResearch.WordTrace]
  refine ⟨221036606957644425438268697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147357737971762950292179131 221036606957644425438268697)
  ·
    refine ⟨165777455218233319078701523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221036606957644425438268697 165777455218233319078701523)
    ·
      refine ⟨248666182827349978618052285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165777455218233319078701523 248666182827349978618052285)
      ·
        refine ⟨93249818560256241981769607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248666182827349978618052285 93249818560256241981769607)
        ·
          refine ⟨139874727840384362972654411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93249818560256241981769607 139874727840384362972654411)
          ·
            refine ⟨209812091760576544458981617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139874727840384362972654411 209812091760576544458981617)
            ·
              refine ⟨157359068820432408344236213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209812091760576544458981617 157359068820432408344236213)
              ·
                refine ⟨14752412701915538282272145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157359068820432408344236213 14752412701915538282272145)
                ·
                  refine ⟨11064309526436653711704109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14752412701915538282272145 11064309526436653711704109)
                  ·
                    refine ⟨4149116072413745141889041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11064309526436653711704109 4149116072413745141889041)
                    ·
                      refine ⟨3111837054310308856416781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149116072413745141889041 3111837054310308856416781)
                      ·
                        rfl

theorem cell23_6060281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_6060281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060281 prefixEnd_6060281 := by exact prefixLift 6060281
  have htrace : WordTrace (prefixWord ++ tailWord_6060281) baseStart_6060281 baseEnd_6060281 := by
    simpa [prefixWord, tailWord_6060281, baseEnd_6060281] using wordTrace_append hprefix tailTrace_6060281
  have hstable : (prefixWord ++ tailWord_6060281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060281).length < 2 ^ (prefixWord ++ tailWord_6060281).sum := by decide
  have hdescent : baseEnd_6060281 < baseStart_6060281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060288 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 1, 1, 3]
def baseStart_6060288 : Nat := 118140960795 + 6060288 * 2 ^ 59
def prefixEnd_6060288 : Nat := 4983230072969 + 3 ^ 40 * 6060288 * 2
def baseEnd_6060288 : Nat := 3111840648674890329029249

theorem tailTrace_6060288 : CollatzResearch.WordTrace tailWord_6060288 prefixEnd_6060288 3111840648674890329029249 := by
  unfold tailWord_6060288
  simp only [CollatzResearch.WordTrace]
  refine ⟨110518431134309532816886759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147357908179079377089182345 110518431134309532816886759)
  ·
    refine ⟨165777646701464299225330139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110518431134309532816886759 165777646701464299225330139)
    ·
      refine ⟨248666470052196448837995209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165777646701464299225330139 248666470052196448837995209)
      ·
        refine ⟨186499852539147336628496407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248666470052196448837995209 186499852539147336628496407)
        ·
          refine ⟨279749778808721004942744611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186499852539147336628496407 279749778808721004942744611)
          ·
            refine ⟨419624668213081507414116917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279749778808721004942744611 419624668213081507414116917)
            ·
              refine ⟨39339812644976391320073461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419624668213081507414116917 39339812644976391320073461)
              ·
                refine ⟨3688107435466536686256887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39339812644976391320073461 3688107435466536686256887)
                ·
                  refine ⟨5532161153199805029385331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688107435466536686256887 5532161153199805029385331)
                  ·
                    refine ⟨8298241729799707544077997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5532161153199805029385331 8298241729799707544077997)
                    ·
                      refine ⟨3111840648674890329029249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298241729799707544077997 3111840648674890329029249)
                      ·
                        rfl

theorem cell23_6060288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_6060288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060288 prefixEnd_6060288 := by exact prefixLift 6060288
  have htrace : WordTrace (prefixWord ++ tailWord_6060288) baseStart_6060288 baseEnd_6060288 := by
    simpa [prefixWord, tailWord_6060288, baseEnd_6060288] using wordTrace_append hprefix tailTrace_6060288
  have hstable : (prefixWord ++ tailWord_6060288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060288).length < 2 ^ (prefixWord ++ tailWord_6060288).sum := by decide
  have hdescent : baseEnd_6060288 < baseStart_6060288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060295 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 6]
def baseStart_6060295 : Nat := 118140960795 + 6060295 * 2 ^ 59
def prefixEnd_6060295 : Nat := 4983230072969 + 3 ^ 40 * 6060295 * 2
def baseEnd_6060295 : Nat := 345760471448830200182413

theorem tailTrace_6060295 : CollatzResearch.WordTrace tailWord_6060295 prefixEnd_6060295 345760471448830200182413 := by
  unfold tailWord_6060295
  simp only [CollatzResearch.WordTrace]
  refine ⟨221037117579593705829278339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147358078386395803886185559 221037117579593705829278339)
  ·
    refine ⟨331555676369390558743917509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221037117579593705829278339 331555676369390558743917509)
    ·
      refine ⟨62166689319260729764484533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331555676369390558743917509 62166689319260729764484533)
      ·
        refine ⟨5828127123680693415420425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62166689319260729764484533 5828127123680693415420425)
        ·
          refine ⟨4371095342760520061565319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5828127123680693415420425 4371095342760520061565319)
          ·
            refine ⟨6556643014140780092347979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4371095342760520061565319 6556643014140780092347979)
            ·
              refine ⟨9834964521211170138521969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556643014140780092347979 9834964521211170138521969)
              ·
                refine ⟨7376223390908377603891477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9834964521211170138521969 7376223390908377603891477)
                ·
                  refine ⟨345760471448830200182413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7376223390908377603891477 345760471448830200182413)
                  ·
                    rfl

theorem cell23_6060295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 6].length) (baseStart_6060295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060295 prefixEnd_6060295 := by exact prefixLift 6060295
  have htrace : WordTrace (prefixWord ++ tailWord_6060295) baseStart_6060295 baseEnd_6060295 := by
    simpa [prefixWord, tailWord_6060295, baseEnd_6060295] using wordTrace_append hprefix tailTrace_6060295
  have hstable : (prefixWord ++ tailWord_6060295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060295).length < 2 ^ (prefixWord ++ tailWord_6060295).sum := by decide
  have hdescent : baseEnd_6060295 < baseStart_6060295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060321 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6060321 : Nat := 118140960795 + 6060321 * 2 ^ 59
def prefixEnd_6060321 : Nat := 4983230072969 + 3 ^ 40 * 6060321 * 2
def baseEnd_6060321 : Nat := 1037285864512162899972199

theorem tailTrace_6060321 : CollatzResearch.WordTrace tailWord_6060321 prefixEnd_6060321 1037285864512162899972199 := by
  unfold tailWord_6060321
  simp only [CollatzResearch.WordTrace]
  refine ⟨221038065877499512269724817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147358710584999674846483211 221038065877499512269724817)
  ·
    refine ⟨165778549408124634202293613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221038065877499512269724817 165778549408124634202293613)
    ·
      refine ⟨62166956028046737825860105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165778549408124634202293613 62166956028046737825860105)
      ·
        refine ⟨46625217021035053369395079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62166956028046737825860105 46625217021035053369395079)
        ·
          refine ⟨69937825531552580054092619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46625217021035053369395079 69937825531552580054092619)
          ·
            refine ⟨104906738297328870081138929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69937825531552580054092619 104906738297328870081138929)
            ·
              refine ⟨78680053722996652560854197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104906738297328870081138929 78680053722996652560854197)
              ·
                refine ⟨7376255036530936177580081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78680053722996652560854197 7376255036530936177580081)
                ·
                  refine ⟨5532191277398202133185061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7376255036530936177580081 5532191277398202133185061)
                  ·
                    refine ⟨1037285864512162899972199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532191277398202133185061 1037285864512162899972199)
                    ·
                      rfl

theorem cell23_6060321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6060321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060321 prefixEnd_6060321 := by exact prefixLift 6060321
  have htrace : WordTrace (prefixWord ++ tailWord_6060321) baseStart_6060321 baseEnd_6060321 := by
    simpa [prefixWord, tailWord_6060321, baseEnd_6060321] using wordTrace_append hprefix tailTrace_6060321
  have hstable : (prefixWord ++ tailWord_6060321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060321).length < 2 ^ (prefixWord ++ tailWord_6060321).sum := by decide
  have hdescent : baseEnd_6060321 < baseStart_6060321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060364 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_6060364 : Nat := 118140960795 + 6060364 * 2 ^ 59
def prefixEnd_6060364 : Nat := 4983230072969 + 3 ^ 40 * 6060364 * 2
def baseEnd_6060364 : Nat := 1037293224401544010559633

theorem tailTrace_6060364 : CollatzResearch.WordTrace tailWord_6060364 prefixEnd_6060364 1037293224401544010559633 := by
  unfold tailWord_6060364
  simp only [CollatzResearch.WordTrace]
  refine ⟨110519817108171865306770073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147359756144229153742360097 110519817108171865306770073)
  ·
    refine ⟨82889862831128898980077555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110519817108171865306770073 82889862831128898980077555)
    ·
      refine ⟨124334794246693348470116333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82889862831128898980077555 124334794246693348470116333)
      ·
        refine ⟨46625547842510005676293625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124334794246693348470116333 46625547842510005676293625)
        ·
          refine ⟨34969160881882504257220219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46625547842510005676293625 34969160881882504257220219)
          ·
            refine ⟨52453741322823756385830329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34969160881882504257220219 52453741322823756385830329)
            ·
              refine ⟨39340305992117817289372747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52453741322823756385830329 39340305992117817289372747)
              ·
                refine ⟨59010458988176725934059121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39340305992117817289372747 59010458988176725934059121)
                ·
                  refine ⟨44257844241132544450544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59010458988176725934059121 44257844241132544450544341)
                  ·
                    refine ⟨1037293224401544010559633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44257844241132544450544341 1037293224401544010559633)
                    ·
                      rfl

theorem cell23_6060364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_6060364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060364 prefixEnd_6060364 := by exact prefixLift 6060364
  have htrace : WordTrace (prefixWord ++ tailWord_6060364) baseStart_6060364 baseEnd_6060364 := by
    simpa [prefixWord, tailWord_6060364, baseEnd_6060364] using wordTrace_append hprefix tailTrace_6060364
  have hstable : (prefixWord ++ tailWord_6060364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060364).length < 2 ^ (prefixWord ++ tailWord_6060364).sum := by decide
  have hdescent : baseEnd_6060364 < baseStart_6060364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060388 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_6060388 : Nat := 118140960795 + 6060388 * 2 ^ 59
def prefixEnd_6060388 : Nat := 4983230072969 + 3 ^ 40 * 6060388 * 2
def baseEnd_6060388 : Nat := 3111891996740339937778789

theorem tailTrace_6060388 : CollatzResearch.WordTrace tailWord_6060388 prefixEnd_6060388 3111891996740339937778789 := by
  unfold tailWord_6060388
  simp only [CollatzResearch.WordTrace]
  refine ⟨110520254784128391356206909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147360339712171188474942545 110520254784128391356206909)
  ·
    refine ⟨41445095544048146758577591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110520254784128391356206909 41445095544048146758577591)
    ·
      refine ⟨62167643316072220137866387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41445095544048146758577591 62167643316072220137866387)
      ·
        refine ⟨93251464974108330206799581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62167643316072220137866387 93251464974108330206799581)
        ·
          refine ⟨34969299365290623827549843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93251464974108330206799581 34969299365290623827549843)
          ·
            refine ⟨52453949047935935741324765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34969299365290623827549843 52453949047935935741324765)
            ·
              refine ⟨19670230892975975902996787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52453949047935935741324765 19670230892975975902996787)
              ·
                refine ⟨29505346339463963854495181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19670230892975975902996787 29505346339463963854495181)
                ·
                  refine ⟨11064504877298986445435693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29505346339463963854495181 11064504877298986445435693)
                  ·
                    refine ⟨4149189328987119917038385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11064504877298986445435693 4149189328987119917038385)
                    ·
                      refine ⟨3111891996740339937778789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149189328987119917038385 3111891996740339937778789)
                      ·
                        rfl

theorem cell23_6060388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_6060388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060388 prefixEnd_6060388 := by exact prefixLift 6060388
  have htrace : WordTrace (prefixWord ++ tailWord_6060388) baseStart_6060388 baseEnd_6060388 := by
    simpa [prefixWord, tailWord_6060388, baseEnd_6060388] using wordTrace_append hprefix tailTrace_6060388
  have hstable : (prefixWord ++ tailWord_6060388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060388).length < 2 ^ (prefixWord ++ tailWord_6060388).sum := by decide
  have hdescent : baseEnd_6060388 < baseStart_6060388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060469 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_6060469 : Nat := 118140960795 + 6060469 * 2 ^ 59
def prefixEnd_6060469 : Nat := 4983230072969 + 3 ^ 40 * 6060469 * 2
def baseEnd_6060469 : Nat := 3111933588673354120865917

theorem tailTrace_6060469 : CollatzResearch.WordTrace tailWord_6060469 prefixEnd_6060469 3111933588673354120865917 := by
  unfold tailWord_6060469
  simp only [CollatzResearch.WordTrace]
  refine ⟨221043463880963333546112461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147362309253975555697408307 221043463880963333546112461)
  ·
    refine ⟨82891298955361250079792173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221043463880963333546112461 82891298955361250079792173)
    ·
      refine ⟨31084237108260468779922065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82891298955361250079792173 31084237108260468779922065)
      ·
        refine ⟨23313177831195351584941549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31084237108260468779922065 23313177831195351584941549)
        ·
          refine ⟨8742441686698256844353081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23313177831195351584941549 8742441686698256844353081)
          ·
            refine ⟨6556831265023692633264811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8742441686698256844353081 6556831265023692633264811)
            ·
              refine ⟨9835246897535538949897217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556831265023692633264811 9835246897535538949897217)
              ·
                refine ⟨7376435173151654212422913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9835246897535538949897217 7376435173151654212422913)
                ·
                  refine ⟨5532326379863740659317185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7376435173151654212422913 5532326379863740659317185)
                  ·
                    refine ⟨4149244784897805494487889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5532326379863740659317185 4149244784897805494487889)
                    ·
                      refine ⟨3111933588673354120865917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149244784897805494487889 3111933588673354120865917)
                      ·
                        rfl

theorem cell23_6060469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_6060469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060469 prefixEnd_6060469 := by exact prefixLift 6060469
  have htrace : WordTrace (prefixWord ++ tailWord_6060469) baseStart_6060469 baseEnd_6060469 := by
    simpa [prefixWord, tailWord_6060469, baseEnd_6060469] using wordTrace_append hprefix tailTrace_6060469
  have hstable : (prefixWord ++ tailWord_6060469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060469).length < 2 ^ (prefixWord ++ tailWord_6060469).sum := by decide
  have hdescent : baseEnd_6060469 < baseStart_6060469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060478 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_6060478 : Nat := 118140960795 + 6060478 * 2 ^ 59
def prefixEnd_6060478 : Nat := 4983230072969 + 3 ^ 40 * 6060478 * 2
def baseEnd_6060478 : Nat := 3111938209999244585653375

theorem tailTrace_6060478 : CollatzResearch.WordTrace tailWord_6060478 prefixEnd_6060478 3111938209999244585653375 := by
  unfold tailWord_6060478
  simp only [CollatzResearch.WordTrace]
  refine ⟨27630474017241341010398761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147362528091953818722126725 27630474017241341010398761)
  ·
    refine ⟨20722855512931005757799071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27630474017241341010398761 20722855512931005757799071)
    ·
      refine ⟨31084283269396508636698607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20722855512931005757799071 31084283269396508636698607)
      ·
        refine ⟨46626424904094762955047911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31084283269396508636698607 46626424904094762955047911)
        ·
          refine ⟨69939637356142144432571867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46626424904094762955047911 69939637356142144432571867)
          ·
            refine ⟨104909456034213216648857801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69939637356142144432571867 104909456034213216648857801)
            ·
              refine ⟨78682092025659912486643351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104909456034213216648857801 78682092025659912486643351)
              ·
                refine ⟨118023138038489868729965027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78682092025659912486643351 118023138038489868729965027)
                ·
                  refine ⟨177034707057734803094947541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118023138038489868729965027 177034707057734803094947541)
                  ·
                    refine ⟨4149250946665659447537833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 177034707057734803094947541 4149250946665659447537833)
                    ·
                      refine ⟨3111938209999244585653375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149250946665659447537833 3111938209999244585653375)
                      ·
                        rfl

theorem cell23_6060478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_6060478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060478 prefixEnd_6060478 := by exact prefixLift 6060478
  have htrace : WordTrace (prefixWord ++ tailWord_6060478) baseStart_6060478 baseEnd_6060478 := by
    simpa [prefixWord, tailWord_6060478, baseEnd_6060478] using wordTrace_append hprefix tailTrace_6060478
  have hstable : (prefixWord ++ tailWord_6060478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060478).length < 2 ^ (prefixWord ++ tailWord_6060478).sum := by decide
  have hdescent : baseEnd_6060478 < baseStart_6060478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060525 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6060525 : Nat := 118140960795 + 6060525 * 2 ^ 59
def prefixEnd_6060525 : Nat := 4983230072969 + 3 ^ 40 * 6060525 * 2
def baseEnd_6060525 : Nat := 3111962343590005901765659

theorem tailTrace_6060525 : CollatzResearch.WordTrace tailWord_6060525 prefixEnd_6060525 3111962343590005901765659 := by
  unfold tailWord_6060525
  simp only [CollatzResearch.WordTrace]
  refine ⟨221045506368760455110151029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147363670912506970073434019 221045506368760455110151029)
  ·
    refine ⟨20723016222071292666576659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221045506368760455110151029 20723016222071292666576659)
    ·
      refine ⟨31084524333106938999864989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20723016222071292666576659 31084524333106938999864989)
      ·
        refine ⟨11656696624915102124949371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31084524333106938999864989 11656696624915102124949371)
        ·
          refine ⟨17485044937372653187424057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11656696624915102124949371 17485044937372653187424057)
          ·
            refine ⟨13113783703029489890568043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17485044937372653187424057 13113783703029489890568043)
            ·
              refine ⟨19670675554544234835852065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13113783703029489890568043 19670675554544234835852065)
              ·
                refine ⟨14753006665908176126889049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19670675554544234835852065 14753006665908176126889049)
                ·
                  refine ⟨11064754999431132095166787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14753006665908176126889049 11064754999431132095166787)
                  ·
                    refine ⟨16597132499146698142750181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11064754999431132095166787 16597132499146698142750181)
                    ·
                      refine ⟨3111962343590005901765659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16597132499146698142750181 3111962343590005901765659)
                      ·
                        rfl

theorem cell23_6060525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6060525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060525 prefixEnd_6060525 := by exact prefixLift 6060525
  have htrace : WordTrace (prefixWord ++ tailWord_6060525) baseStart_6060525 baseEnd_6060525 := by
    simpa [prefixWord, tailWord_6060525, baseEnd_6060525] using wordTrace_append hprefix tailTrace_6060525
  have hstable : (prefixWord ++ tailWord_6060525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060525).length < 2 ^ (prefixWord ++ tailWord_6060525).sum := by decide
  have hdescent : baseEnd_6060525 < baseStart_6060525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060528 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_6060528 : Nat := 118140960795 + 6060528 * 2 ^ 59
def prefixEnd_6060528 : Nat := 4983230072969 + 3 ^ 40 * 6060528 * 2
def baseEnd_6060528 : Nat := 3111963884031969390028145

theorem tailTrace_6060528 : CollatzResearch.WordTrace tailWord_6060528 prefixEnd_6060528 3111963884031969390028145 := by
  unfold tailWord_6060528
  simp only [CollatzResearch.WordTrace]
  refine ⟨110522807893874793311255119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147363743858499724415006825 110522807893874793311255119)
  ·
    refine ⟨165784211840812189966882679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110522807893874793311255119 165784211840812189966882679)
    ·
      refine ⟨248676317761218284950324019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165784211840812189966882679 248676317761218284950324019)
      ·
        refine ⟨373014476641827427425486029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248676317761218284950324019 373014476641827427425486029)
        ·
          refine ⟨139880428740685285284557261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373014476641827427425486029 139880428740685285284557261)
          ·
            refine ⟨52455160777756981981708973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139880428740685285284557261 52455160777756981981708973)
            ·
              refine ⟨19670685291658868243140865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52455160777756981981708973 19670685291658868243140865)
              ·
                refine ⟨14753013968744151182355649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19670685291658868243140865 14753013968744151182355649)
                ·
                  refine ⟨11064760476558113386766737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14753013968744151182355649 11064760476558113386766737)
                  ·
                    refine ⟨8298570357418585040075053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11064760476558113386766737 8298570357418585040075053)
                    ·
                      refine ⟨3111963884031969390028145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298570357418585040075053 3111963884031969390028145)
                      ·
                        rfl

theorem cell23_6060528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_6060528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060528 prefixEnd_6060528 := by exact prefixLift 6060528
  have htrace : WordTrace (prefixWord ++ tailWord_6060528) baseStart_6060528 baseEnd_6060528 := by
    simpa [prefixWord, tailWord_6060528, baseEnd_6060528] using wordTrace_append hprefix tailTrace_6060528
  have hstable : (prefixWord ++ tailWord_6060528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060528).length < 2 ^ (prefixWord ++ tailWord_6060528).sum := by decide
  have hdescent : baseEnd_6060528 < baseStart_6060528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060531 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 6]
def baseStart_6060531 : Nat := 118140960795 + 6060531 * 2 ^ 59
def prefixEnd_6060531 : Nat := 4983230072969 + 3 ^ 40 * 6060531 * 2
def baseEnd_6060531 : Nat := 345773936052659208698959

theorem tailTrace_6060531 : CollatzResearch.WordTrace tailWord_6060531 prefixEnd_6060531 345773936052659208698959 := by
  unfold tailWord_6060531
  simp only [CollatzResearch.WordTrace]
  refine ⟨221045725206738718134869447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147363816804492478756579631 221045725206738718134869447)
  ·
    refine ⟨331568587810108077202304171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221045725206738718134869447 331568587810108077202304171)
    ·
      refine ⟨497352881715162115803456257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331568587810108077202304171 497352881715162115803456257)
      ·
        refine ⟨373014661286371586852592193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497352881715162115803456257 373014661286371586852592193)
        ·
          refine ⟨279760995964778690139444145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373014661286371586852592193 279760995964778690139444145)
          ·
            refine ⟨209820746973584017604583109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279760995964778690139444145 209820746973584017604583109)
            ·
              refine ⟨39341390057547003300859333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209820746973584017604583109 39341390057547003300859333)
              ·
                refine ⟨7376510635790063118911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39341390057547003300859333 7376510635790063118911125)
                ·
                  refine ⟨345773936052659208698959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7376510635790063118911125 345773936052659208698959)
                  ·
                    rfl

theorem cell23_6060531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 6].length) (baseStart_6060531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060531 prefixEnd_6060531 := by exact prefixLift 6060531
  have htrace : WordTrace (prefixWord ++ tailWord_6060531) baseStart_6060531 baseEnd_6060531 := by
    simpa [prefixWord, tailWord_6060531, baseEnd_6060531] using wordTrace_append hprefix tailTrace_6060531
  have hstable : (prefixWord ++ tailWord_6060531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060531).length < 2 ^ (prefixWord ++ tailWord_6060531).sum := by decide
  have hdescent : baseEnd_6060531 < baseStart_6060531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060611 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_6060611 : Nat := 118140960795 + 6060611 * 2 ^ 59
def prefixEnd_6060611 : Nat := 4983230072969 + 3 ^ 40 * 6060611 * 2
def baseEnd_6060611 : Nat := 3112006502926292565290263

theorem tailTrace_6060611 : CollatzResearch.WordTrace tailWord_6060611 prefixEnd_6060611 3112006502926292565290263 := by
  unfold tailWord_6060611
  simp only [CollatzResearch.WordTrace]
  refine ⟨221048643046448891797781687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147365762030965927865187791 221048643046448891797781687)
  ·
    refine ⟨331572964569673337696672531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221048643046448891797781687 331572964569673337696672531)
    ·
      refine ⟨497359446854510006545008797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331572964569673337696672531 497359446854510006545008797)
      ·
        refine ⟨186509792570441252454378299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497359446854510006545008797 186509792570441252454378299)
        ·
          refine ⟨279764688855661878681567449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186509792570441252454378299 279764688855661878681567449)
          ·
            refine ⟨209823516641746409011175587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279764688855661878681567449 209823516641746409011175587)
            ·
              refine ⟨314735274962619613516763381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209823516641746409011175587 314735274962619613516763381)
              ·
                refine ⟨29506432027745588767196567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314735274962619613516763381 29506432027745588767196567)
                ·
                  refine ⟨44259648041618383150794851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29506432027745588767196567 44259648041618383150794851)
                  ·
                    refine ⟨66389472062427574726192277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44259648041618383150794851 66389472062427574726192277)
                    ·
                      refine ⟨3112006502926292565290263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66389472062427574726192277 3112006502926292565290263)
                      ·
                        rfl

theorem cell23_6060611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_6060611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060611 prefixEnd_6060611 := by exact prefixLift 6060611
  have htrace : WordTrace (prefixWord ++ tailWord_6060611) baseStart_6060611 baseEnd_6060611 := by
    simpa [prefixWord, tailWord_6060611, baseEnd_6060611] using wordTrace_append hprefix tailTrace_6060611
  have hstable : (prefixWord ++ tailWord_6060611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060611).length < 2 ^ (prefixWord ++ tailWord_6060611).sum := by decide
  have hdescent : baseEnd_6060611 < baseStart_6060611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060651 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 7]
def baseStart_6060651 : Nat := 118140960795 + 6060651 * 2 ^ 59
def prefixEnd_6060651 : Nat := 4983230072969 + 3 ^ 40 * 6060651 * 2
def baseEnd_6060651 : Nat := 1037342347384157469596693

theorem tailTrace_6060651 : CollatzResearch.WordTrace tailWord_6060651 prefixEnd_6060651 1037342347384157469596693 := by
  unfold tailWord_6060651
  simp only [CollatzResearch.WordTrace]
  refine ⟨221050101966303978629237807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147366734644202652419491871 221050101966303978629237807)
  ·
    refine ⟨331575152949455967943856711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221050101966303978629237807 331575152949455967943856711)
    ·
      refine ⟨497362729424183951915785067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331575152949455967943856711 497362729424183951915785067)
      ·
        refine ⟨746044094136275927873677601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497362729424183951915785067 746044094136275927873677601)
        ·
          refine ⟨559533070602206945905258201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746044094136275927873677601 559533070602206945905258201)
          ·
            refine ⟨419649802951655209428943651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559533070602206945905258201 419649802951655209428943651)
            ·
              refine ⟨629474704427482814143415477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419649802951655209428943651 629474704427482814143415477)
              ·
                refine ⟨59013253540076513825945201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629474704427482814143415477 59013253540076513825945201)
                ·
                  refine ⟨44259940155057385369458901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59013253540076513825945201 44259940155057385369458901)
                  ·
                    refine ⟨1037342347384157469596693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44259940155057385369458901 1037342347384157469596693)
                    ·
                      rfl

theorem cell23_6060651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_6060651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060651 prefixEnd_6060651 := by exact prefixLift 6060651
  have htrace : WordTrace (prefixWord ++ tailWord_6060651) baseStart_6060651 baseEnd_6060651 := by
    simpa [prefixWord, tailWord_6060651, baseEnd_6060651] using wordTrace_append hprefix tailTrace_6060651
  have hstable : (prefixWord ++ tailWord_6060651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060651).length < 2 ^ (prefixWord ++ tailWord_6060651).sum := by decide
  have hdescent : baseEnd_6060651 < baseStart_6060651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060665 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_6060665 : Nat := 118140960795 + 6060665 * 2 ^ 59
def prefixEnd_6060665 : Nat := 4983230072969 + 3 ^ 40 * 6060665 * 2
def baseEnd_6060665 : Nat := 3112034230881635354015015

theorem tailTrace_6060665 : CollatzResearch.WordTrace tailWord_6060665 prefixEnd_6060665 3112034230881635354015015 := by
  unfold tailWord_6060665
  simp only [CollatzResearch.WordTrace]
  refine ⟨221050612588253259020247449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147367075058835506013498299 221050612588253259020247449)
  ·
    refine ⟨165787959441189944265185587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221050612588253259020247449 165787959441189944265185587)
    ·
      refine ⟨248681939161784916397778381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165787959441189944265185587 248681939161784916397778381)
      ·
        refine ⟨93255727185669343649166893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248681939161784916397778381 93255727185669343649166893)
        ·
          refine ⟨34970897694626003868437585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93255727185669343649166893 34970897694626003868437585)
          ·
            refine ⟨26228173270969502901328189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34970897694626003868437585 26228173270969502901328189)
            ·
              refine ⟨9835564976613563587998071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26228173270969502901328189 9835564976613563587998071)
              ·
                refine ⟨14753347464920345381997107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9835564976613563587998071 14753347464920345381997107)
                ·
                  refine ⟨22130021197380518072995661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14753347464920345381997107 22130021197380518072995661)
                  ·
                    refine ⟨8298757949017694277373373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22130021197380518072995661 8298757949017694277373373)
                    ·
                      refine ⟨3112034230881635354015015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298757949017694277373373 3112034230881635354015015)
                      ·
                        rfl

theorem cell23_6060665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_6060665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060665 prefixEnd_6060665 := by exact prefixLift 6060665
  have htrace : WordTrace (prefixWord ++ tailWord_6060665) baseStart_6060665 baseEnd_6060665 := by
    simpa [prefixWord, tailWord_6060665, baseEnd_6060665] using wordTrace_append hprefix tailTrace_6060665
  have hstable : (prefixWord ++ tailWord_6060665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060665).length < 2 ^ (prefixWord ++ tailWord_6060665).sum := by decide
  have hdescent : baseEnd_6060665 < baseStart_6060665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060671 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_6060671 : Nat := 118140960795 + 6060671 * 2 ^ 59
def prefixEnd_6060671 : Nat := 4983230072969 + 3 ^ 40 * 6060671 * 2
def baseEnd_6060671 : Nat := 3112037311765562330539987

theorem tailTrace_6060671 : CollatzResearch.WordTrace tailWord_6060671 prefixEnd_6060671 3112037311765562330539987 := by
  unfold tailWord_6060671
  simp only [CollatzResearch.WordTrace]
  refine ⟨221050831426231522044965867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147367220950821014696643911 221050831426231522044965867)
  ·
    refine ⟨331576247139347283067448801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221050831426231522044965867 331576247139347283067448801)
    ·
      refine ⟨248682185354510462300586601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331576247139347283067448801 248682185354510462300586601)
      ·
        refine ⟨186511639015882846725439951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248682185354510462300586601 186511639015882846725439951)
        ·
          refine ⟨279767458523824270088159927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186511639015882846725439951 279767458523824270088159927)
          ·
            refine ⟨419651187785736405132239891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279767458523824270088159927 419651187785736405132239891)
            ·
              refine ⟨629476781678604607698359837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419651187785736405132239891 629476781678604607698359837)
              ·
                refine ⟨236053793129476727886884939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629476781678604607698359837 236053793129476727886884939)
                ·
                  refine ⟨354080689694215091830327409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236053793129476727886884939 354080689694215091830327409)
                  ·
                    refine ⟨265560517270661318872745557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354080689694215091830327409 265560517270661318872745557)
                    ·
                      refine ⟨3112037311765562330539987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265560517270661318872745557 3112037311765562330539987)
                      ·
                        rfl

theorem cell23_6060671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_6060671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060671 prefixEnd_6060671 := by exact prefixLift 6060671
  have htrace : WordTrace (prefixWord ++ tailWord_6060671) baseStart_6060671 baseEnd_6060671 := by
    simpa [prefixWord, tailWord_6060671, baseEnd_6060671] using wordTrace_append hprefix tailTrace_6060671
  have hstable : (prefixWord ++ tailWord_6060671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060671).length < 2 ^ (prefixWord ++ tailWord_6060671).sum := by decide
  have hdescent : baseEnd_6060671 < baseStart_6060671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060675 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 3, 3, 2]
def baseStart_6060675 : Nat := 118140960795 + 6060675 * 2 ^ 59
def prefixEnd_6060675 : Nat := 4983230072969 + 3 ^ 40 * 6060675 * 2
def baseEnd_6060675 : Nat := 3112039365688180314889969

theorem tailTrace_6060675 : CollatzResearch.WordTrace tailWord_6060675 prefixEnd_6060675 3112039365688180314889969 := by
  unfold tailWord_6060675
  simp only [CollatzResearch.WordTrace]
  refine ⟨221050977318217030728111479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147367318212144687152074319 221050977318217030728111479)
  ·
    refine ⟨331576465977325546092167219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221050977318217030728111479 331576465977325546092167219)
    ·
      refine ⟨497364698965988319138250829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331576465977325546092167219 497364698965988319138250829)
      ·
        refine ⟨186511762112245619676844061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497364698965988319138250829 186511762112245619676844061)
        ·
          refine ⟨69941910792092107378816523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186511762112245619676844061 69941910792092107378816523)
          ·
            refine ⟨104912866188138161068224785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69941910792092107378816523 104912866188138161068224785)
            ·
              refine ⟨78684649641103620801168589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104912866188138161068224785 78684649641103620801168589)
              ·
                refine ⟨29506743615413857800438221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78684649641103620801168589 29506743615413857800438221)
                ·
                  refine ⟨11065028855780196675164333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29506743615413857800438221 11065028855780196675164333)
                  ·
                    refine ⟨4149385820917573753186625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11065028855780196675164333 4149385820917573753186625)
                    ·
                      refine ⟨3112039365688180314889969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149385820917573753186625 3112039365688180314889969)
                      ·
                        rfl

theorem cell23_6060675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_6060675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060675 prefixEnd_6060675 := by exact prefixLift 6060675
  have htrace : WordTrace (prefixWord ++ tailWord_6060675) baseStart_6060675 baseEnd_6060675 := by
    simpa [prefixWord, tailWord_6060675, baseEnd_6060675] using wordTrace_append hprefix tailTrace_6060675
  have hstable : (prefixWord ++ tailWord_6060675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060675).length < 2 ^ (prefixWord ++ tailWord_6060675).sum := by decide
  have hdescent : baseEnd_6060675 < baseStart_6060675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060708 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_6060708 : Nat := 118140960795 + 6060708 * 2 ^ 59
def prefixEnd_6060708 : Nat := 4983230072969 + 3 ^ 40 * 6060708 * 2
def baseEnd_6060708 : Nat := 3112056310549778685777317

theorem tailTrace_6060708 : CollatzResearch.WordTrace tailWord_6060708 prefixEnd_6060708 3112056310549778685777317 := by
  unfold tailWord_6060708
  simp only [CollatzResearch.WordTrace]
  refine ⟨110526090463548738682031389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147368120618064984909375185 110526090463548738682031389)
  ·
    refine ⟨41447283923830777005761771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110526090463548738682031389 41447283923830777005761771)
    ·
      refine ⟨62170925885746165508642657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41447283923830777005761771 62170925885746165508642657)
      ·
        refine ⟨46628194414309624131481993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62170925885746165508642657 46628194414309624131481993)
        ·
          refine ⟨34971145810732218098611495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46628194414309624131481993 34971145810732218098611495)
          ·
            refine ⟨52456718716098327147917243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34971145810732218098611495 52456718716098327147917243)
            ·
              refine ⟨78685078074147490721875865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52456718716098327147917243 78685078074147490721875865)
              ·
                refine ⟨59013808555610618041406899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78685078074147490721875865 59013808555610618041406899)
                ·
                  refine ⟨88520712833415927062110349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59013808555610618041406899 88520712833415927062110349)
                  ·
                    refine ⟨33195267312530972648291381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88520712833415927062110349 33195267312530972648291381)
                    ·
                      refine ⟨3112056310549778685777317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33195267312530972648291381 3112056310549778685777317)
                      ·
                        rfl

theorem cell23_6060708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_6060708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060708 prefixEnd_6060708 := by exact prefixLift 6060708
  have htrace : WordTrace (prefixWord ++ tailWord_6060708) baseStart_6060708 baseEnd_6060708 := by
    simpa [prefixWord, tailWord_6060708, baseEnd_6060708] using wordTrace_append hprefix tailTrace_6060708
  have hstable : (prefixWord ++ tailWord_6060708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060708).length < 2 ^ (prefixWord ++ tailWord_6060708).sum := by decide
  have hdescent : baseEnd_6060708 < baseStart_6060708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060725 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6060725 : Nat := 118140960795 + 6060725 * 2 ^ 59
def prefixEnd_6060725 : Nat := 4983230072969 + 3 ^ 40 * 6060725 * 2
def baseEnd_6060725 : Nat := 3112065039720905119264739

theorem tailTrace_6060725 : CollatzResearch.WordTrace tailWord_6060725 prefixEnd_6060725 3112065039720905119264739 := by
  unfold tailWord_6060725
  simp only [CollatzResearch.WordTrace]
  refine ⟨221052800968035889267431629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147368533978690592844954419 221052800968035889267431629)
  ·
    refine ⟨82894800363013458475286861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221052800968035889267431629 82894800363013458475286861)
    ·
      refine ⟨31085550136130046928232573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82894800363013458475286861 31085550136130046928232573)
      ·
        refine ⟨11657081301048767598087215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31085550136130046928232573 11657081301048767598087215)
        ·
          refine ⟨17485621951573151397130823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11657081301048767598087215 17485621951573151397130823)
          ·
            refine ⟨26228432927359727095696235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17485621951573151397130823 26228432927359727095696235)
            ·
              refine ⟨39342649391039590643544353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26228432927359727095696235 39342649391039590643544353)
              ·
                refine ⟨29506987043279692982658265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39342649391039590643544353 29506987043279692982658265)
                ·
                  refine ⟨22130240282459769736993699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29506987043279692982658265 22130240282459769736993699)
                  ·
                    refine ⟨33195360423689654605490549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22130240282459769736993699 33195360423689654605490549)
                    ·
                      refine ⟨3112065039720905119264739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33195360423689654605490549 3112065039720905119264739)
                      ·
                        rfl

theorem cell23_6060725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6060725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060725 prefixEnd_6060725 := by exact prefixLift 6060725
  have htrace : WordTrace (prefixWord ++ tailWord_6060725) baseStart_6060725 baseEnd_6060725 := by
    simpa [prefixWord, tailWord_6060725, baseEnd_6060725] using wordTrace_append hprefix tailTrace_6060725
  have hstable : (prefixWord ++ tailWord_6060725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060725).length < 2 ^ (prefixWord ++ tailWord_6060725).sum := by decide
  have hdescent : baseEnd_6060725 < baseStart_6060725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060726 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6060726 : Nat := 118140960795 + 6060726 * 2 ^ 59
def prefixEnd_6060726 : Nat := 4983230072969 + 3 ^ 40 * 6060726 * 2
def baseEnd_6060726 : Nat := 3112065553201559615352235

theorem tailTrace_6060726 : CollatzResearch.WordTrace tailWord_6060726 prefixEnd_6060726 3112065553201559615352235 := by
  unfold tailWord_6060726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815802340064516652388627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147368558294021510958812021 13815802340064516652388627)
  ·
    refine ⟨20723703510096774978582941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13815802340064516652388627 20723703510096774978582941)
    ·
      refine ⟨7771388816286290616968603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20723703510096774978582941 7771388816286290616968603)
      ·
        refine ⟨11657083224429435925452905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771388816286290616968603 11657083224429435925452905)
        ·
          refine ⟨8742812418322076944089679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11657083224429435925452905 8742812418322076944089679)
          ·
            refine ⟨13114218627483115416134519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8742812418322076944089679 13114218627483115416134519)
            ·
              refine ⟨19671327941224673124201779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13114218627483115416134519 19671327941224673124201779)
              ·
                refine ⟨29506991911837009686302669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19671327941224673124201779 29506991911837009686302669)
                ·
                  refine ⟨11065121966938878632363501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29506991911837009686302669 11065121966938878632363501)
                  ·
                    refine ⟨4149420737602079487136313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11065121966938878632363501 4149420737602079487136313)
                    ·
                      refine ⟨3112065553201559615352235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149420737602079487136313 3112065553201559615352235)
                      ·
                        rfl

theorem cell23_6060726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6060726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060726 prefixEnd_6060726 := by exact prefixLift 6060726
  have htrace : WordTrace (prefixWord ++ tailWord_6060726) baseStart_6060726 baseEnd_6060726 := by
    simpa [prefixWord, tailWord_6060726, baseEnd_6060726] using wordTrace_append hprefix tailTrace_6060726
  have hstable : (prefixWord ++ tailWord_6060726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060726).length < 2 ^ (prefixWord ++ tailWord_6060726).sum := by decide
  have hdescent : baseEnd_6060726 < baseStart_6060726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060815 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_6060815 : Nat := 118140960795 + 6060815 * 2 ^ 59
def prefixEnd_6060815 : Nat := 4983230072969 + 3 ^ 40 * 6060815 * 2
def baseEnd_6060815 : Nat := 3112111252979809767139325

theorem tailTrace_6060815 : CollatzResearch.WordTrace tailWord_6060815 prefixEnd_6060815 3112111252979809767139325 := by
  unfold tailWord_6060815
  simp only [CollatzResearch.WordTrace]
  refine ⟨221056083537709834638207899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147370722358473223092138599 221056083537709834638207899)
  ·
    refine ⟨331584125306564751957311849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221056083537709834638207899 331584125306564751957311849)
    ·
      refine ⟨248688093979923563967983887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331584125306564751957311849 248688093979923563967983887)
      ·
        refine ⟨373032140969885345951975831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248688093979923563967983887 373032140969885345951975831)
        ·
          refine ⟨559548211454828018927963747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373032140969885345951975831 559548211454828018927963747)
          ·
            refine ⟨839322317182242028391945621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559548211454828018927963747 839322317182242028391945621)
            ·
              refine ⟨39343233617917595080872451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 839322317182242028391945621 39343233617917595080872451)
              ·
                refine ⟨59014850426876392621308677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39343233617917595080872451 59014850426876392621308677)
                ·
                  refine ⟨11065284455039323616495377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59014850426876392621308677 11065284455039323616495377)
                  ·
                    refine ⟨8298963341279492712371533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11065284455039323616495377 8298963341279492712371533)
                    ·
                      refine ⟨3112111252979809767139325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8298963341279492712371533 3112111252979809767139325)
                      ·
                        rfl

theorem cell23_6060815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_6060815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060815 prefixEnd_6060815 := by exact prefixLift 6060815
  have htrace : WordTrace (prefixWord ++ tailWord_6060815) baseStart_6060815 baseEnd_6060815 := by
    simpa [prefixWord, tailWord_6060815, baseEnd_6060815] using wordTrace_append hprefix tailTrace_6060815
  have hstable : (prefixWord ++ tailWord_6060815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060815).length < 2 ^ (prefixWord ++ tailWord_6060815).sum := by decide
  have hdescent : baseEnd_6060815 < baseStart_6060815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060848 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_6060848 : Nat := 118140960795 + 6060848 * 2 ^ 59
def prefixEnd_6060848 : Nat := 4983230072969 + 3 ^ 40 * 6060848 * 2
def baseEnd_6060848 : Nat := 1037376065947136046008891

theorem tailTrace_6060848 : CollatzResearch.WordTrace tailWord_6060848 prefixEnd_6060848 1037376065947136046008891 := by
  unfold tailWord_6060848
  simp only [CollatzResearch.WordTrace]
  refine ⟨110528643573295140637079599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147371524764393520849439465 110528643573295140637079599)
  ·
    refine ⟨165792965359942710955619399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110528643573295140637079599 165792965359942710955619399)
    ·
      refine ⟨248689448039914066433429099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165792965359942710955619399 248689448039914066433429099)
      ·
        refine ⟨373034172059871099650143649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248689448039914066433429099 373034172059871099650143649)
        ·
          refine ⟨279775629044903324737607737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373034172059871099650143649 279775629044903324737607737)
          ·
            refine ⟨209831721783677493553205803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279775629044903324737607737 209831721783677493553205803)
            ·
              refine ⟨314747582675516240329808705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209831721783677493553205803 314747582675516240329808705)
              ·
                refine ⟨236060687006637180247356529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314747582675516240329808705 236060687006637180247356529)
                ·
                  refine ⟨177045515254977885185517397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236060687006637180247356529 177045515254977885185517397)
                  ·
                    refine ⟨1037376065947136046008891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177045515254977885185517397 1037376065947136046008891)
                    ·
                      rfl

theorem cell23_6060848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_6060848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060848 prefixEnd_6060848 := by exact prefixLift 6060848
  have htrace : WordTrace (prefixWord ++ tailWord_6060848) baseStart_6060848 baseEnd_6060848 := by
    simpa [prefixWord, tailWord_6060848, baseEnd_6060848] using wordTrace_append hprefix tailTrace_6060848
  have hstable : (prefixWord ++ tailWord_6060848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060848).length < 2 ^ (prefixWord ++ tailWord_6060848).sum := by decide
  have hdescent : baseEnd_6060848 < baseStart_6060848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060895 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 6]
def baseStart_6060895 : Nat := 118140960795 + 6060895 * 2 ^ 59
def prefixEnd_6060895 : Nat := 4983230072969 + 3 ^ 40 * 6060895 * 2
def baseEnd_6060895 : Nat := 1037384110477389818046319

theorem tailTrace_6060895 : CollatzResearch.WordTrace tailWord_6060895 prefixEnd_6060895 1037384110477389818046319 := by
  unfold tailWord_6060895
  simp only [CollatzResearch.WordTrace]
  refine ⟨221059001377420008301120139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147372667584946672200746759 221059001377420008301120139)
  ·
    refine ⟨331588502066130012451680209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221059001377420008301120139 331588502066130012451680209)
    ·
      refine ⟨248691376549597509338760157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331588502066130012451680209 248691376549597509338760157)
      ·
        refine ⟨93259266206099066002035059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248691376549597509338760157 93259266206099066002035059)
        ·
          refine ⟨139888899309148599003052589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93259266206099066002035059 139888899309148599003052589)
          ·
            refine ⟨52458337240930724626144721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139888899309148599003052589 52458337240930724626144721)
            ·
              refine ⟨39343752930698043469608541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52458337240930724626144721 39343752930698043469608541)
              ·
                refine ⟨14753907349011766301103203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39343752930698043469608541 14753907349011766301103203)
                ·
                  refine ⟨22130861023517649451654805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14753907349011766301103203 22130861023517649451654805)
                  ·
                    refine ⟨1037384110477389818046319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22130861023517649451654805 1037384110477389818046319)
                    ·
                      rfl

theorem cell23_6060895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_6060895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060895 prefixEnd_6060895 := by exact prefixLift 6060895
  have htrace : WordTrace (prefixWord ++ tailWord_6060895) baseStart_6060895 baseEnd_6060895 := by
    simpa [prefixWord, tailWord_6060895, baseEnd_6060895] using wordTrace_append hprefix tailTrace_6060895
  have hstable : (prefixWord ++ tailWord_6060895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060895).length < 2 ^ (prefixWord ++ tailWord_6060895).sum := by decide
  have hdescent : baseEnd_6060895 < baseStart_6060895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060899 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 1, 5]
def baseStart_6060899 : Nat := 118140960795 + 6060899 * 2 ^ 59
def prefixEnd_6060899 : Nat := 4983230072969 + 3 ^ 40 * 6060899 * 2
def baseEnd_6060899 : Nat := 1037384795118262479496313

theorem tailTrace_6060899 : CollatzResearch.WordTrace tailWord_6060899 prefixEnd_6060899 1037384795118262479496313 := by
  unfold tailWord_6060899
  simp only [CollatzResearch.WordTrace]
  refine ⟨221059147269405516984265751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147372764846270344656177167 221059147269405516984265751)
  ·
    refine ⟨331588720904108275476398627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221059147269405516984265751 331588720904108275476398627)
    ·
      refine ⟨497383081356162413214597941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331588720904108275476398627 497383081356162413214597941)
      ·
        refine ⟨46629663877140226238868557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 497383081356162413214597941 46629663877140226238868557)
        ·
          refine ⟨17486123953927584839575709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46629663877140226238868557 17486123953927584839575709)
          ·
            refine ⟨6557296482722844314840891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17486123953927584839575709 6557296482722844314840891)
            ·
              refine ⟨9835944724084266472261337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6557296482722844314840891 9835944724084266472261337)
              ·
                refine ⟨7376958543063199854196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9835944724084266472261337 7376958543063199854196003)
                ·
                  refine ⟨11065437814594799781294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7376958543063199854196003 11065437814594799781294005)
                  ·
                    refine ⟨1037384795118262479496313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11065437814594799781294005 1037384795118262479496313)
                    ·
                      rfl

theorem cell23_6060899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 5].length) (baseStart_6060899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060899 prefixEnd_6060899 := by exact prefixLift 6060899
  have htrace : WordTrace (prefixWord ++ tailWord_6060899) baseStart_6060899 baseEnd_6060899 := by
    simpa [prefixWord, tailWord_6060899, baseEnd_6060899] using wordTrace_append hprefix tailTrace_6060899
  have hstable : (prefixWord ++ tailWord_6060899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060899).length < 2 ^ (prefixWord ++ tailWord_6060899).sum := by decide
  have hdescent : baseEnd_6060899 < baseStart_6060899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060915 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_6060915 : Nat := 118140960795 + 6060915 * 2 ^ 59
def prefixEnd_6060915 : Nat := 4983230072969 + 3 ^ 40 * 6060915 * 2
def baseEnd_6060915 : Nat := 3112162601045259375888865

theorem tailTrace_6060915 : CollatzResearch.WordTrace tailWord_6060915 prefixEnd_6060915 3112162601045259375888865 := by
  unfold tailWord_6060915
  simp only [CollatzResearch.WordTrace]
  refine ⟨221059730837347551716848199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147373153891565034477898799 221059730837347551716848199)
  ·
    refine ⟨331589596256021327575272299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221059730837347551716848199 331589596256021327575272299)
    ·
      refine ⟨497384394384031991362908449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331589596256021327575272299 497384394384031991362908449)
      ·
        refine ⟨373038295788023993522181337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497384394384031991362908449 373038295788023993522181337)
        ·
          refine ⟨279778721841017995141636003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373038295788023993522181337 279778721841017995141636003)
          ·
            refine ⟨419668082761526992712454005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279778721841017995141636003 419668082761526992712454005)
            ·
              refine ⟨39343882758893155566792563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419668082761526992712454005 39343882758893155566792563)
              ·
                refine ⟨59015824138339733350188845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39343882758893155566792563 59015824138339733350188845)
                ·
                  refine ⟨22130934051877400006320817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59015824138339733350188845 22130934051877400006320817)
                  ·
                    refine ⟨16598200538908050004740613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22130934051877400006320817 16598200538908050004740613)
                    ·
                      refine ⟨3112162601045259375888865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16598200538908050004740613 3112162601045259375888865)
                      ·
                        rfl

theorem cell23_6060915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_6060915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060915 prefixEnd_6060915 := by exact prefixLift 6060915
  have htrace : WordTrace (prefixWord ++ tailWord_6060915) baseStart_6060915 baseEnd_6060915 := by
    simpa [prefixWord, tailWord_6060915, baseEnd_6060915] using wordTrace_append hprefix tailTrace_6060915
  have hstable : (prefixWord ++ tailWord_6060915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060915).length < 2 ^ (prefixWord ++ tailWord_6060915).sum := by decide
  have hdescent : baseEnd_6060915 < baseStart_6060915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060973 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6060973 : Nat := 118140960795 + 6060973 * 2 ^ 59
def prefixEnd_6060973 : Nat := 4983230072969 + 3 ^ 40 * 6060973 * 2
def baseEnd_6060973 : Nat := 3112192382923220148963599

theorem tailTrace_6060973 : CollatzResearch.WordTrace tailWord_6060973 prefixEnd_6060973 3112192382923220148963599 := by
  unfold tailWord_6060973
  simp only [CollatzResearch.WordTrace]
  refine ⟨221061846271137427622459573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147374564180758285081639715 221061846271137427622459573)
  ·
    refine ⟨20724548087919133839605585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221061846271137427622459573 20724548087919133839605585)
    ·
      refine ⟨15543411065939350379704189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20724548087919133839605585 15543411065939350379704189)
      ·
        refine ⟨5828779149727256392389071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15543411065939350379704189 5828779149727256392389071)
        ·
          refine ⟨8743168724590884588583607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828779149727256392389071 8743168724590884588583607)
          ·
            refine ⟨13114753086886326882875411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743168724590884588583607 13114753086886326882875411)
            ·
              refine ⟨19672129630329490324313117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13114753086886326882875411 19672129630329490324313117)
              ·
                refine ⟨7377048611373558871617419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19672129630329490324313117 7377048611373558871617419)
                ·
                  refine ⟨11065572917060338307426129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377048611373558871617419 11065572917060338307426129)
                  ·
                    refine ⟨8299179687795253730569597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11065572917060338307426129 8299179687795253730569597)
                    ·
                      refine ⟨3112192382923220148963599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299179687795253730569597 3112192382923220148963599)
                      ·
                        rfl

theorem cell23_6060973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6060973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060973 prefixEnd_6060973 := by exact prefixLift 6060973
  have htrace : WordTrace (prefixWord ++ tailWord_6060973) baseStart_6060973 baseEnd_6060973 := by
    simpa [prefixWord, tailWord_6060973, baseEnd_6060973] using wordTrace_append hprefix tailTrace_6060973
  have hstable : (prefixWord ++ tailWord_6060973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060973).length < 2 ^ (prefixWord ++ tailWord_6060973).sum := by decide
  have hdescent : baseEnd_6060973 < baseStart_6060973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060975 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_6060975 : Nat := 118140960795 + 6060975 * 2 ^ 59
def prefixEnd_6060975 : Nat := 4983230072969 + 3 ^ 40 * 6060975 * 2
def baseEnd_6060975 : Nat := 3112193409884529141138589

theorem tailTrace_6060975 : CollatzResearch.WordTrace tailWord_6060975 prefixEnd_6060975 3112193409884529141138589 := by
  unfold tailWord_6060975
  simp only [CollatzResearch.WordTrace]
  refine ⟨221061919217130181964032379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147374612811420121309354919 221061919217130181964032379)
  ·
    refine ⟨331592878825695272946048569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221061919217130181964032379 331592878825695272946048569)
    ·
      refine ⟨248694659119271454709536427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331592878825695272946048569 248694659119271454709536427)
      ·
        refine ⟨373041988678907182064304641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248694659119271454709536427 373041988678907182064304641)
        ·
          refine ⟨279781491509180386548228481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373041988678907182064304641 279781491509180386548228481)
          ·
            refine ⟨209836118631885289911171361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279781491509180386548228481 209836118631885289911171361)
            ·
              refine ⟨157377088973913967433378521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209836118631885289911171361 157377088973913967433378521)
              ·
                refine ⟨118032816730435475575033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157377088973913967433378521 118032816730435475575033891)
                ·
                  refine ⟨177049225095653213362550837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118032816730435475575033891 177049225095653213362550837)
                  ·
                    refine ⟨16598364852717488752739141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177049225095653213362550837 16598364852717488752739141)
                    ·
                      refine ⟨3112193409884529141138589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16598364852717488752739141 3112193409884529141138589)
                      ·
                        rfl

theorem cell23_6060975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_6060975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060975 prefixEnd_6060975 := by exact prefixLift 6060975
  have htrace : WordTrace (prefixWord ++ tailWord_6060975) baseStart_6060975 baseEnd_6060975 := by
    simpa [prefixWord, tailWord_6060975, baseEnd_6060975] using wordTrace_append hprefix tailTrace_6060975
  have hstable : (prefixWord ++ tailWord_6060975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060975).length < 2 ^ (prefixWord ++ tailWord_6060975).sum := by decide
  have hdescent : baseEnd_6060975 < baseStart_6060975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6060995 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_6060995 : Nat := 118140960795 + 6060995 * 2 ^ 59
def prefixEnd_6060995 : Nat := 4983230072969 + 3 ^ 40 * 6060995 * 2
def baseEnd_6060995 : Nat := 3112203679497619062888497

theorem tailTrace_6060995 : CollatzResearch.WordTrace tailWord_6060995 prefixEnd_6060995 3112203679497619062888497 := by
  unfold tailWord_6060995
  simp only [CollatzResearch.WordTrace]
  refine ⟨221062648677057725379760439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147375099118038483586506959 221062648677057725379760439)
  ·
    refine ⟨331593973015586588069640659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221062648677057725379760439 331593973015586588069640659)
    ·
      refine ⟨497390959523379882104460989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331593973015586588069640659 497390959523379882104460989)
      ·
        refine ⟨186521609821267455789172871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497390959523379882104460989 186521609821267455789172871)
        ·
          refine ⟨279782414731901183683759307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186521609821267455789172871 279782414731901183683759307)
          ·
            refine ⟨419673622097851775525638961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279782414731901183683759307 419673622097851775525638961)
            ·
              refine ⟨314755216573388831644229221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419673622097851775525638961 314755216573388831644229221)
              ·
                refine ⟨59016603107510405933292979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314755216573388831644229221 59016603107510405933292979)
                ·
                  refine ⟨88524904661265608899939469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59016603107510405933292979 88524904661265608899939469)
                  ·
                    refine ⟨33196839247974603337477301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88524904661265608899939469 33196839247974603337477301)
                    ·
                      refine ⟨3112203679497619062888497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33196839247974603337477301 3112203679497619062888497)
                      ·
                        rfl

theorem cell23_6060995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_6060995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6060995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6060995 prefixEnd_6060995 := by exact prefixLift 6060995
  have htrace : WordTrace (prefixWord ++ tailWord_6060995) baseStart_6060995 baseEnd_6060995 := by
    simpa [prefixWord, tailWord_6060995, baseEnd_6060995] using wordTrace_append hprefix tailTrace_6060995
  have hstable : (prefixWord ++ tailWord_6060995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6060995).length < 2 ^ (prefixWord ++ tailWord_6060995).sum := by decide
  have hdescent : baseEnd_6060995 < baseStart_6060995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6060995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061013 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6061013 : Nat := 118140960795 + 6061013 * 2 ^ 59
def prefixEnd_6061013 : Nat := 4983230072969 + 3 ^ 40 * 6061013 * 2
def baseEnd_6061013 : Nat := 3112212922149399992463415

theorem tailTrace_6061013 : CollatzResearch.WordTrace tailWord_6061013 prefixEnd_6061013 3112212922149399992463415 := by
  unfold tailWord_6061013
  simp only [CollatzResearch.WordTrace]
  refine ⟨221063305190992514453915693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147375536793995009635943795 221063305190992514453915693)
  ·
    refine ⟨82898739446622192920218385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221063305190992514453915693 82898739446622192920218385)
    ·
      refine ⟨62174054584966644690163789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82898739446622192920218385 62174054584966644690163789)
      ·
        refine ⟨23315270469362491758811421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62174054584966644690163789 23315270469362491758811421)
        ·
          refine ⟨8743226426010934409554283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23315270469362491758811421 8743226426010934409554283)
          ·
            refine ⟨13114839639016401614331425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743226426010934409554283 13114839639016401614331425)
            ·
              refine ⟨9836129729262301210748569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13114839639016401614331425 9836129729262301210748569)
              ·
                refine ⟨7377097296946725908061427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9836129729262301210748569 7377097296946725908061427)
                ·
                  refine ⟨11065645945420088862092141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377097296946725908061427 11065645945420088862092141)
                  ·
                    refine ⟨4149617229532533323284553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11065645945420088862092141 4149617229532533323284553)
                    ·
                      refine ⟨3112212922149399992463415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149617229532533323284553 3112212922149399992463415)
                      ·
                        rfl

theorem cell23_6061013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6061013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061013 prefixEnd_6061013 := by exact prefixLift 6061013
  have htrace : WordTrace (prefixWord ++ tailWord_6061013) baseStart_6061013 baseEnd_6061013 := by
    simpa [prefixWord, tailWord_6061013, baseEnd_6061013] using wordTrace_append hprefix tailTrace_6061013
  have hstable : (prefixWord ++ tailWord_6061013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061013).length < 2 ^ (prefixWord ++ tailWord_6061013).sum := by decide
  have hdescent : baseEnd_6061013 < baseStart_6061013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061015 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 9]
def baseStart_6061015 : Nat := 118140960795 + 6061015 * 2 ^ 59
def prefixEnd_6061015 : Nat := 4983230072969 + 3 ^ 40 * 6061015 * 2
def baseEnd_6061015 : Nat := 345801549901189887182045

theorem tailTrace_6061015 : CollatzResearch.WordTrace tailWord_6061015 prefixEnd_6061015 345801549901189887182045 := by
  unfold tailWord_6061015
  simp only [CollatzResearch.WordTrace]
  refine ⟨221063378136985268795488499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147375585424656845863658999 221063378136985268795488499)
  ·
    refine ⟨331595067205477903193232749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221063378136985268795488499 331595067205477903193232749)
    ·
      refine ⟨124348150202054213697462281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331595067205477903193232749 124348150202054213697462281)
      ·
        refine ⟨93261112651540660273096711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124348150202054213697462281 93261112651540660273096711)
        ·
          refine ⟨139891668977310990409645067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93261112651540660273096711 139891668977310990409645067)
          ·
            refine ⟨209837503465966485614467601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139891668977310990409645067 209837503465966485614467601)
            ·
              refine ⟨157378127599474864210850701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209837503465966485614467601 157378127599474864210850701)
              ·
                refine ⟨59016797849803074079069013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157378127599474864210850701 59016797849803074079069013)
                ·
                  refine ⟨345801549901189887182045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59016797849803074079069013 345801549901189887182045)
                  ·
                    rfl

theorem cell23_6061015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 9].length) (baseStart_6061015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061015 prefixEnd_6061015 := by exact prefixLift 6061015
  have htrace : WordTrace (prefixWord ++ tailWord_6061015) baseStart_6061015 baseEnd_6061015 := by
    simpa [prefixWord, tailWord_6061015, baseEnd_6061015] using wordTrace_append hprefix tailTrace_6061015
  have hstable : (prefixWord ++ tailWord_6061015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061015).length < 2 ^ (prefixWord ++ tailWord_6061015).sum := by decide
  have hdescent : baseEnd_6061015 < baseStart_6061015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061035 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_6061035 : Nat := 118140960795 + 6061035 * 2 ^ 59
def prefixEnd_6061035 : Nat := 4983230072969 + 3 ^ 40 * 6061035 * 2
def baseEnd_6061035 : Nat := 3112224218723798906388313

theorem tailTrace_6061035 : CollatzResearch.WordTrace tailWord_6061035 prefixEnd_6061035 3112224218723798906388313 := by
  unfold tailWord_6061035
  simp only [CollatzResearch.WordTrace]
  refine ⟨221064107596912812211216559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147376071731275208140811039 221064107596912812211216559)
  ·
    refine ⟨331596161395369218316824839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221064107596912812211216559 331596161395369218316824839)
    ·
      refine ⟨497394242093053827475237259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331596161395369218316824839 497394242093053827475237259)
      ·
        refine ⟨746091363139580741212855889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497394242093053827475237259 746091363139580741212855889)
        ·
          refine ⟨559568522354685555909641917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746091363139580741212855889 559568522354685555909641917)
          ·
            refine ⟨209838195883007083466115719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559568522354685555909641917 209838195883007083466115719)
            ·
              refine ⟨314757293824510625199173579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209838195883007083466115719 314757293824510625199173579)
              ·
                refine ⟨472135940736765937798760369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314757293824510625199173579 472135940736765937798760369)
                ·
                  refine ⟨354101955552574453349070277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472135940736765937798760369 354101955552574453349070277)
                  ·
                    refine ⟨66394116666107710002950677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354101955552574453349070277 66394116666107710002950677)
                    ·
                      refine ⟨3112224218723798906388313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66394116666107710002950677 3112224218723798906388313)
                      ·
                        rfl

theorem cell23_6061035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_6061035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061035 prefixEnd_6061035 := by exact prefixLift 6061035
  have htrace : WordTrace (prefixWord ++ tailWord_6061035) baseStart_6061035 baseEnd_6061035 := by
    simpa [prefixWord, tailWord_6061035, baseEnd_6061035] using wordTrace_append hprefix tailTrace_6061035
  have hstable : (prefixWord ++ tailWord_6061035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061035).length < 2 ^ (prefixWord ++ tailWord_6061035).sum := by decide
  have hdescent : baseEnd_6061035 < baseStart_6061035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061079 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 2, 5]
def baseStart_6061079 : Nat := 118140960795 + 6061079 * 2 ^ 59
def prefixEnd_6061079 : Nat := 4983230072969 + 3 ^ 40 * 6061079 * 2
def baseEnd_6061079 : Nat := 1037415603957532244746037

theorem tailTrace_6061079 : CollatzResearch.WordTrace tailWord_6061079 prefixEnd_6061079 1037415603957532244746037 := by
  unfold tailWord_6061079
  simp only [CollatzResearch.WordTrace]
  refine ⟨221065712408753407725818291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147377141605835605150545527 221065712408753407725818291)
  ·
    refine ⟨331598568613130111588727437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221065712408753407725818291 331598568613130111588727437)
    ·
      refine ⟨124349463229923791845772789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331598568613130111588727437 124349463229923791845772789)
      ·
        refine ⟨11657762177805355485541199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124349463229923791845772789 11657762177805355485541199)
        ·
          refine ⟨17486643266708033228311799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11657762177805355485541199 17486643266708033228311799)
          ·
            refine ⟨26229964900062049842467699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17486643266708033228311799 26229964900062049842467699)
            ·
              refine ⟨39344947350093074763701549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26229964900062049842467699 39344947350093074763701549)
              ·
                refine ⟨14754355256284903036388081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39344947350093074763701549 14754355256284903036388081)
                ·
                  refine ⟨11065766442213677277291061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14754355256284903036388081 11065766442213677277291061)
                  ·
                    refine ⟨1037415603957532244746037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11065766442213677277291061 1037415603957532244746037)
                    ·
                      rfl

theorem cell23_6061079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_6061079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061079 prefixEnd_6061079 := by exact prefixLift 6061079
  have htrace : WordTrace (prefixWord ++ tailWord_6061079) baseStart_6061079 baseEnd_6061079 := by
    simpa [prefixWord, tailWord_6061079, baseEnd_6061079] using wordTrace_append hprefix tailTrace_6061079
  have hstable : (prefixWord ++ tailWord_6061079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061079).length < 2 ^ (prefixWord ++ tailWord_6061079).sum := by decide
  have hdescent : baseEnd_6061079 < baseStart_6061079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061099 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 4, 2]
def baseStart_6061099 : Nat := 118140960795 + 6061099 * 2 ^ 59
def prefixEnd_6061099 : Nat := 4983230072969 + 3 ^ 40 * 6061099 * 2
def baseEnd_6061099 : Nat := 3112257081485686655988019

theorem tailTrace_6061099 : CollatzResearch.WordTrace tailWord_6061099 prefixEnd_6061099 3112257081485686655988019 := by
  unfold tailWord_6061099
  simp only [CollatzResearch.WordTrace]
  refine ⟨221066441868680951141546351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147377627912453967427697567 221066441868680951141546351)
  ·
    refine ⟨331599662803021426712319527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221066441868680951141546351 331599662803021426712319527)
    ·
      refine ⟨497399494204532140068479291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331599662803021426712319527 497399494204532140068479291)
      ·
        refine ⟨746099241306798210102718937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497399494204532140068479291 746099241306798210102718937)
        ·
          refine ⟨559574430980098657577039203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746099241306798210102718937 559574430980098657577039203)
          ·
            refine ⟨839361646470147986365558805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559574430980098657577039203 839361646470147986365558805)
            ·
              refine ⟨39345077178288186860885569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 839361646470147986365558805 39345077178288186860885569)
              ·
                refine ⟨29508807883716140145664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39345077178288186860885569 29508807883716140145664177)
                ·
                  refine ⟨22131605912787105109248133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29508807883716140145664177 22131605912787105109248133)
                  ·
                    refine ⟨4149676108647582207984025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22131605912787105109248133 4149676108647582207984025)
                    ·
                      refine ⟨3112257081485686655988019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149676108647582207984025 3112257081485686655988019)
                      ·
                        rfl

theorem cell23_6061099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4, 2].length) (baseStart_6061099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061099 prefixEnd_6061099 := by exact prefixLift 6061099
  have htrace : WordTrace (prefixWord ++ tailWord_6061099) baseStart_6061099 baseEnd_6061099 := by
    simpa [prefixWord, tailWord_6061099, baseEnd_6061099] using wordTrace_append hprefix tailTrace_6061099
  have hstable : (prefixWord ++ tailWord_6061099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061099).length < 2 ^ (prefixWord ++ tailWord_6061099).sum := by decide
  have hdescent : baseEnd_6061099 < baseStart_6061099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061109 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_6061109 : Nat := 118140960795 + 6061109 * 2 ^ 59
def prefixEnd_6061109 : Nat := 4983230072969 + 3 ^ 40 * 6061109 * 2
def baseEnd_6061109 : Nat := 1037420738764077205620991

theorem tailTrace_6061109 : CollatzResearch.WordTrace tailWord_6061109 prefixEnd_6061109 1037420738764077205620991 := by
  unfold tailWord_6061109
  simp only [CollatzResearch.WordTrace]
  refine ⟨221066806598644722849410381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147377871065763148566273587 221066806598644722849410381)
  ·
    refine ⟨82900052474491771068528893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221066806598644722849410381 82900052474491771068528893)
    ·
      refine ⟨31087519677934414150698335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82900052474491771068528893 31087519677934414150698335)
      ·
        refine ⟨46631279516901621226047503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31087519677934414150698335 46631279516901621226047503)
        ·
          refine ⟨69946919275352431839071255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46631279516901621226047503 69946919275352431839071255)
          ·
            refine ⟨104920378913028647758606883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69946919275352431839071255 104920378913028647758606883)
            ·
              refine ⟨157380568369542971637910325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104920378913028647758606883 157380568369542971637910325)
              ·
                refine ⟨14754428284644653591054093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157380568369542971637910325 14754428284644653591054093)
                ·
                  refine ⟨5532910606741745096645285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14754428284644653591054093 5532910606741745096645285)
                  ·
                    refine ⟨1037420738764077205620991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5532910606741745096645285 1037420738764077205620991)
                    ·
                      rfl

theorem cell23_6061109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_6061109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061109 prefixEnd_6061109 := by exact prefixLift 6061109
  have htrace : WordTrace (prefixWord ++ tailWord_6061109) baseStart_6061109 baseEnd_6061109 := by
    simpa [prefixWord, tailWord_6061109, baseEnd_6061109] using wordTrace_append hprefix tailTrace_6061109
  have hstable : (prefixWord ++ tailWord_6061109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061109).length < 2 ^ (prefixWord ++ tailWord_6061109).sum := by decide
  have hdescent : baseEnd_6061109 < baseStart_6061109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061116 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_6061116 : Nat := 118140960795 + 6061116 * 2 ^ 59
def prefixEnd_6061116 : Nat := 4983230072969 + 3 ^ 40 * 6061116 * 2
def baseEnd_6061116 : Nat := 3112265810656813089475441

theorem tailTrace_6061116 : CollatzResearch.WordTrace tailWord_6061116 prefixEnd_6061116 3112265810656813089475441 := by
  unfold tailWord_6061116
  simp only [CollatzResearch.WordTrace]
  refine ⟨110533530954809681522457601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147378041273079575363276801 110533530954809681522457601)
  ·
    refine ⟨82900148216107261141843201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110533530954809681522457601 82900148216107261141843201)
    ·
      refine ⟨62175111162080445856382401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82900148216107261141843201 62175111162080445856382401)
      ·
        refine ⟨46631333371560334392286801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62175111162080445856382401 46631333371560334392286801)
        ·
          refine ⟨34973500028670250794215101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46631333371560334392286801 34973500028670250794215101)
          ·
            refine ⟨13115062510751344047830663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34973500028670250794215101 13115062510751344047830663)
            ·
              refine ⟨19672593766127016071745995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115062510751344047830663 19672593766127016071745995)
              ·
                refine ⟨29508890649190524107618993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19672593766127016071745995 29508890649190524107618993)
                ·
                  refine ⟨22131667986892893080714245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29508890649190524107618993 22131667986892893080714245)
                  ·
                    refine ⟨4149687747542417452633921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22131667986892893080714245 4149687747542417452633921)
                    ·
                      refine ⟨3112265810656813089475441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149687747542417452633921 3112265810656813089475441)
                      ·
                        rfl

theorem cell23_6061116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_6061116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061116 prefixEnd_6061116 := by exact prefixLift 6061116
  have htrace : WordTrace (prefixWord ++ tailWord_6061116) baseStart_6061116 baseEnd_6061116 := by
    simpa [prefixWord, tailWord_6061116, baseEnd_6061116] using wordTrace_append hprefix tailTrace_6061116
  have hstable : (prefixWord ++ tailWord_6061116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061116).length < 2 ^ (prefixWord ++ tailWord_6061116).sum := by decide
  have hdescent : baseEnd_6061116 < baseStart_6061116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061133 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6061133 : Nat := 118140960795 + 6061133 * 2 ^ 59
def prefixEnd_6061133 : Nat := 4983230072969 + 3 ^ 40 * 6061133 * 2
def baseEnd_6061133 : Nat := 3112274539827939522962863

theorem tailTrace_6061133 : CollatzResearch.WordTrace tailWord_6061133 prefixEnd_6061133 3112274539827939522962863 := by
  unfold tailWord_6061133
  simp only [CollatzResearch.WordTrace]
  refine ⟨221067681950557774948284053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147378454633705183298856035 221067681950557774948284053)
  ·
    refine ⟨10362547591432395700700815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221067681950557774948284053 10362547591432395700700815)
    ·
      refine ⟨15543821387148593551051223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362547591432395700700815 15543821387148593551051223)
      ·
        refine ⟨23315732080722890326576835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15543821387148593551051223 23315732080722890326576835)
        ·
          refine ⟨34973598121084335489865253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23315732080722890326576835 34973598121084335489865253)
          ·
            refine ⟨6557549647703312904349735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34973598121084335489865253 6557549647703312904349735)
            ·
              refine ⟨9836324471554969356524603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6557549647703312904349735 9836324471554969356524603)
              ·
                refine ⟨14754486707332454034786905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836324471554969356524603 14754486707332454034786905)
                ·
                  refine ⟨11065865030499340526090179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14754486707332454034786905 11065865030499340526090179)
                  ·
                    refine ⟨16598797545749010789135269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11065865030499340526090179 16598797545749010789135269)
                    ·
                      refine ⟨3112274539827939522962863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16598797545749010789135269 3112274539827939522962863)
                      ·
                        rfl

theorem cell23_6061133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6061133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061133 prefixEnd_6061133 := by exact prefixLift 6061133
  have htrace : WordTrace (prefixWord ++ tailWord_6061133) baseStart_6061133 baseEnd_6061133 := by
    simpa [prefixWord, tailWord_6061133, baseEnd_6061133] using wordTrace_append hprefix tailTrace_6061133
  have hstable : (prefixWord ++ tailWord_6061133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061133).length < 2 ^ (prefixWord ++ tailWord_6061133).sum := by decide
  have hdescent : baseEnd_6061133 < baseStart_6061133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061150 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6061150 : Nat := 118140960795 + 6061150 * 2 ^ 59
def prefixEnd_6061150 : Nat := 4983230072969 + 3 ^ 40 * 6061150 * 2
def baseEnd_6061150 : Nat := 3112283268999065956450285

theorem tailTrace_6061150 : CollatzResearch.WordTrace tailWord_6061150 prefixEnd_6061150 3112283268999065956450285 := by
  unfold tailWord_6061150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27633537748937023356456613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147378867994330791234435269 27633537748937023356456613)
  ·
    refine ⟨5181288327925691879335615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27633537748937023356456613 5181288327925691879335615)
    ·
      refine ⟨7771932491888537819003423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181288327925691879335615 7771932491888537819003423)
      ·
        refine ⟨11657898737832806728505135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7771932491888537819003423 11657898737832806728505135)
        ·
          refine ⟨17486848106749210092757703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11657898737832806728505135 17486848106749210092757703)
          ·
            refine ⟨26230272160123815139136555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17486848106749210092757703 26230272160123815139136555)
            ·
              refine ⟨39345408240185722708704833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26230272160123815139136555 39345408240185722708704833)
              ·
                refine ⟨29509056180139292031528625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39345408240185722708704833 29509056180139292031528625)
                ·
                  refine ⟨22131792135104469023646469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29509056180139292031528625 22131792135104469023646469)
                  ·
                    refine ⟨4149711025332087941933713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22131792135104469023646469 4149711025332087941933713)
                    ·
                      refine ⟨3112283268999065956450285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149711025332087941933713 3112283268999065956450285)
                      ·
                        rfl

theorem cell23_6061150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6061150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061150 prefixEnd_6061150 := by exact prefixLift 6061150
  have htrace : WordTrace (prefixWord ++ tailWord_6061150) baseStart_6061150 baseEnd_6061150 := by
    simpa [prefixWord, tailWord_6061150, baseEnd_6061150] using wordTrace_append hprefix tailTrace_6061150
  have hstable : (prefixWord ++ tailWord_6061150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061150).length < 2 ^ (prefixWord ++ tailWord_6061150).sum := by decide
  have hdescent : baseEnd_6061150 < baseStart_6061150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061209 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_6061209 : Nat := 118140960795 + 6061209 * 2 ^ 59
def prefixEnd_6061209 : Nat := 4983230072969 + 3 ^ 40 * 6061209 * 2
def baseEnd_6061209 : Nat := 3112313564357681225612513

theorem tailTrace_6061209 : CollatzResearch.WordTrace tailWord_6061209 prefixEnd_6061209 3112313564357681225612513 := by
  unfold tailWord_6061209
  simp only [CollatzResearch.WordTrace]
  refine ⟨221070453898282439928050681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147380302598854959952033787 221070453898282439928050681)
  ·
    refine ⟨165802840423711829946038011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221070453898282439928050681 165802840423711829946038011)
    ·
      refine ⟨248704260635567744919057017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165802840423711829946038011 248704260635567744919057017)
      ·
        refine ⟨186528195476675808689292763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248704260635567744919057017 186528195476675808689292763)
        ·
          refine ⟨279792293215013713033939145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186528195476675808689292763 279792293215013713033939145)
          ·
            refine ⟨209844219911260284775454359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279792293215013713033939145 209844219911260284775454359)
            ·
              refine ⟨314766329866890427163181539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209844219911260284775454359 314766329866890427163181539)
              ·
                refine ⟨472149494800335640744772309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314766329866890427163181539 472149494800335640744772309)
                ·
                  refine ⟨11066003784382866579955601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 472149494800335640744772309 11066003784382866579955601)
                  ·
                    refine ⟨8299502838287149934966701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11066003784382866579955601 8299502838287149934966701)
                    ·
                      refine ⟨3112313564357681225612513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299502838287149934966701 3112313564357681225612513)
                      ·
                        rfl

theorem cell23_6061209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_6061209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061209 prefixEnd_6061209 := by exact prefixLift 6061209
  have htrace : WordTrace (prefixWord ++ tailWord_6061209) baseStart_6061209 baseEnd_6061209 := by
    simpa [prefixWord, tailWord_6061209, baseEnd_6061209] using wordTrace_append hprefix tailTrace_6061209
  have hstable : (prefixWord ++ tailWord_6061209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061209).length < 2 ^ (prefixWord ++ tailWord_6061209).sum := by decide
  have hdescent : baseEnd_6061209 < baseStart_6061209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061216 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_6061216 : Nat := 118140960795 + 6061216 * 2 ^ 59
def prefixEnd_6061216 : Nat := 4983230072969 + 3 ^ 40 * 6061216 * 2
def baseEnd_6061216 : Nat := 1037439052907420899408327

theorem tailTrace_6061216 : CollatzResearch.WordTrace tailWord_6061216 prefixEnd_6061216 1037439052907420899408327 := by
  unfold tailWord_6061216
  simp only [CollatzResearch.WordTrace]
  refine ⟨110535354604628540061777751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147380472806171386749037001 110535354604628540061777751)
  ·
    refine ⟨165803031906942810092666627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110535354604628540061777751 165803031906942810092666627)
    ·
      refine ⟨248704547860414215138999941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165803031906942810092666627 248704547860414215138999941)
      ·
        refine ⟨46632102723827665338562489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248704547860414215138999941 46632102723827665338562489)
        ·
          refine ⟨34974077042870749003921867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46632102723827665338562489 34974077042870749003921867)
          ·
            refine ⟨52461115564306123505882801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34974077042870749003921867 52461115564306123505882801)
            ·
              refine ⟨39345836673229592629412101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52461115564306123505882801 39345836673229592629412101)
              ·
                refine ⟨7377344376230548618014769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39345836673229592629412101 7377344376230548618014769)
                ·
                  refine ⟨5533008282172911463511077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377344376230548618014769 5533008282172911463511077)
                  ·
                    refine ⟨1037439052907420899408327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533008282172911463511077 1037439052907420899408327)
                    ·
                      rfl

theorem cell23_6061216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_6061216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061216 prefixEnd_6061216 := by exact prefixLift 6061216
  have htrace : WordTrace (prefixWord ++ tailWord_6061216) baseStart_6061216 baseEnd_6061216 := by
    simpa [prefixWord, tailWord_6061216, baseEnd_6061216] using wordTrace_append hprefix tailTrace_6061216
  have hstable : (prefixWord ++ tailWord_6061216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061216).length < 2 ^ (prefixWord ++ tailWord_6061216).sum := by decide
  have hdescent : baseEnd_6061216 < baseStart_6061216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061233 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_6061233 : Nat := 118140960795 + 6061233 * 2 ^ 59
def prefixEnd_6061233 : Nat := 4983230072969 + 3 ^ 40 * 6061233 * 2
def baseEnd_6061233 : Nat := 1037441962631129710570801

theorem tailTrace_6061233 : CollatzResearch.WordTrace tailWord_6061233 prefixEnd_6061233 1037441962631129710570801 := by
  unfold tailWord_6061233
  simp only [CollatzResearch.WordTrace]
  refine ⟨221071329250195492026924353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147380886166796994684616235 221071329250195492026924353)
  ·
    refine ⟨165803496937646619020193265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221071329250195492026924353 165803496937646619020193265)
    ·
      refine ⟨124352622703234964265144949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165803496937646619020193265 124352622703234964265144949)
      ·
        refine ⟨11658058378428277899857339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124352622703234964265144949 11658058378428277899857339)
        ·
          refine ⟨17487087567642416849786009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11658058378428277899857339 17487087567642416849786009)
          ·
            refine ⟨13115315675731812637339507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17487087567642416849786009 13115315675731812637339507)
            ·
              refine ⟨19672973513597718956009261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115315675731812637339507 19672973513597718956009261)
              ·
                refine ⟨7377365067599144608503473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19672973513597718956009261 7377365067599144608503473)
                ·
                  refine ⟨5533023800699358456377605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377365067599144608503473 5533023800699358456377605)
                  ·
                    refine ⟨1037441962631129710570801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533023800699358456377605 1037441962631129710570801)
                    ·
                      rfl

theorem cell23_6061233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_6061233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061233 prefixEnd_6061233 := by exact prefixLift 6061233
  have htrace : WordTrace (prefixWord ++ tailWord_6061233) baseStart_6061233 baseEnd_6061233 := by
    simpa [prefixWord, tailWord_6061233, baseEnd_6061233] using wordTrace_append hprefix tailTrace_6061233
  have hstable : (prefixWord ++ tailWord_6061233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061233).length < 2 ^ (prefixWord ++ tailWord_6061233).sum := by decide
  have hdescent : baseEnd_6061233 < baseStart_6061233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061250 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6061250 : Nat := 118140960795 + 6061250 * 2 ^ 59
def prefixEnd_6061250 : Nat := 4983230072969 + 3 ^ 40 * 6061250 * 2
def baseEnd_6061250 : Nat := 1037444872354838521733275

theorem tailTrace_6061250 : CollatzResearch.WordTrace tailWord_6061250 prefixEnd_6061250 1037444872354838521733275 := by
  unfold tailWord_6061250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55267987322783475982573301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147381299527422602620195469 55267987322783475982573301)
  ·
    refine ⟨5181373811510950873366247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55267987322783475982573301 5181373811510950873366247)
    ·
      refine ⟨7772060717266426310049371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181373811510950873366247 7772060717266426310049371)
      ·
        refine ⟨11658091075899639465074057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7772060717266426310049371 11658091075899639465074057)
        ·
          refine ⟨8743568306924729598805543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11658091075899639465074057 8743568306924729598805543)
          ·
            refine ⟨13115352460387094398208315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743568306924729598805543 13115352460387094398208315)
            ·
              refine ⟨19673028690580641597312473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115352460387094398208315 19673028690580641597312473)
              ·
                refine ⟨14754771517935481197984355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19673028690580641597312473 14754771517935481197984355)
                ·
                  refine ⟨22132157276903221796976533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14754771517935481197984355 22132157276903221796976533)
                  ·
                    refine ⟨1037444872354838521733275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22132157276903221796976533 1037444872354838521733275)
                    ·
                      rfl

theorem cell23_6061250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6061250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061250 prefixEnd_6061250 := by exact prefixLift 6061250
  have htrace : WordTrace (prefixWord ++ tailWord_6061250) baseStart_6061250 baseEnd_6061250 := by
    simpa [prefixWord, tailWord_6061250, baseEnd_6061250] using wordTrace_append hprefix tailTrace_6061250
  have hstable : (prefixWord ++ tailWord_6061250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061250).length < 2 ^ (prefixWord ++ tailWord_6061250).sum := by decide
  have hdescent : baseEnd_6061250 < baseStart_6061250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061254 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6061254 : Nat := 118140960795 + 6061254 * 2 ^ 59
def prefixEnd_6061254 : Nat := 4983230072969 + 3 ^ 40 * 6061254 * 2
def baseEnd_6061254 : Nat := 1037445556995711183183269

theorem tailTrace_6061254 : CollatzResearch.WordTrace tailWord_6061254 prefixEnd_6061254 1037445556995711183183269 := by
  unfold tailWord_6061254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908502974472481644169963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147381396788746275075625877 6908502974472481644169963)
  ·
    refine ⟨10362754461708722466254945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908502974472481644169963 10362754461708722466254945)
    ·
      refine ⟨7772065846281541849691209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10362754461708722466254945 7772065846281541849691209)
      ·
        refine ⟨5829049384711156387268407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772065846281541849691209 5829049384711156387268407)
        ·
          refine ⟨8743574077066734580902611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5829049384711156387268407 8743574077066734580902611)
          ·
            refine ⟨13115361115600101871353917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743574077066734580902611 13115361115600101871353917)
            ·
              refine ⟨4918260418350038201757719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13115361115600101871353917 4918260418350038201757719)
              ·
                refine ⟨7377390627525057302636579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918260418350038201757719 7377390627525057302636579)
                ·
                  refine ⟨11066085941287585953954869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377390627525057302636579 11066085941287585953954869)
                  ·
                    refine ⟨1037445556995711183183269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11066085941287585953954869 1037445556995711183183269)
                    ·
                      rfl

theorem cell23_6061254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6061254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061254 prefixEnd_6061254 := by exact prefixLift 6061254
  have htrace : WordTrace (prefixWord ++ tailWord_6061254) baseStart_6061254 baseEnd_6061254 := by
    simpa [prefixWord, tailWord_6061254, baseEnd_6061254] using wordTrace_append hprefix tailTrace_6061254
  have hstable : (prefixWord ++ tailWord_6061254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061254).length < 2 ^ (prefixWord ++ tailWord_6061254).sum := by decide
  have hdescent : baseEnd_6061254 < baseStart_6061254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061256 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_6061256 : Nat := 118140960795 + 6061256 * 2 ^ 59
def prefixEnd_6061256 : Nat := 4983230072969 + 3 ^ 40 * 6061256 * 2
def baseEnd_6061256 : Nat := 3112337697948442541724797

theorem tailTrace_6061256 : CollatzResearch.WordTrace tailWord_6061256 prefixEnd_6061256 3112337697948442541724797 := by
  unfold tailWord_6061256
  simp only [CollatzResearch.WordTrace]
  refine ⟨110536084064556083477505811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147381445419408111303341081 110536084064556083477505811)
  ·
    refine ⟨165804126096834125216258717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110536084064556083477505811 165804126096834125216258717)
    ·
      refine ⟨62176547286312796956097019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165804126096834125216258717 62176547286312796956097019)
      ·
        refine ⟨93264820929469195434145529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62176547286312796956097019 93264820929469195434145529)
        ·
          refine ⟨69948615697101896575609147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93264820929469195434145529 69948615697101896575609147)
          ·
            refine ⟨104922923545652844863413721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69948615697101896575609147 104922923545652844863413721)
            ·
              refine ⟨78692192659239633647560291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104922923545652844863413721 78692192659239633647560291)
              ·
                refine ⟨118038288988859450471340437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78692192659239633647560291 118038288988859450471340437)
                ·
                  refine ⟨5533044796352786740844083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118038288988859450471340437 5533044796352786740844083)
                  ·
                    refine ⟨8299567194529180111266125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5533044796352786740844083 8299567194529180111266125)
                    ·
                      refine ⟨3112337697948442541724797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299567194529180111266125 3112337697948442541724797)
                      ·
                        rfl

theorem cell23_6061256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_6061256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061256 prefixEnd_6061256 := by exact prefixLift 6061256
  have htrace : WordTrace (prefixWord ++ tailWord_6061256) baseStart_6061256 baseEnd_6061256 := by
    simpa [prefixWord, tailWord_6061256, baseEnd_6061256] using wordTrace_append hprefix tailTrace_6061256
  have hstable : (prefixWord ++ tailWord_6061256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061256).length < 2 ^ (prefixWord ++ tailWord_6061256).sum := by decide
  have hdescent : baseEnd_6061256 < baseStart_6061256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061279 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_6061279 : Nat := 118140960795 + 6061279 * 2 ^ 59
def prefixEnd_6061279 : Nat := 4983230072969 + 3 ^ 40 * 6061279 * 2
def baseEnd_6061279 : Nat := 3112349508003495951737191

theorem tailTrace_6061279 : CollatzResearch.WordTrace tailWord_6061279 prefixEnd_6061279 3112349508003495951737191 := by
  unfold tailWord_6061279
  simp only [CollatzResearch.WordTrace]
  refine ⟨221073007008028841883098891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147382004672019227922065927 221073007008028841883098891)
  ·
    refine ⟨331609510512043262824648337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221073007008028841883098891 331609510512043262824648337)
    ·
      refine ⟨248707132884032447118486253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331609510512043262824648337 248707132884032447118486253)
      ·
        refine ⟨93265174831512167669432345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248707132884032447118486253 93265174831512167669432345)
        ·
          refine ⟨69948881123634125752074259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93265174831512167669432345 69948881123634125752074259)
          ·
            refine ⟨104923321685451188628111389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69948881123634125752074259 104923321685451188628111389)
            ·
              refine ⟨39346245632044195735541771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104923321685451188628111389 39346245632044195735541771)
              ·
                refine ⟨59019368448066293603312657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39346245632044195735541771 59019368448066293603312657)
                ·
                  refine ⟨44264526336049720202484493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59019368448066293603312657 44264526336049720202484493)
                  ·
                    refine ⟨16599197376018645075931685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44264526336049720202484493 16599197376018645075931685)
                    ·
                      refine ⟨3112349508003495951737191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16599197376018645075931685 3112349508003495951737191)
                      ·
                        rfl

theorem cell23_6061279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_6061279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061279 prefixEnd_6061279 := by exact prefixLift 6061279
  have htrace : WordTrace (prefixWord ++ tailWord_6061279) baseStart_6061279 baseEnd_6061279 := by
    simpa [prefixWord, tailWord_6061279, baseEnd_6061279] using wordTrace_append hprefix tailTrace_6061279
  have hstable : (prefixWord ++ tailWord_6061279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061279).length < 2 ^ (prefixWord ++ tailWord_6061279).sum := by decide
  have hdescent : baseEnd_6061279 < baseStart_6061279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061313 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_6061313 : Nat := 118140960795 + 6061313 * 2 ^ 59
def prefixEnd_6061313 : Nat := 4983230072969 + 3 ^ 40 * 6061313 * 2
def baseEnd_6061313 : Nat := 3112366966345748818712035

theorem tailTrace_6061313 : CollatzResearch.WordTrace tailWord_6061313 prefixEnd_6061313 3112366966345748818712035 := by
  unfold tailWord_6061313
  simp only [CollatzResearch.WordTrace]
  refine ⟨221074247089905665689836593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147382831393270443793224395 221074247089905665689836593)
  ·
    refine ⟨165805685317429249267377445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221074247089905665689836593 165805685317429249267377445)
    ·
      refine ⟨31088565997017984237633271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165805685317429249267377445 31088565997017984237633271)
      ·
        refine ⟨46632848995526976356449907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31088565997017984237633271 46632848995526976356449907)
        ·
          refine ⟨69949273493290464534674861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46632848995526976356449907 69949273493290464534674861)
          ·
            refine ⟨26230977559983924200503073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69949273493290464534674861 26230977559983924200503073)
            ·
              refine ⟨19673233169987943150377305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26230977559983924200503073 19673233169987943150377305)
              ·
                refine ⟨14754924877490957362782979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19673233169987943150377305 14754924877490957362782979)
                ·
                  refine ⟨22132387316236436044174469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14754924877490957362782979 22132387316236436044174469)
                  ·
                    refine ⟨4149822621794331758282713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22132387316236436044174469 4149822621794331758282713)
                    ·
                      refine ⟨3112366966345748818712035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149822621794331758282713 3112366966345748818712035)
                      ·
                        rfl

theorem cell23_6061313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_6061313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061313 prefixEnd_6061313 := by exact prefixLift 6061313
  have htrace : WordTrace (prefixWord ++ tailWord_6061313) baseStart_6061313 baseEnd_6061313 := by
    simpa [prefixWord, tailWord_6061313, baseEnd_6061313] using wordTrace_append hprefix tailTrace_6061313
  have hstable : (prefixWord ++ tailWord_6061313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061313).length < 2 ^ (prefixWord ++ tailWord_6061313).sum := by decide
  have hdescent : baseEnd_6061313 < baseStart_6061313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061326 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6061326 : Nat := 118140960795 + 6061326 * 2 ^ 59
def prefixEnd_6061326 : Nat := 4983230072969 + 3 ^ 40 * 6061326 * 2
def baseEnd_6061326 : Nat := 3112373641594257267849475

theorem tailTrace_6061326 : CollatzResearch.WordTrace tailWord_6061326 prefixEnd_6061326 3112373641594257267849475 := by
  unfold tailWord_6061326
  simp only [CollatzResearch.WordTrace]
  refine ⟨27634340154857321113757479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147383147492572379273373221 27634340154857321113757479)
  ·
    refine ⟨41451510232285981670636219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27634340154857321113757479 41451510232285981670636219)
    ·
      refine ⟨62177265348428972505954329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41451510232285981670636219 62177265348428972505954329)
      ·
        refine ⟨46632949011321729379465747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62177265348428972505954329 46632949011321729379465747)
        ·
          refine ⟨69949423516982594069198621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46632949011321729379465747 69949423516982594069198621)
          ·
            refine ⟨26231033818868472775949483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69949423516982594069198621 26231033818868472775949483)
            ·
              refine ⟨39346550728302709163924225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26231033818868472775949483 39346550728302709163924225)
              ·
                refine ⟨29509913046227031872943169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39346550728302709163924225 29509913046227031872943169)
                ·
                  refine ⟨22132434784670273904707377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29509913046227031872943169 22132434784670273904707377)
                  ·
                    refine ⟨16599326088502705428530533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22132434784670273904707377 16599326088502705428530533)
                    ·
                      refine ⟨3112373641594257267849475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16599326088502705428530533 3112373641594257267849475)
                      ·
                        rfl

theorem cell23_6061326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6061326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061326 prefixEnd_6061326 := by exact prefixLift 6061326
  have htrace : WordTrace (prefixWord ++ tailWord_6061326) baseStart_6061326 baseEnd_6061326 := by
    simpa [prefixWord, tailWord_6061326, baseEnd_6061326] using wordTrace_append hprefix tailTrace_6061326
  have hstable : (prefixWord ++ tailWord_6061326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061326).length < 2 ^ (prefixWord ++ tailWord_6061326).sum := by decide
  have hdescent : baseEnd_6061326 < baseStart_6061326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061336 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 7]
def baseStart_6061336 : Nat := 118140960795 + 6061336 * 2 ^ 59
def prefixEnd_6061336 : Nat := 4983230072969 + 3 ^ 40 * 6061336 * 2
def baseEnd_6061336 : Nat := 345819864044533580969381

theorem tailTrace_6061336 : CollatzResearch.WordTrace tailWord_6061336 prefixEnd_6061336 345819864044533580969381 := by
  unfold tailWord_6061336
  simp only [CollatzResearch.WordTrace]
  refine ⟨110537542984411170308961931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147383390645881560411949241 110537542984411170308961931)
  ·
    refine ⟨165806314476616755463442897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110537542984411170308961931 165806314476616755463442897)
    ·
      refine ⟨124354735857462566597582173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165806314476616755463442897 124354735857462566597582173)
      ·
        refine ⟨46633025946548462474093315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124354735857462566597582173 46633025946548462474093315)
        ·
          refine ⟨69949538919822693711139973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46633025946548462474093315 69949538919822693711139973)
          ·
            refine ⟨13115538547466755070838745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69949538919822693711139973 13115538547466755070838745)
            ·
              refine ⟨9836653910600066303129059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13115538547466755070838745 9836653910600066303129059)
              ·
                refine ⟨14754980865900099454693589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836653910600066303129059 14754980865900099454693589)
                ·
                  refine ⟨345819864044533580969381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14754980865900099454693589 345819864044533580969381)
                  ·
                    rfl

theorem cell23_6061336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_6061336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061336 prefixEnd_6061336 := by exact prefixLift 6061336
  have htrace : WordTrace (prefixWord ++ tailWord_6061336) baseStart_6061336 baseEnd_6061336 := by
    simpa [prefixWord, tailWord_6061336, baseEnd_6061336] using wordTrace_append hprefix tailTrace_6061336
  have hstable : (prefixWord ++ tailWord_6061336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061336).length < 2 ^ (prefixWord ++ tailWord_6061336).sum := by decide
  have hdescent : baseEnd_6061336 < baseStart_6061336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061347 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 2, 2, 2]
def baseStart_6061347 : Nat := 118140960795 + 6061347 * 2 ^ 59
def prefixEnd_6061347 : Nat := 4983230072969 + 3 ^ 40 * 6061347 * 2
def baseEnd_6061347 : Nat := 3112384424688001685686879

theorem tailTrace_6061347 : CollatzResearch.WordTrace tailWord_6061347 prefixEnd_6061347 3112384424688001685686879 := by
  unfold tailWord_6061347
  simp only [CollatzResearch.WordTrace]
  refine ⟨221075487171782489496574295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147383658114521659664382863 221075487171782489496574295)
  ·
    refine ⟨331613230757673734244861443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221075487171782489496574295 331613230757673734244861443)
    ·
      refine ⟨497419846136510601367292165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331613230757673734244861443 497419846136510601367292165)
      ·
        refine ⟨93266221150595737756367281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 497419846136510601367292165 93266221150595737756367281)
        ·
          refine ⟨69949665862946803317275461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93266221150595737756367281 69949665862946803317275461)
          ·
            refine ⟨13115562349302525621989149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69949665862946803317275461 13115562349302525621989149)
            ·
              refine ⟨4918335880988447108245931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13115562349302525621989149 4918335880988447108245931)
              ·
                refine ⟨7377503821482670662368897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918335880988447108245931 7377503821482670662368897)
                ·
                  refine ⟨5533127866112002996776673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377503821482670662368897 5533127866112002996776673)
                  ·
                    refine ⟨4149845899584002247582505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533127866112002996776673 4149845899584002247582505)
                    ·
                      refine ⟨3112384424688001685686879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149845899584002247582505 3112384424688001685686879)
                      ·
                        rfl

theorem cell23_6061347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_6061347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061347 prefixEnd_6061347 := by exact prefixLift 6061347
  have htrace : WordTrace (prefixWord ++ tailWord_6061347) baseStart_6061347 baseEnd_6061347 := by
    simpa [prefixWord, tailWord_6061347, baseEnd_6061347] using wordTrace_append hprefix tailTrace_6061347
  have hstable : (prefixWord ++ tailWord_6061347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061347).length < 2 ^ (prefixWord ++ tailWord_6061347).sum := by decide
  have hdescent : baseEnd_6061347 < baseStart_6061347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061359 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_6061359 : Nat := 118140960795 + 6061359 * 2 ^ 59
def prefixEnd_6061359 : Nat := 4983230072969 + 3 ^ 40 * 6061359 * 2
def baseEnd_6061359 : Nat := 3112390586455855638736823

theorem tailTrace_6061359 : CollatzResearch.WordTrace tailWord_6061359 prefixEnd_6061359 3112390586455855638736823 := by
  unfold tailWord_6061359
  simp only [CollatzResearch.WordTrace]
  refine ⟨221075924847739015546011131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147383949898492677030674087 221075924847739015546011131)
  ·
    refine ⟨331613887271608523319016697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221075924847739015546011131 331613887271608523319016697)
    ·
      refine ⟨248710415453706392489262523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331613887271608523319016697 248710415453706392489262523)
      ·
        refine ⟨373065623180559588733893785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248710415453706392489262523 373065623180559588733893785)
        ·
          refine ⟨279799217385419691550420339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373065623180559588733893785 279799217385419691550420339)
          ·
            refine ⟨419698826078129537325630509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279799217385419691550420339 419698826078129537325630509)
            ·
              refine ⟨157387059779298576497111441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419698826078129537325630509 157387059779298576497111441)
              ·
                refine ⟨118040294834473932372833581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157387059779298576497111441 118040294834473932372833581)
                ·
                  refine ⟨44265110562927724639812593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118040294834473932372833581 44265110562927724639812593)
                  ·
                    refine ⟨33198832922195793479859445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44265110562927724639812593 33198832922195793479859445)
                    ·
                      refine ⟨3112390586455855638736823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33198832922195793479859445 3112390586455855638736823)
                      ·
                        rfl

theorem cell23_6061359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_6061359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061359 prefixEnd_6061359 := by exact prefixLift 6061359
  have htrace : WordTrace (prefixWord ++ tailWord_6061359) baseStart_6061359 baseEnd_6061359 := by
    simpa [prefixWord, tailWord_6061359, baseEnd_6061359] using wordTrace_append hprefix tailTrace_6061359
  have hstable : (prefixWord ++ tailWord_6061359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061359).length < 2 ^ (prefixWord ++ tailWord_6061359).sum := by decide
  have hdescent : baseEnd_6061359 < baseStart_6061359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061398 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6061398 : Nat := 118140960795 + 6061398 * 2 ^ 59
def prefixEnd_6061398 : Nat := 4983230072969 + 3 ^ 40 * 6061398 * 2
def baseEnd_6061398 : Nat := 3112410612201380986149145

theorem tailTrace_6061398 : CollatzResearch.WordTrace tailWord_6061398 prefixEnd_6061398 3112410612201380986149145 := by
  unfold tailWord_6061398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817334205912357825417553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147384898196398483471120565 13817334205912357825417553)
  ·
    refine ⟨10363000654434268369063165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13817334205912357825417553 10363000654434268369063165)
    ·
      refine ⟨3886125245412850638398687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10363000654434268369063165 3886125245412850638398687)
      ·
        refine ⟨5829187868119275957598031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886125245412850638398687 5829187868119275957598031)
        ·
          refine ⟨8743781802178913936397047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5829187868119275957598031 8743781802178913936397047)
          ·
            refine ⟨13115672703268370904595571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8743781802178913936397047 13115672703268370904595571)
            ·
              refine ⟨19673509054902556356893357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115672703268370904595571 19673509054902556356893357)
              ·
                refine ⟨7377565895588458633835009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19673509054902556356893357 7377565895588458633835009)
                ·
                  refine ⟨5533174421691343975376257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7377565895588458633835009 5533174421691343975376257)
                  ·
                    refine ⟨4149880816268507981532193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533174421691343975376257 4149880816268507981532193)
                    ·
                      refine ⟨3112410612201380986149145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149880816268507981532193 3112410612201380986149145)
                      ·
                        rfl

theorem cell23_6061398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6061398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061398 prefixEnd_6061398 := by exact prefixLift 6061398
  have htrace : WordTrace (prefixWord ++ tailWord_6061398) baseStart_6061398 baseEnd_6061398 := by
    simpa [prefixWord, tailWord_6061398, baseEnd_6061398] using wordTrace_append hprefix tailTrace_6061398
  have hstable : (prefixWord ++ tailWord_6061398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061398).length < 2 ^ (prefixWord ++ tailWord_6061398).sum := by decide
  have hdescent : baseEnd_6061398 < baseStart_6061398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061419 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_6061419 : Nat := 118140960795 + 6061419 * 2 ^ 59
def prefixEnd_6061419 : Nat := 4983230072969 + 3 ^ 40 * 6061419 * 2
def baseEnd_6061419 : Nat := 3112421395295125403986547

theorem tailTrace_6061419 : CollatzResearch.WordTrace tailWord_6061419 prefixEnd_6061419 3112421395295125403986547 := by
  unfold tailWord_6061419
  simp only [CollatzResearch.WordTrace]
  refine ⟨221078113227521645793195311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147385408818347763862130207 221078113227521645793195311)
  ·
    refine ⟨331617169841282468689792967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221078113227521645793195311 331617169841282468689792967)
    ·
      refine ⟨497425754761923703034689451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331617169841282468689792967 497425754761923703034689451)
      ·
        refine ⟨746138632142885554552034177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497425754761923703034689451 746138632142885554552034177)
        ·
          refine ⟨559603974107164165914025633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746138632142885554552034177 559603974107164165914025633)
          ·
            refine ⟨419702980580373124435519225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559603974107164165914025633 419702980580373124435519225)
            ·
              refine ⟨314777235435279843326639419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419702980580373124435519225 314777235435279843326639419)
              ·
                refine ⟨472165853152919764989959129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314777235435279843326639419 472165853152919764989959129)
                ·
                  refine ⟨354124389864689823742469347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472165853152919764989959129 354124389864689823742469347)
                  ·
                    refine ⟨531186584797034735613704021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354124389864689823742469347 531186584797034735613704021)
                    ·
                      refine ⟨3112421395295125403986547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 531186584797034735613704021 3112421395295125403986547)
                      ·
                        rfl

theorem cell23_6061419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_6061419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061419 prefixEnd_6061419 := by exact prefixLift 6061419
  have htrace : WordTrace (prefixWord ++ tailWord_6061419) baseStart_6061419 baseEnd_6061419 := by
    simpa [prefixWord, tailWord_6061419, baseEnd_6061419] using wordTrace_append hprefix tailTrace_6061419
  have hstable : (prefixWord ++ tailWord_6061419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061419).length < 2 ^ (prefixWord ++ tailWord_6061419).sum := by decide
  have hdescent : baseEnd_6061419 < baseStart_6061419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061423 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_6061423 : Nat := 118140960795 + 6061423 * 2 ^ 59
def prefixEnd_6061423 : Nat := 4983230072969 + 3 ^ 40 * 6061423 * 2
def baseEnd_6061423 : Nat := 3112423449217743388336529

theorem tailTrace_6061423 : CollatzResearch.WordTrace tailWord_6061423 prefixEnd_6061423 3112423449217743388336529 := by
  unfold tailWord_6061423
  simp only [CollatzResearch.WordTrace]
  refine ⟨221078259119507154476340923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147385506079671436317560615 221078259119507154476340923)
  ·
    refine ⟨331617388679260731714511385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221078259119507154476340923 331617388679260731714511385)
    ·
      refine ⟨248713041509445548785883539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331617388679260731714511385 248713041509445548785883539)
      ·
        refine ⟨373069562264168323178825309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248713041509445548785883539 373069562264168323178825309)
        ·
          refine ⟨139901085849063121192059491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373069562264168323178825309 139901085849063121192059491)
          ·
            refine ⟨209851628773594681788089237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139901085849063121192059491 209851628773594681788089237)
            ·
              refine ⟨9836795098762250708816683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209851628773594681788089237 9836795098762250708816683)
              ·
                refine ⟨14755192648143376063225025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9836795098762250708816683 14755192648143376063225025)
                ·
                  refine ⟨11066394486107532047418769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14755192648143376063225025 11066394486107532047418769)
                  ·
                    refine ⟨8299795864580649035564077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11066394486107532047418769 8299795864580649035564077)
                    ·
                      refine ⟨3112423449217743388336529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299795864580649035564077 3112423449217743388336529)
                      ·
                        rfl

theorem cell23_6061423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_6061423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061423 prefixEnd_6061423 := by exact prefixLift 6061423
  have htrace : WordTrace (prefixWord ++ tailWord_6061423) baseStart_6061423 baseEnd_6061423 := by
    simpa [prefixWord, tailWord_6061423, baseEnd_6061423] using wordTrace_append hprefix tailTrace_6061423
  have hstable : (prefixWord ++ tailWord_6061423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061423).length < 2 ^ (prefixWord ++ tailWord_6061423).sum := by decide
  have hdescent : baseEnd_6061423 < baseStart_6061423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061443 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 6]
def baseStart_6061443 : Nat := 118140960795 + 6061443 * 2 ^ 59
def prefixEnd_6061443 : Nat := 4983230072969 + 3 ^ 40 * 6061443 * 2
def baseEnd_6061443 : Nat := 345825968758981478898493

theorem tailTrace_6061443 : CollatzResearch.WordTrace tailWord_6061443 prefixEnd_6061443 345825968758981478898493 := by
  unfold tailWord_6061443
  simp only [CollatzResearch.WordTrace]
  refine ⟨221078988579434697892068983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147385992386289798594712655 221078988579434697892068983)
  ·
    refine ⟨331618482869152046838103475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221078988579434697892068983 331618482869152046838103475)
    ·
      refine ⟨497427724303728070257155213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331618482869152046838103475 497427724303728070257155213)
      ·
        refine ⟨186535396613898026346433205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 497427724303728070257155213 186535396613898026346433205)
        ·
          refine ⟨17487693432552939969978113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186535396613898026346433205 17487693432552939969978113)
          ·
            refine ⟨13115770074414704977483585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17487693432552939969978113 13115770074414704977483585)
            ·
              refine ⟨9836827555811028733112689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13115770074414704977483585 9836827555811028733112689)
              ·
                refine ⟨7377620666858271549834517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9836827555811028733112689 7377620666858271549834517)
                ·
                  refine ⟨345825968758981478898493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7377620666858271549834517 345825968758981478898493)
                  ·
                    rfl

theorem cell23_6061443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 6].length) (baseStart_6061443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061443 prefixEnd_6061443 := by exact prefixLift 6061443
  have htrace : WordTrace (prefixWord ++ tailWord_6061443) baseStart_6061443 baseEnd_6061443 := by
    simpa [prefixWord, tailWord_6061443, baseEnd_6061443] using wordTrace_append hprefix tailTrace_6061443
  have hstable : (prefixWord ++ tailWord_6061443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061443).length < 2 ^ (prefixWord ++ tailWord_6061443).sum := by decide
  have hdescent : baseEnd_6061443 < baseStart_6061443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061447 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 1, 4]
def baseStart_6061447 : Nat := 118140960795 + 6061447 * 2 ^ 59
def prefixEnd_6061447 : Nat := 4983230072969 + 3 ^ 40 * 6061447 * 2
def baseEnd_6061447 : Nat := 1037478590917817098145473

theorem tailTrace_6061447 : CollatzResearch.WordTrace tailWord_6061447 prefixEnd_6061447 1037478590917817098145473 := by
  unfold tailWord_6061447
  simp only [CollatzResearch.WordTrace]
  refine ⟨221079134471420206575214595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147386089647613471050143063 221079134471420206575214595)
  ·
    refine ⟨331618701707130309862821893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221079134471420206575214595 331618701707130309862821893)
    ·
      refine ⟨62178506570086933099279105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331618701707130309862821893 62178506570086933099279105)
      ·
        refine ⟨46633879927565199824459329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62178506570086933099279105 46633879927565199824459329)
        ·
          refine ⟨34975409945673899868344497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46633879927565199824459329 34975409945673899868344497)
          ·
            refine ⟨26231557459255424901258373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34975409945673899868344497 26231557459255424901258373)
            ·
              refine ⟨4918417023610392168985945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26231557459255424901258373 4918417023610392168985945)
              ·
                refine ⟨3688812767707794126739459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4918417023610392168985945 3688812767707794126739459)
                ·
                  refine ⟨5533219151561691190109189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3688812767707794126739459 5533219151561691190109189)
                  ·
                    refine ⟨1037478590917817098145473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533219151561691190109189 1037478590917817098145473)
                    ·
                      rfl

theorem cell23_6061447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_6061447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061447 prefixEnd_6061447 := by exact prefixLift 6061447
  have htrace : WordTrace (prefixWord ++ tailWord_6061447) baseStart_6061447 baseEnd_6061447 := by
    simpa [prefixWord, tailWord_6061447, baseEnd_6061447] using wordTrace_append hprefix tailTrace_6061447
  have hstable : (prefixWord ++ tailWord_6061447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061447).length < 2 ^ (prefixWord ++ tailWord_6061447).sum := by decide
  have hdescent : baseEnd_6061447 < baseStart_6061447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061463 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_6061463 : Nat := 118140960795 + 6061463 * 2 ^ 59
def prefixEnd_6061463 : Nat := 4983230072969 + 3 ^ 40 * 6061463 * 2
def baseEnd_6061463 : Nat := 3112443988443923231836345

theorem tailTrace_6061463 : CollatzResearch.WordTrace tailWord_6061463 prefixEnd_6061463 3112443988443923231836345 := by
  unfold tailWord_6061463
  simp only [CollatzResearch.WordTrace]
  refine ⟨221079718039362241307797043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147386478692908160871864695 221079718039362241307797043)
  ·
    refine ⟨331619577059043361961695565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221079718039362241307797043 331619577059043361961695565)
    ·
      refine ⟨124357341397141260735635837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331619577059043361961695565 124357341397141260735635837)
      ·
        refine ⟨46634003023927972775863439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124357341397141260735635837 46634003023927972775863439)
        ·
          refine ⟨69951004535891959163795159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46634003023927972775863439 69951004535891959163795159)
          ·
            refine ⟨104926506803837938745692739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69951004535891959163795159 104926506803837938745692739)
            ·
              refine ⟨157389760205756908118539109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104926506803837938745692739 157389760205756908118539109)
              ·
                refine ⟨29510580038579420272226083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157389760205756908118539109 29510580038579420272226083)
                ·
                  refine ⟨44265870057869130408339125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29510580038579420272226083 44265870057869130408339125)
                  ·
                    refine ⟨4149925317925230975781793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44265870057869130408339125 4149925317925230975781793)
                    ·
                      refine ⟨3112443988443923231836345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4149925317925230975781793 3112443988443923231836345)
                      ·
                        rfl

theorem cell23_6061463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_6061463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061463 prefixEnd_6061463 := by exact prefixLift 6061463
  have htrace : WordTrace (prefixWord ++ tailWord_6061463) baseStart_6061463 baseEnd_6061463 := by
    simpa [prefixWord, tailWord_6061463, baseEnd_6061463] using wordTrace_append hprefix tailTrace_6061463
  have hstable : (prefixWord ++ tailWord_6061463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061463).length < 2 ^ (prefixWord ++ tailWord_6061463).sum := by decide
  have hdescent : baseEnd_6061463 < baseStart_6061463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061466 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6061466 : Nat := 118140960795 + 6061466 * 2 ^ 59
def prefixEnd_6061466 : Nat := 4983230072969 + 3 ^ 40 * 6061466 * 2
def baseEnd_6061466 : Nat := 3112445528885886720098831

theorem tailTrace_6061466 : CollatzResearch.WordTrace tailWord_6061466 prefixEnd_6061466 3112445528885886720098831 := by
  unfold tailWord_6061466
  simp only [CollatzResearch.WordTrace]
  refine ⟨55269956864587843205039063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147386551638900915213437501 55269956864587843205039063)
  ·
    refine ⟨82904935296881764807558595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55269956864587843205039063 82904935296881764807558595)
    ·
      refine ⟨124357402945322647211337893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82904935296881764807558595 124357402945322647211337893)
      ·
        refine ⟨23317013052247996352125855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124357402945322647211337893 23317013052247996352125855)
        ·
          refine ⟨34975519578371994528188783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23317013052247996352125855 34975519578371994528188783)
          ·
            refine ⟨52463279367557991792283175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34975519578371994528188783 52463279367557991792283175)
            ·
              refine ⟨78694919051336987688424763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52463279367557991792283175 78694919051336987688424763)
              ·
                refine ⟨118042378577005481532637145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78694919051336987688424763 118042378577005481532637145)
                ·
                  refine ⟨88531783932754111149477859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118042378577005481532637145 88531783932754111149477859)
                  ·
                    refine ⟨132797675899131166724216789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88531783932754111149477859 132797675899131166724216789)
                    ·
                      refine ⟨3112445528885886720098831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132797675899131166724216789 3112445528885886720098831)
                      ·
                        rfl

theorem cell23_6061466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6061466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061466 prefixEnd_6061466 := by exact prefixLift 6061466
  have htrace : WordTrace (prefixWord ++ tailWord_6061466) baseStart_6061466 baseEnd_6061466 := by
    simpa [prefixWord, tailWord_6061466, baseEnd_6061466] using wordTrace_append hprefix tailTrace_6061466
  have hstable : (prefixWord ++ tailWord_6061466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061466).length < 2 ^ (prefixWord ++ tailWord_6061466).sum := by decide
  have hdescent : baseEnd_6061466 < baseStart_6061466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061530 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_6061530 : Nat := 118140960795 + 6061530 * 2 ^ 59
def prefixEnd_6061530 : Nat := 4983230072969 + 3 ^ 40 * 6061530 * 2
def baseEnd_6061530 : Nat := 3112478391647774469698537

theorem tailTrace_6061530 : CollatzResearch.WordTrace tailWord_6061530 prefixEnd_6061530 3112478391647774469698537 := by
  unfold tailWord_6061530
  simp only [CollatzResearch.WordTrace]
  refine ⟨55270540432529877937621511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147388107820079674500324029 55270540432529877937621511)
  ·
    refine ⟨82905810648794816906432267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55270540432529877937621511 82905810648794816906432267)
    ·
      refine ⟨124358715973192225359648401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82905810648794816906432267 124358715973192225359648401)
      ·
        refine ⟨93269036979894169019736301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124358715973192225359648401 93269036979894169019736301)
        ·
          refine ⟨34975888867460313382401113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93269036979894169019736301 34975888867460313382401113)
          ·
            refine ⟨26231916650595235036800835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34975888867460313382401113 26231916650595235036800835)
            ·
              refine ⟨39347874975892852555201253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26231916650595235036800835 39347874975892852555201253)
              ·
                refine ⟨7377726557979909854100235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39347874975892852555201253 7377726557979909854100235)
                ·
                  refine ⟨11066589836969864781150353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377726557979909854100235 11066589836969864781150353)
                  ·
                    refine ⟨8299942377727398585862765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11066589836969864781150353 8299942377727398585862765)
                    ·
                      refine ⟨3112478391647774469698537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299942377727398585862765 3112478391647774469698537)
                      ·
                        rfl

theorem cell23_6061530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_6061530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061530 prefixEnd_6061530 := by exact prefixLift 6061530
  have htrace : WordTrace (prefixWord ++ tailWord_6061530) baseStart_6061530 baseEnd_6061530 := by
    simpa [prefixWord, tailWord_6061530, baseEnd_6061530] using wordTrace_append hprefix tailTrace_6061530
  have hstable : (prefixWord ++ tailWord_6061530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061530).length < 2 ^ (prefixWord ++ tailWord_6061530).sum := by decide
  have hdescent : baseEnd_6061530 < baseStart_6061530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061533 : List Nat := [1, 4, 3, 1, 1, 3, 1, 9]
def baseStart_6061533 : Nat := 118140960795 + 6061533 * 2 ^ 59
def prefixEnd_6061533 : Nat := 4983230072969 + 3 ^ 40 * 6061533 * 2
def baseEnd_6061533 : Nat := 115277034521842146591149

theorem tailTrace_6061533 : CollatzResearch.WordTrace tailWord_6061533 prefixEnd_6061533 115277034521842146591149 := by
  unfold tailWord_6061533
  simp only [CollatzResearch.WordTrace]
  refine ⟨221082271149108643262845253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147388180766072428841896835 221082271149108643262845253)
  ·
    refine ⟨41452925840457870611783485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221082271149108643262845253 41452925840457870611783485)
    ·
      refine ⟨15544847190171701479418807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41452925840457870611783485 15544847190171701479418807)
      ·
        refine ⟨23317270785257552219128211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15544847190171701479418807 23317270785257552219128211)
        ·
          refine ⟨34975906177886328328692317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23317270785257552219128211 34975906177886328328692317)
          ·
            refine ⟨13115964816707373123259619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34975906177886328328692317 13115964816707373123259619)
            ·
              refine ⟨19673947225061059684889429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115964816707373123259619 19673947225061059684889429)
              ·
                refine ⟨115277034521842146591149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19673947225061059684889429 115277034521842146591149)
                ·
                  rfl

theorem cell23_6061533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 9].length) (baseStart_6061533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061533 prefixEnd_6061533 := by exact prefixLift 6061533
  have htrace : WordTrace (prefixWord ++ tailWord_6061533) baseStart_6061533 baseEnd_6061533 := by
    simpa [prefixWord, tailWord_6061533, baseEnd_6061533] using wordTrace_append hprefix tailTrace_6061533
  have hstable : (prefixWord ++ tailWord_6061533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061533).length < 2 ^ (prefixWord ++ tailWord_6061533).sum := by decide
  have hdescent : baseEnd_6061533 < baseStart_6061533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061560 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_6061560 : Nat := 118140960795 + 6061560 * 2 ^ 59
def prefixEnd_6061560 : Nat := 4983230072969 + 3 ^ 40 * 6061560 * 2
def baseEnd_6061560 : Nat := 3112493796067409352323399

theorem tailTrace_6061560 : CollatzResearch.WordTrace tailWord_6061560 prefixEnd_6061560 3112493796067409352323399 := by
  unfold tailWord_6061560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110541627960005413437039067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147388837280007217916052089 110541627960005413437039067)
  ·
    refine ⟨165812441940008120155558601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110541627960005413437039067 165812441940008120155558601)
    ·
      refine ⟨124359331455006090116668951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165812441940008120155558601 124359331455006090116668951)
      ·
        refine ⟨186538997182509135175003427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124359331455006090116668951 186538997182509135175003427)
        ·
          refine ⟨279808495773763702762505141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186538997182509135175003427 279808495773763702762505141)
          ·
            refine ⟨26232046478790347133984857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 279808495773763702762505141 26232046478790347133984857)
            ·
              refine ⟨19674034859092760350488643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26232046478790347133984857 19674034859092760350488643)
              ·
                refine ⟨29511052288639140525732965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19674034859092760350488643 29511052288639140525732965)
                ·
                  refine ⟨5533322304119838848574931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29511052288639140525732965 5533322304119838848574931)
                  ·
                    refine ⟨8299983456179758272862397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5533322304119838848574931 8299983456179758272862397)
                    ·
                      refine ⟨3112493796067409352323399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8299983456179758272862397 3112493796067409352323399)
                      ·
                        rfl

theorem cell23_6061560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_6061560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061560 prefixEnd_6061560 := by exact prefixLift 6061560
  have htrace : WordTrace (prefixWord ++ tailWord_6061560) baseStart_6061560 baseEnd_6061560 := by
    simpa [prefixWord, tailWord_6061560, baseEnd_6061560] using wordTrace_append hprefix tailTrace_6061560
  have hstable : (prefixWord ++ tailWord_6061560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061560).length < 2 ^ (prefixWord ++ tailWord_6061560).sum := by decide
  have hdescent : baseEnd_6061560 < baseStart_6061560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061587 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 1, 3, 2]
def baseStart_6061587 : Nat := 118140960795 + 6061587 * 2 ^ 59
def prefixEnd_6061587 : Nat := 4983230072969 + 3 ^ 40 * 6061587 * 2
def baseEnd_6061587 : Nat := 3112507660045080746685775

theorem tailTrace_6061587 : CollatzResearch.WordTrace tailWord_6061587 prefixEnd_6061587 3112507660045080746685775 := by
  unfold tailWord_6061587
  simp only [CollatzResearch.WordTrace]
  refine ⟨221084240690913010485311015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147389493793942006990207343 221084240690913010485311015)
  ·
    refine ⟨331626361036369515727966523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221084240690913010485311015 331626361036369515727966523)
    ·
      refine ⟨497439541554554273591949785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331626361036369515727966523 497439541554554273591949785)
      ·
        refine ⟨373079656165915705193962339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497439541554554273591949785 373079656165915705193962339)
        ·
          refine ⟨559619484248873557790943509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373079656165915705193962339 559619484248873557790943509)
          ·
            refine ⟨26232163324165948021450477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 559619484248873557790943509 26232163324165948021450477)
            ·
              refine ⟨9837061246562230508043929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26232163324165948021450477 9837061246562230508043929)
              ·
                refine ⟨7377795934921672881032947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9837061246562230508043929 7377795934921672881032947)
                ·
                  refine ⟨11066693902382509321549421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7377795934921672881032947 11066693902382509321549421)
                  ·
                    refine ⟨4150010213393440995581033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11066693902382509321549421 4150010213393440995581033)
                    ·
                      refine ⟨3112507660045080746685775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150010213393440995581033 3112507660045080746685775)
                      ·
                        rfl

theorem cell23_6061587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3, 2].length) (baseStart_6061587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061587 prefixEnd_6061587 := by exact prefixLift 6061587
  have htrace : WordTrace (prefixWord ++ tailWord_6061587) baseStart_6061587 baseEnd_6061587 := by
    simpa [prefixWord, tailWord_6061587, baseEnd_6061587] using wordTrace_append hprefix tailTrace_6061587
  have hstable : (prefixWord ++ tailWord_6061587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061587).length < 2 ^ (prefixWord ++ tailWord_6061587).sum := by decide
  have hdescent : baseEnd_6061587 < baseStart_6061587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061598 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6061598 : Nat := 118140960795 + 6061598 * 2 ^ 59
def prefixEnd_6061598 : Nat := 4983230072969 + 3 ^ 40 * 6061598 * 2
def baseEnd_6061598 : Nat := 3112513308332280203648225

theorem tailTrace_6061598 : CollatzResearch.WordTrace tailWord_6061598 prefixEnd_6061598 3112513308332280203648225 := by
  unfold tailWord_6061598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635580236734144920495181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147389761262582106242640965 27635580236734144920495181)
  ·
    refine ⟨10363342588775304345185693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27635580236734144920495181 10363342588775304345185693)
    ·
      refine ⟨3886253470790739129444635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10363342588775304345185693 3886253470790739129444635)
      ·
        refine ⟨5829380206186108694166953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886253470790739129444635 5829380206186108694166953)
        ·
          refine ⟨4372035154639581520625215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5829380206186108694166953 4372035154639581520625215)
          ·
            refine ⟨6558052731959372280937823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372035154639581520625215 6558052731959372280937823)
            ·
              refine ⟨9837079097939058421406735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558052731959372280937823 9837079097939058421406735)
              ·
                refine ⟨14755618646908587632110103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837079097939058421406735 14755618646908587632110103)
                ·
                  refine ⟨22133427970362881448165155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14755618646908587632110103 22133427970362881448165155)
                  ·
                    refine ⟨33200141955544322172247733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22133427970362881448165155 33200141955544322172247733)
                    ·
                      refine ⟨3112513308332280203648225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33200141955544322172247733 3112513308332280203648225)
                      ·
                        rfl

theorem cell23_6061598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6061598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061598 prefixEnd_6061598 := by exact prefixLift 6061598
  have htrace : WordTrace (prefixWord ++ tailWord_6061598) baseStart_6061598 baseEnd_6061598 := by
    simpa [prefixWord, tailWord_6061598, baseEnd_6061598] using wordTrace_append hprefix tailTrace_6061598
  have hstable : (prefixWord ++ tailWord_6061598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061598).length < 2 ^ (prefixWord ++ tailWord_6061598).sum := by decide
  have hdescent : baseEnd_6061598 < baseStart_6061598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061690 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_6061690 : Nat := 118140960795 + 6061690 * 2 ^ 59
def prefixEnd_6061690 : Nat := 4983230072969 + 3 ^ 40 * 6061690 * 2
def baseEnd_6061690 : Nat := 3112560548552493843697801

theorem tailTrace_6061690 : CollatzResearch.WordTrace tailWord_6061690 prefixEnd_6061690 3112560548552493843697801 := by
  unfold tailWord_6061690
  simp only [CollatzResearch.WordTrace]
  refine ⟨55271999352384964769077631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147391998273026572717540349 55271999352384964769077631)
  ·
    refine ⟨82907999028577447153616447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55271999352384964769077631 82907999028577447153616447)
    ·
      refine ⟨124361998542866170730424671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82907999028577447153616447 124361998542866170730424671)
      ·
        refine ⟨186542997814299256095637007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124361998542866170730424671 186542997814299256095637007)
        ·
          refine ⟨279814496721448884143455511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186542997814299256095637007 279814496721448884143455511)
          ·
            refine ⟨419721745082173326215183267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279814496721448884143455511 419721745082173326215183267)
            ·
              refine ⟨629582617623259989322774901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419721745082173326215183267 629582617623259989322774901)
              ·
                refine ⟨59023370402180623999010147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629582617623259989322774901 59023370402180623999010147)
                ·
                  refine ⟨88535055603270935998515221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59023370402180623999010147 88535055603270935998515221)
                  ·
                    refine ⟨4150080731403325124930401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88535055603270935998515221 4150080731403325124930401)
                    ·
                      refine ⟨3112560548552493843697801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150080731403325124930401 3112560548552493843697801)
                      ·
                        rfl

theorem cell23_6061690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_6061690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061690 prefixEnd_6061690 := by exact prefixLift 6061690
  have htrace : WordTrace (prefixWord ++ tailWord_6061690) baseStart_6061690 baseEnd_6061690 := by
    simpa [prefixWord, tailWord_6061690, baseEnd_6061690] using wordTrace_append hprefix tailTrace_6061690
  have hstable : (prefixWord ++ tailWord_6061690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061690).length < 2 ^ (prefixWord ++ tailWord_6061690).sum := by decide
  have hdescent : baseEnd_6061690 < baseStart_6061690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061733 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_6061733 : Nat := 118140960795 + 6061733 * 2 ^ 59
def prefixEnd_6061733 : Nat := 4983230072969 + 3 ^ 40 * 6061733 * 2
def baseEnd_6061733 : Nat := 3112582628220637175460103

theorem tailTrace_6061733 : CollatzResearch.WordTrace tailWord_6061733 prefixEnd_6061733 3112582628220637175460103 := by
  unfold tailWord_6061733
  simp only [CollatzResearch.WordTrace]
  refine ⟨221089565748384077420125853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147393043832256051613417235 221089565748384077420125853)
  ·
    refine ⟨82908587155644029032547195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221089565748384077420125853 82908587155644029032547195)
    ·
      refine ⟨124362880733466043548820793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82908587155644029032547195 124362880733466043548820793)
      ·
        refine ⟨93272160550099532661615595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124362880733466043548820793 93272160550099532661615595)
        ·
          refine ⟨139908240825149298992423393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93272160550099532661615595 139908240825149298992423393)
          ·
            refine ⟨104931180618861974244317545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139908240825149298992423393 104931180618861974244317545)
            ·
              refine ⟨78698385464146480683238159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104931180618861974244317545 78698385464146480683238159)
              ·
                refine ⟨118047578196219721024857239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78698385464146480683238159 118047578196219721024857239)
                ·
                  refine ⟨177071367294329581537285859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118047578196219721024857239 177071367294329581537285859)
                  ·
                    refine ⟨265607050941494372305928789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177071367294329581537285859 265607050941494372305928789)
                    ·
                      refine ⟨3112582628220637175460103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265607050941494372305928789 3112582628220637175460103)
                      ·
                        rfl

theorem cell23_6061733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_6061733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061733 prefixEnd_6061733 := by exact prefixLift 6061733
  have htrace : WordTrace (prefixWord ++ tailWord_6061733) baseStart_6061733 baseEnd_6061733 := by
    simpa [prefixWord, tailWord_6061733, baseEnd_6061733] using wordTrace_append hprefix tailTrace_6061733
  have hstable : (prefixWord ++ tailWord_6061733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061733).length < 2 ^ (prefixWord ++ tailWord_6061733).sum := by decide
  have hdescent : baseEnd_6061733 < baseStart_6061733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061757 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_6061757 : Nat := 118140960795 + 6061757 * 2 ^ 59
def prefixEnd_6061757 : Nat := 4983230072969 + 3 ^ 40 * 6061757 * 2
def baseEnd_6061757 : Nat := 3112594951756345081559993

theorem tailTrace_6061757 : CollatzResearch.WordTrace tailWord_6061757 prefixEnd_6061757 3112594951756345081559993 := by
  unfold tailWord_6061757
  simp only [CollatzResearch.WordTrace]
  refine ⟨221090441100297129518999525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147393627400198086345999683 221090441100297129518999525)
  ·
    refine ⟨41454457706305711784812411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221090441100297129518999525 41454457706305711784812411)
    ·
      refine ⟨62181686559458567677218617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41454457706305711784812411 62181686559458567677218617)
      ·
        refine ⟨46636264919593925757913963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62181686559458567677218617 46636264919593925757913963)
        ·
          refine ⟨69954397379390888636870945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46636264919593925757913963 69954397379390888636870945)
          ·
            refine ⟨52465798034543166477653209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69954397379390888636870945 52465798034543166477653209)
            ·
              refine ⟨39349348525907374858239907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52465798034543166477653209 39349348525907374858239907)
              ·
                refine ⟨59024022788861062287359861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39349348525907374858239907 59024022788861062287359861)
                ·
                  refine ⟨5533502136455724589439987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59024022788861062287359861 5533502136455724589439987)
                  ·
                    refine ⟨8300253204683586884159981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5533502136455724589439987 8300253204683586884159981)
                    ·
                      refine ⟨3112594951756345081559993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8300253204683586884159981 3112594951756345081559993)
                      ·
                        rfl

theorem cell23_6061757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_6061757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061757 prefixEnd_6061757 := by exact prefixLift 6061757
  have htrace : WordTrace (prefixWord ++ tailWord_6061757) baseStart_6061757 baseEnd_6061757 := by
    simpa [prefixWord, tailWord_6061757, baseEnd_6061757] using wordTrace_append hprefix tailTrace_6061757
  have hstable : (prefixWord ++ tailWord_6061757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061757).length < 2 ^ (prefixWord ++ tailWord_6061757).sum := by decide
  have hdescent : baseEnd_6061757 < baseStart_6061757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061760 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_6061760 : Nat := 118140960795 + 6061760 * 2 ^ 59
def prefixEnd_6061760 : Nat := 4983230072969 + 3 ^ 40 * 6061760 * 2
def baseEnd_6061760 : Nat := 1037532164066102856607493

theorem tailTrace_6061760 : CollatzResearch.WordTrace tailWord_6061760 prefixEnd_6061760 1037532164066102856607493 := by
  unfold tailWord_6061760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110545275259643130515679367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147393700346190840687572489 110545275259643130515679367)
  ·
    refine ⟨165817912889464695773519051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110545275259643130515679367 165817912889464695773519051)
    ·
      refine ⟨248726869334197043660278577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165817912889464695773519051 248726869334197043660278577)
      ·
        refine ⟨186545152000647782745208933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248726869334197043660278577 186545152000647782745208933)
        ·
          refine ⟨34977216000121459264726675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186545152000647782745208933 34977216000121459264726675)
          ·
            refine ⟨52465824000182188897090013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34977216000121459264726675 52465824000182188897090013)
            ·
              refine ⟨19674684000068320836408755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52465824000182188897090013 19674684000068320836408755)
              ·
                refine ⟨29512026000102481254613133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19674684000068320836408755 29512026000102481254613133)
                ·
                  refine ⟨11067009750038430470479925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29512026000102481254613133 11067009750038430470479925)
                  ·
                    refine ⟨1037532164066102856607493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11067009750038430470479925 1037532164066102856607493)
                    ·
                      rfl

theorem cell23_6061760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_6061760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061760 prefixEnd_6061760 := by exact prefixLift 6061760
  have htrace : WordTrace (prefixWord ++ tailWord_6061760) baseStart_6061760 baseEnd_6061760 := by
    simpa [prefixWord, tailWord_6061760, baseEnd_6061760] using wordTrace_append hprefix tailTrace_6061760
  have hstable : (prefixWord ++ tailWord_6061760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061760).length < 2 ^ (prefixWord ++ tailWord_6061760).sum := by decide
  have hdescent : baseEnd_6061760 < baseStart_6061760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061807 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 2, 4]
def baseStart_6061807 : Nat := 118140960795 + 6061807 * 2 ^ 59
def prefixEnd_6061807 : Nat := 4983230072969 + 3 ^ 40 * 6061807 * 2
def baseEnd_6061807 : Nat := 1037540208596356628644921

theorem tailTrace_6061807 : CollatzResearch.WordTrace tailWord_6061807 prefixEnd_6061807 1037540208596356628644921 := by
  unfold tailWord_6061807
  simp only [CollatzResearch.WordTrace]
  refine ⟨221092264750115988058319675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147394843166743992038879783 221092264750115988058319675)
  ·
    refine ⟨331638397125173982087479513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221092264750115988058319675 331638397125173982087479513)
    ·
      refine ⟨248728797843880486565609635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331638397125173982087479513 248728797843880486565609635)
      ·
        refine ⟨373093196765820729848414453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248728797843880486565609635 373093196765820729848414453)
        ·
          refine ⟨34977487196795693423288855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 373093196765820729848414453 34977487196795693423288855)
          ·
            refine ⟨52466230795193540134933283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34977487196795693423288855 52466230795193540134933283)
            ·
              refine ⟨78699346192790310202399925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52466230795193540134933283 78699346192790310202399925)
              ·
                refine ⟨7378063705574091581474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78699346192790310202399925 7378063705574091581474993)
                ·
                  refine ⟨5533547779180568686106245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378063705574091581474993 5533547779180568686106245)
                  ·
                    refine ⟨1037540208596356628644921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533547779180568686106245 1037540208596356628644921)
                    ·
                      rfl

theorem cell23_6061807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_6061807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061807 prefixEnd_6061807 := by exact prefixLift 6061807
  have htrace : WordTrace (prefixWord ++ tailWord_6061807) baseStart_6061807 baseEnd_6061807 := by
    simpa [prefixWord, tailWord_6061807, baseEnd_6061807] using wordTrace_append hprefix tailTrace_6061807
  have hstable : (prefixWord ++ tailWord_6061807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061807).length < 2 ^ (prefixWord ++ tailWord_6061807).sum := by decide
  have hdescent : baseEnd_6061807 < baseStart_6061807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061834 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_6061834 : Nat := 118140960795 + 6061834 * 2 ^ 59
def prefixEnd_6061834 : Nat := 4983230072969 + 3 ^ 40 * 6061834 * 2
def baseEnd_6061834 : Nat := 3112634489766741280297139

theorem tailTrace_6061834 : CollatzResearch.WordTrace tailWord_6061834 prefixEnd_6061834 3112634489766741280297139 := by
  unfold tailWord_6061834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55273312380254542917388139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147395499680678781113035037 55273312380254542917388139)
  ·
    refine ⟨82909968570381814376082209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55273312380254542917388139 82909968570381814376082209)
    ·
      refine ⟨62182476427786360782061657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82909968570381814376082209 62182476427786360782061657)
      ·
        refine ⟨46636857320839770586546243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62182476427786360782061657 46636857320839770586546243)
        ·
          refine ⟨69955285981259655879819365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46636857320839770586546243 69955285981259655879819365)
          ·
            refine ⟨13116616121486185477466131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69955285981259655879819365 13116616121486185477466131)
            ·
              refine ⟨19674924182229278216199197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13116616121486185477466131 19674924182229278216199197)
              ·
                refine ⟨7378096568335979331074699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19674924182229278216199197 7378096568335979331074699)
                ·
                  refine ⟨11067144852503968996612049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378096568335979331074699 11067144852503968996612049)
                  ·
                    refine ⟨8300358639377976747459037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11067144852503968996612049 8300358639377976747459037)
                    ·
                      refine ⟨3112634489766741280297139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8300358639377976747459037 3112634489766741280297139)
                      ·
                        rfl

theorem cell23_6061834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_6061834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061834 prefixEnd_6061834 := by exact prefixLift 6061834
  have htrace : WordTrace (prefixWord ++ tailWord_6061834) baseStart_6061834 baseEnd_6061834 := by
    simpa [prefixWord, tailWord_6061834, baseEnd_6061834] using wordTrace_append hprefix tailTrace_6061834
  have hstable : (prefixWord ++ tailWord_6061834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061834).length < 2 ^ (prefixWord ++ tailWord_6061834).sum := by decide
  have hdescent : baseEnd_6061834 < baseStart_6061834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061864 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6061864 : Nat := 118140960795 + 6061864 * 2 ^ 59
def prefixEnd_6061864 : Nat := 4983230072969 + 3 ^ 40 * 6061864 * 2
def baseEnd_6061864 : Nat := 3112649894186376162922001

theorem tailTrace_6061864 : CollatzResearch.WordTrace tailWord_6061864 prefixEnd_6061864 3112649894186376162922001 := by
  unfold tailWord_6061864
  simp only [CollatzResearch.WordTrace]
  refine ⟨110547171855454743396572323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147396229140606324528763097 110547171855454743396572323)
  ·
    refine ⟨165820757783182115094858485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110547171855454743396572323 165820757783182115094858485)
    ·
      refine ⟨15545696042173323290142983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165820757783182115094858485 15545696042173323290142983)
      ·
        refine ⟨23318544063259984935214475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15545696042173323290142983 23318544063259984935214475)
        ·
          refine ⟨34977816094889977402821713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23318544063259984935214475 34977816094889977402821713)
          ·
            refine ⟨26233362071167483052116285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34977816094889977402821713 26233362071167483052116285)
            ·
              refine ⟨9837510776687806144543607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26233362071167483052116285 9837510776687806144543607)
              ·
                refine ⟨14756266165031709216815411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837510776687806144543607 14756266165031709216815411)
                ·
                  refine ⟨22134399247547563825223117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14756266165031709216815411 22134399247547563825223117)
                  ·
                    refine ⟨8300399717830336434458669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22134399247547563825223117 8300399717830336434458669)
                    ·
                      refine ⟨3112649894186376162922001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8300399717830336434458669 3112649894186376162922001)
                      ·
                        rfl

theorem cell23_6061864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6061864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061864 prefixEnd_6061864 := by exact prefixLift 6061864
  have htrace : WordTrace (prefixWord ++ tailWord_6061864) baseStart_6061864 baseEnd_6061864 := by
    simpa [prefixWord, tailWord_6061864, baseEnd_6061864] using wordTrace_append hprefix tailTrace_6061864
  have hstable : (prefixWord ++ tailWord_6061864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061864).length < 2 ^ (prefixWord ++ tailWord_6061864).sum := by decide
  have hdescent : baseEnd_6061864 < baseStart_6061864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061921 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_6061921 : Nat := 118140960795 + 6061921 * 2 ^ 59
def prefixEnd_6061921 : Nat := 4983230072969 + 3 ^ 40 * 6061921 * 2
def baseEnd_6061921 : Nat := 3112679162583682439909239

theorem tailTrace_6061921 : CollatzResearch.WordTrace tailWord_6061921 prefixEnd_6061921 3112679162583682439909239 := by
  unfold tailWord_6061921
  simp only [CollatzResearch.WordTrace]
  refine ⟨221096422671702985527969617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147397615114468657018646411 221096422671702985527969617)
  ·
    refine ⟨165822317003777239145977213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221096422671702985527969617 165822317003777239145977213)
    ·
      refine ⟨62183368876416464679741455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165822317003777239145977213 62183368876416464679741455)
      ·
        refine ⟨93275053314624697019612183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62183368876416464679741455 93275053314624697019612183)
        ·
          refine ⟨139912579971937045529418275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93275053314624697019612183 139912579971937045529418275)
          ·
            refine ⟨209868869957905568294127413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139912579971937045529418275 209868869957905568294127413)
            ·
              refine ⟨19675206558553647027574445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209868869957905568294127413 19675206558553647027574445)
              ·
                refine ⟨7378202459457617635340417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19675206558553647027574445 7378202459457617635340417)
                ·
                  refine ⟨5533651844593213226505313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378202459457617635340417 5533651844593213226505313)
                  ·
                    refine ⟨4150238883444909919878985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5533651844593213226505313 4150238883444909919878985)
                    ·
                      refine ⟨3112679162583682439909239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150238883444909919878985 3112679162583682439909239)
                      ·
                        rfl

theorem cell23_6061921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_6061921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061921 prefixEnd_6061921 := by exact prefixLift 6061921
  have htrace : WordTrace (prefixWord ++ tailWord_6061921) baseStart_6061921 baseEnd_6061921 := by
    simpa [prefixWord, tailWord_6061921, baseEnd_6061921] using wordTrace_append hprefix tailTrace_6061921
  have hstable : (prefixWord ++ tailWord_6061921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061921).length < 2 ^ (prefixWord ++ tailWord_6061921).sum := by decide
  have hdescent : baseEnd_6061921 < baseStart_6061921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061957 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_6061957 : Nat := 118140960795 + 6061957 * 2 ^ 59
def prefixEnd_6061957 : Nat := 4983230072969 + 3 ^ 40 * 6061957 * 2
def baseEnd_6061957 : Nat := 1037565882629081433019691

theorem tailTrace_6061957 : CollatzResearch.WordTrace tailWord_6061957 prefixEnd_6061957 1037565882629081433019691 := by
  unfold tailWord_6061957
  simp only [CollatzResearch.WordTrace]
  refine ⟨221097735699572563676280125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147398490466381709117520083 221097735699572563676280125)
  ·
    refine ⟨82911650887339711378605047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221097735699572563676280125 82911650887339711378605047)
    ·
      refine ⟨124367476331009567067907571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82911650887339711378605047 124367476331009567067907571)
      ·
        refine ⟨186551214496514350601861357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124367476331009567067907571 186551214496514350601861357)
        ·
          refine ⟨69956705436192881475698009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186551214496514350601861357 69956705436192881475698009)
          ·
            refine ⟨52467529077144661106773507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69956705436192881475698009 52467529077144661106773507)
            ·
              refine ⟨78701293615716991660160261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52467529077144661106773507 78701293615716991660160261)
              ·
                refine ⟨14756492552946935936280049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78701293615716991660160261 14756492552946935936280049)
                ·
                  refine ⟨11067369414710201952210037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14756492552946935936280049 11067369414710201952210037)
                  ·
                    refine ⟨1037565882629081433019691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11067369414710201952210037 1037565882629081433019691)
                    ·
                      rfl

theorem cell23_6061957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_6061957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061957 prefixEnd_6061957 := by exact prefixLift 6061957
  have htrace : WordTrace (prefixWord ++ tailWord_6061957) baseStart_6061957 baseEnd_6061957 := by
    simpa [prefixWord, tailWord_6061957, baseEnd_6061957] using wordTrace_append hprefix tailTrace_6061957
  have hstable : (prefixWord ++ tailWord_6061957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061957).length < 2 ^ (prefixWord ++ tailWord_6061957).sum := by decide
  have hdescent : baseEnd_6061957 < baseStart_6061957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061977 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_6061977 : Nat := 118140960795 + 6061977 * 2 ^ 59
def prefixEnd_6061977 : Nat := 4983230072969 + 3 ^ 40 * 6061977 * 2
def baseEnd_6061977 : Nat := 3112707917500334220808981

theorem tailTrace_6061977 : CollatzResearch.WordTrace tailWord_6061977 prefixEnd_6061977 3112707917500334220808981 := by
  unfold tailWord_6061977
  simp only [CollatzResearch.WordTrace]
  refine ⟨221098465159500107092008185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147398976773000071394672123 221098465159500107092008185)
  ·
    refine ⟨165823848869625080319006139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221098465159500107092008185 165823848869625080319006139)
    ·
      refine ⟨248735773304437620478509209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165823848869625080319006139 248735773304437620478509209)
      ·
        refine ⟨186551829978328215358881907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248735773304437620478509209 186551829978328215358881907)
        ·
          refine ⟨279827744967492323038322861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186551829978328215358881907 279827744967492323038322861)
          ·
            refine ⟨104935404362809621139371073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279827744967492323038322861 104935404362809621139371073)
            ·
              refine ⟨78701553272107215854528305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104935404362809621139371073 78701553272107215854528305)
              ·
                refine ⟨59026164954080411890896229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78701553272107215854528305 59026164954080411890896229)
                ·
                  refine ⟨11067405928890077229543043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59026164954080411890896229 11067405928890077229543043)
                  ·
                    refine ⟨16601108893335115844314565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11067405928890077229543043 16601108893335115844314565)
                    ·
                      refine ⟨3112707917500334220808981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16601108893335115844314565 3112707917500334220808981)
                      ·
                        rfl

theorem cell23_6061977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_6061977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061977 prefixEnd_6061977 := by exact prefixLift 6061977
  have htrace : WordTrace (prefixWord ++ tailWord_6061977) baseStart_6061977 baseEnd_6061977 := by
    simpa [prefixWord, tailWord_6061977, baseEnd_6061977] using wordTrace_append hprefix tailTrace_6061977
  have hstable : (prefixWord ++ tailWord_6061977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061977).length < 2 ^ (prefixWord ++ tailWord_6061977).sum := by decide
  have hdescent : baseEnd_6061977 < baseStart_6061977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6061991 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 2, 5]
def baseStart_6061991 : Nat := 118140960795 + 6061991 * 2 ^ 59
def prefixEnd_6061991 : Nat := 4983230072969 + 3 ^ 40 * 6061991 * 2
def baseEnd_6061991 : Nat := 1037571702076499055344639

theorem tailTrace_6061991 : CollatzResearch.WordTrace tailWord_6061991 prefixEnd_6061991 1037571702076499055344639 := by
  unfold tailWord_6061991
  simp only [CollatzResearch.WordTrace]
  refine ⟨221098975781449387483017827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147399317187632924988678551 221098975781449387483017827)
  ·
    refine ⟨331648463672174081224526741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221098975781449387483017827 331648463672174081224526741)
    ·
      refine ⟨15546021734633160057399691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 331648463672174081224526741 15546021734633160057399691)
      ·
        refine ⟨23319032601949740086099537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15546021734633160057399691 23319032601949740086099537)
        ·
          refine ⟨17489274451462305064574653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23319032601949740086099537 17489274451462305064574653)
          ·
            refine ⟨6558477919298364399215495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17489274451462305064574653 6558477919298364399215495)
            ·
              refine ⟨9837716878947546598823243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558477919298364399215495 9837716878947546598823243)
              ·
                refine ⟨14756575318421319898234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837716878947546598823243 14756575318421319898234865)
                ·
                  refine ⟨11067431488815989923676149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14756575318421319898234865 11067431488815989923676149)
                  ·
                    refine ⟨1037571702076499055344639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11067431488815989923676149 1037571702076499055344639)
                    ·
                      rfl

theorem cell23_6061991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_6061991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6061991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6061991 prefixEnd_6061991 := by exact prefixLift 6061991
  have htrace : WordTrace (prefixWord ++ tailWord_6061991) baseStart_6061991 baseEnd_6061991 := by
    simpa [prefixWord, tailWord_6061991, baseEnd_6061991] using wordTrace_append hprefix tailTrace_6061991
  have hstable : (prefixWord ++ tailWord_6061991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6061991).length < 2 ^ (prefixWord ++ tailWord_6061991).sum := by decide
  have hdescent : baseEnd_6061991 < baseStart_6061991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6061991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062055 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 1, 4]
def baseStart_6062055 : Nat := 118140960795 + 6062055 * 2 ^ 59
def prefixEnd_6062055 : Nat := 4983230072969 + 3 ^ 40 * 6062055 * 2
def baseEnd_6062055 : Nat := 1037582656330461638544541

theorem tailTrace_6062055 : CollatzResearch.WordTrace tailWord_6062055 prefixEnd_6062055 1037582656330461638544541 := by
  unfold tailWord_6062055
  simp only [CollatzResearch.WordTrace]
  refine ⟨221101310053217526413347619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147400873368811684275565079 221101310053217526413347619)
  ·
    refine ⟨331651965079826289620021429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221101310053217526413347619 331651965079826289620021429)
    ·
      refine ⟨31092371726233714651877009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 331651965079826289620021429 31092371726233714651877009)
      ·
        refine ⟨23319278794675285988907757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31092371726233714651877009 23319278794675285988907757)
        ·
          refine ⟨8744729548003232245840409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23319278794675285988907757 8744729548003232245840409)
          ·
            refine ⟨6558547161002424184380307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8744729548003232245840409 6558547161002424184380307)
            ·
              refine ⟨9837820741503636276570461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558547161002424184380307 9837820741503636276570461)
              ·
                refine ⟨3689182778063863603713923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9837820741503636276570461 3689182778063863603713923)
                ·
                  refine ⟨5533774167095795405570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689182778063863603713923 5533774167095795405570885)
                  ·
                    refine ⟨1037582656330461638544541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5533774167095795405570885 1037582656330461638544541)
                    ·
                      rfl

theorem cell23_6062055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_6062055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062055 prefixEnd_6062055 := by exact prefixLift 6062055
  have htrace : WordTrace (prefixWord ++ tailWord_6062055) baseStart_6062055 baseEnd_6062055 := by
    simpa [prefixWord, tailWord_6062055, baseEnd_6062055] using wordTrace_append hprefix tailTrace_6062055
  have hstable : (prefixWord ++ tailWord_6062055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062055).length < 2 ^ (prefixWord ++ tailWord_6062055).sum := by decide
  have hdescent : baseEnd_6062055 < baseStart_6062055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062064 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_6062064 : Nat := 118140960795 + 6062064 * 2 ^ 59
def prefixEnd_6062064 : Nat := 4983230072969 + 3 ^ 40 * 6062064 * 2
def baseEnd_6062064 : Nat := 1037584196772425126807027

theorem tailTrace_6062064 : CollatzResearch.WordTrace tailWord_6062064 prefixEnd_6062064 1037584196772425126807027 := by
  unfold tailWord_6062064
  simp only [CollatzResearch.WordTrace]
  refine ⟨110550819155092460475212623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147401092206789947300283497 110550819155092460475212623)
  ·
    refine ⟨165826228732638690712818935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110550819155092460475212623 165826228732638690712818935)
    ·
      refine ⟨248739343098958036069228403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165826228732638690712818935 248739343098958036069228403)
      ·
        refine ⟨373109014648437054103842605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248739343098958036069228403 373109014648437054103842605)
        ·
          refine ⟨139915880493163895288940977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373109014648437054103842605 139915880493163895288940977)
          ·
            refine ⟨104936910369872921466705733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139915880493163895288940977 104936910369872921466705733)
            ·
              refine ⟨19675670694351172775007325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104936910369872921466705733 19675670694351172775007325)
              ·
                refine ⟨7378376510381689790627747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19675670694351172775007325 7378376510381689790627747)
                ·
                  refine ⟨11067564765572534685941621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378376510381689790627747 11067564765572534685941621)
                  ·
                    refine ⟨1037584196772425126807027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11067564765572534685941621 1037584196772425126807027)
                    ·
                      rfl

theorem cell23_6062064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_6062064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062064 prefixEnd_6062064 := by exact prefixLift 6062064
  have htrace : WordTrace (prefixWord ++ tailWord_6062064) baseStart_6062064 baseEnd_6062064 := by
    simpa [prefixWord, tailWord_6062064, baseEnd_6062064] using wordTrace_append hprefix tailTrace_6062064
  have hstable : (prefixWord ++ tailWord_6062064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062064).length < 2 ^ (prefixWord ++ tailWord_6062064).sum := by decide
  have hdescent : baseEnd_6062064 < baseStart_6062064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062094 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_6062094 : Nat := 118140960795 + 6062094 * 2 ^ 59
def prefixEnd_6062094 : Nat := 4983230072969 + 3 ^ 40 * 6062094 * 2
def baseEnd_6062094 : Nat := 1037589331578970087681981

theorem tailTrace_6062094 : CollatzResearch.WordTrace tailWord_6062094 prefixEnd_6062094 1037589331578970087681981 := by
  unfold tailWord_6062094
  simp only [CollatzResearch.WordTrace]
  refine ⟨27637841562509529509252167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147401821666717490716011557 27637841562509529509252167)
  ·
    refine ⟨41456762343764294263878251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27637841562509529509252167 41456762343764294263878251)
    ·
      refine ⟨62185143515646441395817377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41456762343764294263878251 62185143515646441395817377)
      ·
        refine ⟨46638857636734831046863033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62185143515646441395817377 46638857636734831046863033)
        ·
          refine ⟨34979143227551123285147275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46638857636734831046863033 34979143227551123285147275)
          ·
            refine ⟨52468714841326684927720913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34979143227551123285147275 52468714841326684927720913)
            ·
              refine ⟨39351536130995013695790685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52468714841326684927720913 39351536130995013695790685)
              ·
                refine ⟨14756826049123130135921507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39351536130995013695790685 14756826049123130135921507)
                ·
                  refine ⟨22135239073684695203882261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14756826049123130135921507 22135239073684695203882261)
                  ·
                    refine ⟨1037589331578970087681981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22135239073684695203882261 1037589331578970087681981)
                    ·
                      rfl

theorem cell23_6062094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_6062094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062094 prefixEnd_6062094 := by exact prefixLift 6062094
  have htrace : WordTrace (prefixWord ++ tailWord_6062094) baseStart_6062094 baseEnd_6062094 := by
    simpa [prefixWord, tailWord_6062094, baseEnd_6062094] using wordTrace_append hprefix tailTrace_6062094
  have hstable : (prefixWord ++ tailWord_6062094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062094).length < 2 ^ (prefixWord ++ tailWord_6062094).sum := by decide
  have hdescent : baseEnd_6062094 < baseStart_6062094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062101 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_6062101 : Nat := 118140960795 + 6062101 * 2 ^ 59
def prefixEnd_6062101 : Nat := 4983230072969 + 3 ^ 40 * 6062101 * 2
def baseEnd_6062101 : Nat := 3112771589101491735658411

theorem tailTrace_6062101 : CollatzResearch.WordTrace tailWord_6062101 prefixEnd_6062101 3112771589101491735658411 := by
  unfold tailWord_6062101
  simp only [CollatzResearch.WordTrace]
  refine ⟨221102987811050876269522157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147401991874033917513014771 221102987811050876269522157)
  ·
    refine ⟨82913620429144078601070809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221102987811050876269522157 82913620429144078601070809)
    ·
      refine ⟨62185215321858058950803107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82913620429144078601070809 62185215321858058950803107)
      ·
        refine ⟨93277822982787088426204661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62185215321858058950803107 93277822982787088426204661)
        ·
          refine ⟨8744795904636289539956687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93277822982787088426204661 8744795904636289539956687)
          ·
            refine ⟨13117193856954434309935031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8744795904636289539956687 13117193856954434309935031)
            ·
              refine ⟨19675790785431651464902547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13117193856954434309935031 19675790785431651464902547)
              ·
                refine ⟨29513686178147477197353821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19675790785431651464902547 29513686178147477197353821)
                ·
                  refine ⟨11067632316805303949007683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29513686178147477197353821 11067632316805303949007683)
                  ·
                    refine ⟨16601448475207955923511525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11067632316805303949007683 16601448475207955923511525)
                    ·
                      refine ⟨3112771589101491735658411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16601448475207955923511525 3112771589101491735658411)
                      ·
                        rfl

theorem cell23_6062101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_6062101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062101 prefixEnd_6062101 := by exact prefixLift 6062101
  have htrace : WordTrace (prefixWord ++ tailWord_6062101) baseStart_6062101 baseEnd_6062101 := by
    simpa [prefixWord, tailWord_6062101, baseEnd_6062101] using wordTrace_append hprefix tailTrace_6062101
  have hstable : (prefixWord ++ tailWord_6062101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062101).length < 2 ^ (prefixWord ++ tailWord_6062101).sum := by decide
  have hdescent : baseEnd_6062101 < baseStart_6062101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062127 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_6062127 : Nat := 118140960795 + 6062127 * 2 ^ 59
def prefixEnd_6062127 : Nat := 4983230072969 + 3 ^ 40 * 6062127 * 2
def baseEnd_6062127 : Nat := 3112784939598508633933291

theorem tailTrace_6062127 : CollatzResearch.WordTrace tailWord_6062127 prefixEnd_6062127 3112784939598508633933291 := by
  unfold tailWord_6062127
  simp only [CollatzResearch.WordTrace]
  refine ⟨221103936108956682709968635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147402624072637788473312423 221103936108956682709968635)
  ·
    refine ⟨331655904163435024064952953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221103936108956682709968635 331655904163435024064952953)
    ·
      refine ⟨248741928122576268048714715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331655904163435024064952953 248741928122576268048714715)
      ·
        refine ⟨373112892183864402073072073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248741928122576268048714715 373112892183864402073072073)
        ·
          refine ⟨279834669137898301554804055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373112892183864402073072073 279834669137898301554804055)
          ·
            refine ⟨419752003706847452332206083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279834669137898301554804055 419752003706847452332206083)
            ·
              refine ⟨629628005560271178498309125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419752003706847452332206083 629628005560271178498309125)
              ·
                refine ⟨118055251042550845968432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629628005560271178498309125 118055251042550845968432961)
                ·
                  refine ⟨88541438281913134476324721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118055251042550845968432961 88541438281913134476324721)
                  ·
                    refine ⟨66406078711434850857243541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88541438281913134476324721 66406078711434850857243541)
                    ·
                      refine ⟨3112784939598508633933291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66406078711434850857243541 3112784939598508633933291)
                      ·
                        rfl

theorem cell23_6062127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_6062127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062127 prefixEnd_6062127 := by exact prefixLift 6062127
  have htrace : WordTrace (prefixWord ++ tailWord_6062127) baseStart_6062127 baseEnd_6062127 := by
    simpa [prefixWord, tailWord_6062127, baseEnd_6062127] using wordTrace_append hprefix tailTrace_6062127
  have hstable : (prefixWord ++ tailWord_6062127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062127).length < 2 ^ (prefixWord ++ tailWord_6062127).sum := by decide
  have hdescent : baseEnd_6062127 < baseStart_6062127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062151 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_6062151 : Nat := 118140960795 + 6062151 * 2 ^ 59
def prefixEnd_6062151 : Nat := 4983230072969 + 3 ^ 40 * 6062151 * 2
def baseEnd_6062151 : Nat := 3112797263134216540033181

theorem tailTrace_6062151 : CollatzResearch.WordTrace tailWord_6062151 prefixEnd_6062151 3112797263134216540033181 := by
  unfold tailWord_6062151
  simp only [CollatzResearch.WordTrace]
  refine ⟨221104811460869734808842307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147403207640579823205894871 221104811460869734808842307)
  ·
    refine ⟨331657217191304602213263461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221104811460869734808842307 331657217191304602213263461)
    ·
      refine ⟨62185728223369612914986899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331657217191304602213263461 62185728223369612914986899)
      ·
        refine ⟨93278592335054419372480349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62185728223369612914986899 93278592335054419372480349)
        ·
          refine ⟨34979472125645407264680131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93278592335054419372480349 34979472125645407264680131)
          ·
            refine ⟨52469208188468110897020197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34979472125645407264680131 52469208188468110897020197)
            ·
              refine ⟨9837976535337770793191287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52469208188468110897020197 9837976535337770793191287)
              ·
                refine ⟨14756964803006656189786931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837976535337770793191287 14756964803006656189786931)
                ·
                  refine ⟨22135447204509984284680397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14756964803006656189786931 22135447204509984284680397)
                  ·
                    refine ⟨8300792701691244106755149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22135447204509984284680397 8300792701691244106755149)
                    ·
                      refine ⟨3112797263134216540033181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8300792701691244106755149 3112797263134216540033181)
                      ·
                        rfl

theorem cell23_6062151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_6062151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062151 prefixEnd_6062151 := by exact prefixLift 6062151
  have htrace : WordTrace (prefixWord ++ tailWord_6062151) baseStart_6062151 baseEnd_6062151 := by
    simpa [prefixWord, tailWord_6062151, baseEnd_6062151] using wordTrace_append hprefix tailTrace_6062151
  have hstable : (prefixWord ++ tailWord_6062151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062151).length < 2 ^ (prefixWord ++ tailWord_6062151).sum := by decide
  have hdescent : baseEnd_6062151 < baseStart_6062151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062164 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6062164 : Nat := 118140960795 + 6062164 * 2 ^ 59
def prefixEnd_6062164 : Nat := 4983230072969 + 3 ^ 40 * 6062164 * 2
def baseEnd_6062164 : Nat := 3112803938382724989170621

theorem tailTrace_6062164 : CollatzResearch.WordTrace tailWord_6062164 prefixEnd_6062164 3112803938382724989170621 := by
  unfold tailWord_6062164
  simp only [CollatzResearch.WordTrace]
  refine ⟨110552642804911319014532773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147403523739881758686043697 110552642804911319014532773)
  ·
    refine ⟨20728620525920872315224895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110552642804911319014532773 20728620525920872315224895)
    ·
      refine ⟨31092930788881308472837343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20728620525920872315224895 31092930788881308472837343)
      ·
        refine ⟨46639396183321962709256015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31092930788881308472837343 46639396183321962709256015)
        ·
          refine ⟨69959094274982944063884023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46639396183321962709256015 69959094274982944063884023)
          ·
            refine ⟨104938641412474416095826035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69959094274982944063884023 104938641412474416095826035)
            ·
              refine ⟨157407962118711624143739053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104938641412474416095826035 157407962118711624143739053)
              ·
                refine ⟨59027985794516859053902145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157407962118711624143739053 59027985794516859053902145)
                ·
                  refine ⟨44270989345887644290426609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59027985794516859053902145 44270989345887644290426609)
                  ·
                    refine ⟨33203242009415733217819957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44270989345887644290426609 33203242009415733217819957)
                    ·
                      refine ⟨3112803938382724989170621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33203242009415733217819957 3112803938382724989170621)
                      ·
                        rfl

theorem cell23_6062164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6062164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062164 prefixEnd_6062164 := by exact prefixLift 6062164
  have htrace : WordTrace (prefixWord ++ tailWord_6062164) baseStart_6062164 baseEnd_6062164 := by
    simpa [prefixWord, tailWord_6062164, baseEnd_6062164] using wordTrace_append hprefix tailTrace_6062164
  have hstable : (prefixWord ++ tailWord_6062164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062164).length < 2 ^ (prefixWord ++ tailWord_6062164).sum := by decide
  have hdescent : baseEnd_6062164 < baseStart_6062164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062281 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 6, 2]
def baseStart_6062281 : Nat := 118140960795 + 6062281 * 2 ^ 59
def prefixEnd_6062281 : Nat := 4983230072969 + 3 ^ 40 * 6062281 * 2
def baseEnd_6062281 : Nat := 3112864015619301031407583

theorem tailTrace_6062281 : CollatzResearch.WordTrace tailWord_6062281 prefixEnd_6062281 3112864015619301031407583 := by
  unfold tailWord_6062281
  simp only [CollatzResearch.WordTrace]
  refine ⟨221109552950398767011074697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147406368633599178007383131 221109552950398767011074697)
  ·
    refine ⟨165832164712799075258306023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221109552950398767011074697 165832164712799075258306023)
    ·
      refine ⟨248748247069198612887459035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165832164712799075258306023 248748247069198612887459035)
      ·
        refine ⟨373122370603797919331188553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248748247069198612887459035 373122370603797919331188553)
        ·
          refine ⟨279841777952848439498391415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373122370603797919331188553 279841777952848439498391415)
          ·
            refine ⟨419762666929272659247587123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279841777952848439498391415 419762666929272659247587123)
            ·
              refine ⟨629644000393908988871380685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419762666929272659247587123 629644000393908988871380685)
              ·
                refine ⟨236116500147715870826767757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629644000393908988871380685 236116500147715870826767757)
                ·
                  refine ⟨88543687555393451560037909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236116500147715870826767757 88543687555393451560037909)
                  ·
                    refine ⟨4150485354159068041876777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88543687555393451560037909 4150485354159068041876777)
                    ·
                      refine ⟨3112864015619301031407583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150485354159068041876777 3112864015619301031407583)
                      ·
                        rfl

theorem cell23_6062281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6, 2].length) (baseStart_6062281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062281 prefixEnd_6062281 := by exact prefixLift 6062281
  have htrace : WordTrace (prefixWord ++ tailWord_6062281) baseStart_6062281 baseEnd_6062281 := by
    simpa [prefixWord, tailWord_6062281, baseEnd_6062281] using wordTrace_append hprefix tailTrace_6062281
  have hstable : (prefixWord ++ tailWord_6062281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062281).length < 2 ^ (prefixWord ++ tailWord_6062281).sum := by decide
  have hdescent : baseEnd_6062281 < baseStart_6062281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062321 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 6]
def baseStart_6062321 : Nat := 118140960795 + 6062321 * 2 ^ 59
def prefixEnd_6062321 : Nat := 4983230072969 + 3 ^ 40 * 6062321 * 2
def baseEnd_6062321 : Nat := 345876061649497874989711

theorem tailTrace_6062321 : CollatzResearch.WordTrace tailWord_6062321 prefixEnd_6062321 345876061649497874989711 := by
  unfold tailWord_6062321
  simp only [CollatzResearch.WordTrace]
  refine ⟨221111011870253853842530817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147407341246835902561687211 221111011870253853842530817)
  ·
    refine ⟨165833258902690390381898113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221111011870253853842530817 165833258902690390381898113)
    ·
      refine ⟨124374944177017792786423585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165833258902690390381898113 124374944177017792786423585)
      ·
        refine ⟨93281208132763344589817689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124374944177017792786423585 93281208132763344589817689)
        ·
          refine ⟨69960906099572508442363267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93281208132763344589817689 69960906099572508442363267)
          ·
            refine ⟨104941359149358762663544901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69960906099572508442363267 104941359149358762663544901)
            ·
              refine ⟨19676504840504767999414669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104941359149358762663544901 19676504840504767999414669)
              ·
                refine ⟨7378689315189287999780501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19676504840504767999414669 7378689315189287999780501)
                ·
                  refine ⟨345876061649497874989711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7378689315189287999780501 345876061649497874989711)
                  ·
                    rfl

theorem cell23_6062321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_6062321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062321 prefixEnd_6062321 := by exact prefixLift 6062321
  have htrace : WordTrace (prefixWord ++ tailWord_6062321) baseStart_6062321 baseEnd_6062321 := by
    simpa [prefixWord, tailWord_6062321, baseEnd_6062321] using wordTrace_append hprefix tailTrace_6062321
  have hstable : (prefixWord ++ tailWord_6062321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062321).length < 2 ^ (prefixWord ++ tailWord_6062321).sum := by decide
  have hdescent : baseEnd_6062321 < baseStart_6062321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062348 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_6062348 : Nat := 118140960795 + 6062348 * 2 ^ 59
def prefixEnd_6062348 : Nat := 4983230072969 + 3 ^ 40 * 6062348 * 2
def baseEnd_6062348 : Nat := 3112898418823152269269775

theorem tailTrace_6062348 : CollatzResearch.WordTrace tailWord_6062348 prefixEnd_6062348 3112898418823152269269775 := by
  unfold tailWord_6062348
  simp only [CollatzResearch.WordTrace]
  refine ⟨110555998320578018726881849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147407997760770691635842465 110555998320578018726881849)
  ·
    refine ⟨82916998740433514045161387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110555998320578018726881849 82916998740433514045161387)
    ·
      refine ⟨124375498110650271067742081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82916998740433514045161387 124375498110650271067742081)
      ·
        refine ⟨93281623582987703300806561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124375498110650271067742081 93281623582987703300806561)
        ·
          refine ⟨69961217687240777475604921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93281623582987703300806561 69961217687240777475604921)
          ·
            refine ⟨52470913265430583106703691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69961217687240777475604921 52470913265430583106703691)
            ·
              refine ⟨78706369898145874660055537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52470913265430583106703691 78706369898145874660055537)
              ·
                refine ⟨59029777423609405995041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78706369898145874660055537 59029777423609405995041653)
                ·
                  refine ⟨5534041633463381812035155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59029777423609405995041653 5534041633463381812035155)
                  ·
                    refine ⟨8301062450195072718052733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534041633463381812035155 8301062450195072718052733)
                    ·
                      refine ⟨3112898418823152269269775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301062450195072718052733 3112898418823152269269775)
                      ·
                        rfl

theorem cell23_6062348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_6062348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062348 prefixEnd_6062348 := by exact prefixLift 6062348
  have htrace : WordTrace (prefixWord ++ tailWord_6062348) baseStart_6062348 baseEnd_6062348 := by
    simpa [prefixWord, tailWord_6062348, baseEnd_6062348] using wordTrace_append hprefix tailTrace_6062348
  have hstable : (prefixWord ++ tailWord_6062348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062348).length < 2 ^ (prefixWord ++ tailWord_6062348).sum := by decide
  have hdescent : baseEnd_6062348 < baseStart_6062348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062385 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_6062385 : Nat := 118140960795 + 6062385 * 2 ^ 59
def prefixEnd_6062385 : Nat := 4983230072969 + 3 ^ 40 * 6062385 * 2
def baseEnd_6062385 : Nat := 1037639139202456208169035

theorem tailTrace_6062385 : CollatzResearch.WordTrace tailWord_6062385 prefixEnd_6062385 1037639139202456208169035 := by
  unfold tailWord_6062385
  simp only [CollatzResearch.WordTrace]
  refine ⟨221113346142021992772860609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147408897428014661848573739 221113346142021992772860609)
  ·
    refine ⟨165835009606516494579645457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221113346142021992772860609 165835009606516494579645457)
    ·
      refine ⟨124376257204887370934734093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165835009606516494579645457 124376257204887370934734093)
      ·
        refine ⟨46641096451832764100525285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124376257204887370934734093 46641096451832764100525285)
        ·
          refine ⟨8745205584718643268848491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46641096451832764100525285 8745205584718643268848491)
          ·
            refine ⟨13117808377077964903272737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745205584718643268848491 13117808377077964903272737)
            ·
              refine ⟨9838356282808473677454553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13117808377077964903272737 9838356282808473677454553)
              ·
                refine ⟨7378767212106355258090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9838356282808473677454553 7378767212106355258090915)
                ·
                  refine ⟨11068150818159532887136373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378767212106355258090915 11068150818159532887136373)
                  ·
                    refine ⟨1037639139202456208169035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11068150818159532887136373 1037639139202456208169035)
                    ·
                      rfl

theorem cell23_6062385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_6062385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062385 prefixEnd_6062385 := by exact prefixLift 6062385
  have htrace : WordTrace (prefixWord ++ tailWord_6062385) baseStart_6062385 baseEnd_6062385 := by
    simpa [prefixWord, tailWord_6062385, baseEnd_6062385] using wordTrace_append hprefix tailTrace_6062385
  have hstable : (prefixWord ++ tailWord_6062385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062385).length < 2 ^ (prefixWord ++ tailWord_6062385).sum := by decide
  have hdescent : baseEnd_6062385 < baseStart_6062385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062391 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_6062391 : Nat := 118140960795 + 6062391 * 2 ^ 59
def prefixEnd_6062391 : Nat := 4983230072969 + 3 ^ 40 * 6062391 * 2
def baseEnd_6062391 : Nat := 3112920498491295601032077

theorem tailTrace_6062391 : CollatzResearch.WordTrace tailWord_6062391 prefixEnd_6062391 3112920498491295601032077 := by
  unfold tailWord_6062391
  simp only [CollatzResearch.WordTrace]
  refine ⟨221113564980000255797579027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147409043320000170531719351 221113564980000255797579027)
  ·
    refine ⟨331670347470000383696368541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221113564980000255797579027 331670347470000383696368541)
    ·
      refine ⟨124376380301250143886138203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331670347470000383696368541 124376380301250143886138203)
      ·
        refine ⟨186564570451875215829207305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124376380301250143886138203 186564570451875215829207305)
        ·
          refine ⟨139923427838906411871905479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186564570451875215829207305 139923427838906411871905479)
          ·
            refine ⟨209885141758359617807858219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139923427838906411871905479 209885141758359617807858219)
            ·
              refine ⟨314827712637539426711787329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209885141758359617807858219 314827712637539426711787329)
              ·
                refine ⟨236120784478154570033840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314827712637539426711787329 236120784478154570033840497)
                ·
                  refine ⟨177090588358615927525380373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236120784478154570033840497 177090588358615927525380373)
                  ·
                    refine ⟨8301121329310121602752205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177090588358615927525380373 8301121329310121602752205)
                    ·
                      refine ⟨3112920498491295601032077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301121329310121602752205 3112920498491295601032077)
                      ·
                        rfl

theorem cell23_6062391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_6062391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062391 prefixEnd_6062391 := by exact prefixLift 6062391
  have htrace : WordTrace (prefixWord ++ tailWord_6062391) baseStart_6062391 baseEnd_6062391 := by
    simpa [prefixWord, tailWord_6062391, baseEnd_6062391] using wordTrace_append hprefix tailTrace_6062391
  have hstable : (prefixWord ++ tailWord_6062391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062391).length < 2 ^ (prefixWord ++ tailWord_6062391).sum := by decide
  have hdescent : baseEnd_6062391 < baseStart_6062391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062442 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6062442 : Nat := 118140960795 + 6062442 * 2 ^ 59
def prefixEnd_6062442 : Nat := 4983230072969 + 3 ^ 40 * 6062442 * 2
def baseEnd_6062442 : Nat := 3112946686004674901494343

theorem tailTrace_6062442 : CollatzResearch.WordTrace tailWord_6062442 prefixEnd_6062442 3112946686004674901494343 := by
  unfold tailWord_6062442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55278856275703872876921395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147410283401876994338457053 55278856275703872876921395)
  ·
    refine ⟨82918284413555809315382093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55278856275703872876921395 82918284413555809315382093)
    ·
      refine ⟨31094356655083428493268285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82918284413555809315382093 31094356655083428493268285)
      ·
        refine ⟨11660383745656285684975607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31094356655083428493268285 11660383745656285684975607)
        ·
          refine ⟨17490575618484428527463411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11660383745656285684975607 17490575618484428527463411)
          ·
            refine ⟨26235863427726642791195117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17490575618484428527463411 26235863427726642791195117)
            ·
              refine ⟨9838448785397491046698169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26235863427726642791195117 9838448785397491046698169)
              ·
                refine ⟨7378836589048118285023627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9838448785397491046698169 7378836589048118285023627)
                ·
                  refine ⟨11068254883572177427535441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378836589048118285023627 11068254883572177427535441)
                  ·
                    refine ⟨8301191162679133070651581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11068254883572177427535441 8301191162679133070651581)
                    ·
                      refine ⟨3112946686004674901494343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301191162679133070651581 3112946686004674901494343)
                      ·
                        rfl

theorem cell23_6062442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6062442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062442 prefixEnd_6062442 := by exact prefixLift 6062442
  have htrace : WordTrace (prefixWord ++ tailWord_6062442) baseStart_6062442 baseEnd_6062442 := by
    simpa [prefixWord, tailWord_6062442, baseEnd_6062442] using wordTrace_append hprefix tailTrace_6062442
  have hstable : (prefixWord ++ tailWord_6062442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062442).length < 2 ^ (prefixWord ++ tailWord_6062442).sum := by decide
  have hdescent : baseEnd_6062442 < baseStart_6062442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062472 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_6062472 : Nat := 118140960795 + 6062472 * 2 ^ 59
def prefixEnd_6062472 : Nat := 4983230072969 + 3 ^ 40 * 6062472 * 2
def baseEnd_6062472 : Nat := 3112962090424309784119205

theorem tailTrace_6062472 : CollatzResearch.WordTrace tailWord_6062472 prefixEnd_6062472 3112962090424309784119205 := by
  unfold tailWord_6062472
  simp only [CollatzResearch.WordTrace]
  refine ⟨110558259646353403315638835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147411012861804537754185113 110558259646353403315638835)
  ·
    refine ⟨165837389469530104973458253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110558259646353403315638835 165837389469530104973458253)
    ·
      refine ⟨62189021051073789365046845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165837389469530104973458253 62189021051073789365046845)
      ·
        refine ⟨23320882894152671011892567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62189021051073789365046845 23320882894152671011892567)
        ·
          refine ⟨34981324341229006517838851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23320882894152671011892567 34981324341229006517838851)
          ·
            refine ⟨52471986511843509776758277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34981324341229006517838851 52471986511843509776758277)
            ·
              refine ⟨9838497470970658083142177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52471986511843509776758277 9838497470970658083142177)
              ·
                refine ⟨7378873103227993562356633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9838497470970658083142177 7378873103227993562356633)
                ·
                  refine ⟨5534154827420995171767475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7378873103227993562356633 5534154827420995171767475)
                  ·
                    refine ⟨8301232241131492757651213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534154827420995171767475 8301232241131492757651213)
                    ·
                      refine ⟨3112962090424309784119205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301232241131492757651213 3112962090424309784119205)
                      ·
                        rfl

theorem cell23_6062472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_6062472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062472 prefixEnd_6062472 := by exact prefixLift 6062472
  have htrace : WordTrace (prefixWord ++ tailWord_6062472) baseStart_6062472 baseEnd_6062472 := by
    simpa [prefixWord, tailWord_6062472, baseEnd_6062472] using wordTrace_append hprefix tailTrace_6062472
  have hstable : (prefixWord ++ tailWord_6062472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062472).length < 2 ^ (prefixWord ++ tailWord_6062472).sum := by decide
  have hdescent : baseEnd_6062472 < baseStart_6062472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062486 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6062486 : Nat := 118140960795 + 6062486 * 2 ^ 59
def prefixEnd_6062486 : Nat := 4983230072969 + 3 ^ 40 * 6062486 * 2
def baseEnd_6062486 : Nat := 3112969279153472729344141

theorem tailTrace_6062486 : CollatzResearch.WordTrace tailWord_6062486 prefixEnd_6062486 3112969279153472729344141 := by
  unfold tailWord_6062486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819814369666005438892957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147411353276437391348191541 13819814369666005438892957)
  ·
    refine ⟨5182430388624752039584859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13819814369666005438892957 5182430388624752039584859)
    ·
      refine ⟨7773645582937128059377289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182430388624752039584859 7773645582937128059377289)
      ·
        refine ⟨5830234187202846044532967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7773645582937128059377289 5830234187202846044532967)
        ·
          refine ⟨8745351280804269066799451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5830234187202846044532967 8745351280804269066799451)
          ·
            refine ⟨13118026921206403600199177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8745351280804269066799451 13118026921206403600199177)
            ·
              refine ⟨9838520190904802700149383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13118026921206403600199177 9838520190904802700149383)
              ·
                refine ⟨14757780286357204050224075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9838520190904802700149383 14757780286357204050224075)
                ·
                  refine ⟨22136670429535806075336113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14757780286357204050224075 22136670429535806075336113)
                  ·
                    refine ⟨16602502822151854556502085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22136670429535806075336113 16602502822151854556502085)
                    ·
                      refine ⟨3112969279153472729344141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16602502822151854556502085 3112969279153472729344141)
                      ·
                        rfl

theorem cell23_6062486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6062486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062486 prefixEnd_6062486 := by exact prefixLift 6062486
  have htrace : WordTrace (prefixWord ++ tailWord_6062486) baseStart_6062486 baseEnd_6062486 := by
    simpa [prefixWord, tailWord_6062486, baseEnd_6062486] using wordTrace_append hprefix tailTrace_6062486
  have hstable : (prefixWord ++ tailWord_6062486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062486).length < 2 ^ (prefixWord ++ tailWord_6062486).sum := by decide
  have hdescent : baseEnd_6062486 < baseStart_6062486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062488 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_6062488 : Nat := 118140960795 + 6062488 * 2 ^ 59
def prefixEnd_6062488 : Nat := 4983230072969 + 3 ^ 40 * 6062488 * 2
def baseEnd_6062488 : Nat := 1037656768704927240506377

theorem tailTrace_6062488 : CollatzResearch.WordTrace tailWord_6062488 prefixEnd_6062488 1037656768704927240506377 := by
  unfold tailWord_6062488
  simp only [CollatzResearch.WordTrace]
  refine ⟨110558551430324420681930059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147411401907099227575906745 110558551430324420681930059)
  ·
    refine ⟨165837827145486631022895089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110558551430324420681930059 165837827145486631022895089)
    ·
      refine ⟨124378370359114973267171317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165837827145486631022895089 124378370359114973267171317)
      ·
        refine ⟨11660472221167028743797311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124378370359114973267171317 11660472221167028743797311)
        ·
          refine ⟨17490708331750543115695967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11660472221167028743797311 17490708331750543115695967)
          ·
            refine ⟨26236062497625814673543951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17490708331750543115695967 26236062497625814673543951)
            ·
              refine ⟨39354093746438722010315927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26236062497625814673543951 39354093746438722010315927)
              ·
                refine ⟨59031140619658083015473891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39354093746438722010315927 59031140619658083015473891)
                ·
                  refine ⟨88546710929487124523210837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59031140619658083015473891 88546710929487124523210837)
                  ·
                    refine ⟨1037656768704927240506377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88546710929487124523210837 1037656768704927240506377)
                    ·
                      rfl

theorem cell23_6062488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_6062488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062488 prefixEnd_6062488 := by exact prefixLift 6062488
  have htrace : WordTrace (prefixWord ++ tailWord_6062488) baseStart_6062488 baseEnd_6062488 := by
    simpa [prefixWord, tailWord_6062488, baseEnd_6062488] using wordTrace_append hprefix tailTrace_6062488
  have hstable : (prefixWord ++ tailWord_6062488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062488).length < 2 ^ (prefixWord ++ tailWord_6062488).sum := by decide
  have hdescent : baseEnd_6062488 < baseStart_6062488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062511 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_6062511 : Nat := 118140960795 + 6062511 * 2 ^ 59
def prefixEnd_6062511 : Nat := 4983230072969 + 3 ^ 40 * 6062511 * 2
def baseEnd_6062511 : Nat := 3112982116169835131531525

theorem tailTrace_6062511 : CollatzResearch.WordTrace tailWord_6062511 prefixEnd_6062511 3112982116169835131531525 := by
  unfold tailWord_6062511
  simp only [CollatzResearch.WordTrace]
  refine ⟨221117941739565516291947387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147411961159710344194631591 221117941739565516291947387)
  ·
    refine ⟨331676912609348274437921081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221117941739565516291947387 331676912609348274437921081)
    ·
      refine ⟨248757684457011205828440811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331676912609348274437921081 248757684457011205828440811)
      ·
        refine ⟨373136526685516808742661217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248757684457011205828440811 373136526685516808742661217)
        ·
          refine ⟨279852395014137606556995913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373136526685516808742661217 279852395014137606556995913)
          ·
            refine ⟨209889296260603204917746935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279852395014137606556995913 209889296260603204917746935)
            ·
              refine ⟨314833944390904807376620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209889296260603204917746935 314833944390904807376620403)
              ·
                refine ⟨472250916586357211064930605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314833944390904807376620403 472250916586357211064930605)
                ·
                  refine ⟨177094093719883954149348977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472250916586357211064930605 177094093719883954149348977)
                  ·
                    refine ⟨132820570289912965612011733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177094093719883954149348977 132820570289912965612011733)
                    ·
                      refine ⟨3112982116169835131531525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132820570289912965612011733 3112982116169835131531525)
                      ·
                        rfl

theorem cell23_6062511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_6062511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062511 prefixEnd_6062511 := by exact prefixLift 6062511
  have htrace : WordTrace (prefixWord ++ tailWord_6062511) baseStart_6062511 baseEnd_6062511 := by
    simpa [prefixWord, tailWord_6062511, baseEnd_6062511] using wordTrace_append hprefix tailTrace_6062511
  have hstable : (prefixWord ++ tailWord_6062511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062511).length < 2 ^ (prefixWord ++ tailWord_6062511).sum := by decide
  have hdescent : baseEnd_6062511 < baseStart_6062511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062535 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 5]
def baseStart_6062535 : Nat := 118140960795 + 6062535 * 2 ^ 59
def prefixEnd_6062535 : Nat := 4983230072969 + 3 ^ 40 * 6062535 * 2
def baseEnd_6062535 : Nat := 345888271078393670847935

theorem tailTrace_6062535 : CollatzResearch.WordTrace tailWord_6062535 prefixEnd_6062535 345888271078393670847935 := by
  unfold tailWord_6062535
  simp only [CollatzResearch.WordTrace]
  refine ⟨221118817091478568390821059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147412544727652378927214039 221118817091478568390821059)
  ·
    refine ⟨331678225637217852586231589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221118817091478568390821059 331678225637217852586231589)
    ·
      refine ⟨62189667306978347359918423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331678225637217852586231589 62189667306978347359918423)
      ·
        refine ⟨93284500960467521039877635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62189667306978347359918423 93284500960467521039877635)
        ·
          refine ⟨139926751440701281559816453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93284500960467521039877635 139926751440701281559816453)
          ·
            refine ⟨26236265895131490292465585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139926751440701281559816453 26236265895131490292465585)
            ·
              refine ⟨19677199421348617719349189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26236265895131490292465585 19677199421348617719349189)
              ·
                refine ⟨3689474891502865822377973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19677199421348617719349189 3689474891502865822377973)
                ·
                  refine ⟨345888271078393670847935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3689474891502865822377973 345888271078393670847935)
                  ·
                    rfl

theorem cell23_6062535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 5].length) (baseStart_6062535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062535 prefixEnd_6062535 := by exact prefixLift 6062535
  have htrace : WordTrace (prefixWord ++ tailWord_6062535) baseStart_6062535 baseEnd_6062535 := by
    simpa [prefixWord, tailWord_6062535, baseEnd_6062535] using wordTrace_append hprefix tailTrace_6062535
  have hstable : (prefixWord ++ tailWord_6062535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062535).length < 2 ^ (prefixWord ++ tailWord_6062535).sum := by decide
  have hdescent : baseEnd_6062535 < baseStart_6062535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062546 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6062546 : Nat := 118140960795 + 6062546 * 2 ^ 59
def prefixEnd_6062546 : Nat := 4983230072969 + 3 ^ 40 * 6062546 * 2
def baseEnd_6062546 : Nat := 3113000087992742494593865

theorem tailTrace_6062546 : CollatzResearch.WordTrace tailWord_6062546 prefixEnd_6062546 3113000087992742494593865 := by
  unfold tailWord_6062546
  simp only [CollatzResearch.WordTrace]
  refine ⟨55279804573609679317367873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147412812196292478179647661 55279804573609679317367873)
  ·
    refine ⟨41459853430207259488025905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55279804573609679317367873 41459853430207259488025905)
    ·
      refine ⟨31094890072655444616019429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41459853430207259488025905 31094890072655444616019429)
      ·
        refine ⟨5830291888622895865503643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31094890072655444616019429 5830291888622895865503643)
        ·
          refine ⟨8745437832934343798255465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5830291888622895865503643 8745437832934343798255465)
          ·
            refine ⟨6559078374700757848691599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8745437832934343798255465 6559078374700757848691599)
            ·
              refine ⟨9838617562051136773037399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6559078374700757848691599 9838617562051136773037399)
              ·
                refine ⟨14757926343076705159556099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9838617562051136773037399 14757926343076705159556099)
                ·
                  refine ⟨22136889514615057739334149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14757926343076705159556099 22136889514615057739334149)
                  ·
                    refine ⟨4150666783990323326125153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22136889514615057739334149 4150666783990323326125153)
                    ·
                      refine ⟨3113000087992742494593865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150666783990323326125153 3113000087992742494593865)
                      ·
                        rfl

theorem cell23_6062546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6062546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062546 prefixEnd_6062546 := by exact prefixLift 6062546
  have htrace : WordTrace (prefixWord ++ tailWord_6062546) baseStart_6062546 baseEnd_6062546 := by
    simpa [prefixWord, tailWord_6062546, baseEnd_6062546] using wordTrace_append hprefix tailTrace_6062546
  have hstable : (prefixWord ++ tailWord_6062546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062546).length < 2 ^ (prefixWord ++ tailWord_6062546).sum := by decide
  have hdescent : baseEnd_6062546 < baseStart_6062546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062585 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 4, 2]
def baseStart_6062585 : Nat := 118140960795 + 6062585 * 2 ^ 59
def prefixEnd_6062585 : Nat := 4983230072969 + 3 ^ 40 * 6062585 * 2
def baseEnd_6062585 : Nat := 3113020113738267842006185

theorem tailTrace_6062585 : CollatzResearch.WordTrace tailWord_6062585 prefixEnd_6062585 3113020113738267842006185 := by
  unfold tailWord_6062585
  simp only [CollatzResearch.WordTrace]
  refine ⟨221120640741297426930141209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147413760494198284620094139 221120640741297426930141209)
  ·
    refine ⟨165840480555973070197605907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221120640741297426930141209 165840480555973070197605907)
    ·
      refine ⟨248760720833959605296408861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165840480555973070197605907 248760720833959605296408861)
      ·
        refine ⟨93285270312734851986153323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248760720833959605296408861 93285270312734851986153323)
        ·
          refine ⟨139927905469102277979229985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93285270312734851986153323 139927905469102277979229985)
          ·
            refine ⟨104945929101826708484422489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139927905469102277979229985 104945929101826708484422489)
            ·
              refine ⟨78709446826370031363316867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104945929101826708484422489 78709446826370031363316867)
              ·
                refine ⟨118064170239555047044975301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78709446826370031363316867 118064170239555047044975301)
                ·
                  refine ⟨22137031919916571320932869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118064170239555047044975301 22137031919916571320932869)
                  ·
                    refine ⟨4150693484984357122674913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22137031919916571320932869 4150693484984357122674913)
                    ·
                      refine ⟨3113020113738267842006185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4150693484984357122674913 3113020113738267842006185)
                      ·
                        rfl

theorem cell23_6062585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_6062585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062585 prefixEnd_6062585 := by exact prefixLift 6062585
  have htrace : WordTrace (prefixWord ++ tailWord_6062585) baseStart_6062585 baseEnd_6062585 := by
    simpa [prefixWord, tailWord_6062585, baseEnd_6062585] using wordTrace_append hprefix tailTrace_6062585
  have hstable : (prefixWord ++ tailWord_6062585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062585).length < 2 ^ (prefixWord ++ tailWord_6062585).sum := by decide
  have hdescent : baseEnd_6062585 < baseStart_6062585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062646 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6062646 : Nat := 118140960795 + 6062646 * 2 ^ 59
def prefixEnd_6062646 : Nat := 4983230072969 + 3 ^ 40 * 6062646 * 2
def baseEnd_6062646 : Nat := 1037683812019397367781135

theorem tailTrace_6062646 : CollatzResearch.WordTrace tailWord_6062646 prefixEnd_6062646 1037683812019397367781135 := by
  unfold tailWord_6062646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820179099629777146756987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147415243729384289565407861 13820179099629777146756987)
  ·
    refine ⟨20730268649444665720135481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13820179099629777146756987 20730268649444665720135481)
    ·
      refine ⟨15547701487083499290101611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20730268649444665720135481 15547701487083499290101611)
      ·
        refine ⟨23321552230625248935152417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15547701487083499290101611 23321552230625248935152417)
        ·
          refine ⟨17491164172968936701364313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23321552230625248935152417 17491164172968936701364313)
          ·
            refine ⟨13118373129726702526023235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17491164172968936701364313 13118373129726702526023235)
            ·
              refine ⟨19677559694590053789034853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13118373129726702526023235 19677559694590053789034853)
              ·
                refine ⟨3689542442735635085444035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19677559694590053789034853 3689542442735635085444035)
                ·
                  refine ⟨5534313664103452628166053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3689542442735635085444035 5534313664103452628166053)
                  ·
                    refine ⟨1037683812019397367781135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5534313664103452628166053 1037683812019397367781135)
                    ·
                      rfl

theorem cell23_6062646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6062646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062646 prefixEnd_6062646 := by exact prefixLift 6062646
  have htrace : WordTrace (prefixWord ++ tailWord_6062646) baseStart_6062646 baseEnd_6062646 := by
    simpa [prefixWord, tailWord_6062646, baseEnd_6062646] using wordTrace_append hprefix tailTrace_6062646
  have hstable : (prefixWord ++ tailWord_6062646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062646).length < 2 ^ (prefixWord ++ tailWord_6062646).sum := by decide
  have hdescent : baseEnd_6062646 < baseStart_6062646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062669 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6062669 : Nat := 118140960795 + 6062669 * 2 ^ 59
def prefixEnd_6062669 : Nat := 4983230072969 + 3 ^ 40 * 6062669 * 2
def baseEnd_6062669 : Nat := 3113063246113245513355799

theorem tailTrace_6062669 : CollatzResearch.WordTrace tailWord_6062669 prefixEnd_6062669 3113063246113245513355799 := by
  unfold tailWord_6062669
  simp only [CollatzResearch.WordTrace]
  refine ⟨221123704472993109276199061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147415802981995406184132707 221123704472993109276199061)
  ·
    refine ⟨10365173647171551997321831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221123704472993109276199061 10365173647171551997321831)
    ·
      refine ⟨15547760470757327995982747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10365173647171551997321831 15547760470757327995982747)
      ·
        refine ⟨23321640706135991993974121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15547760470757327995982747 23321640706135991993974121)
        ·
          refine ⟨17491230529601993995480591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23321640706135991993974121 17491230529601993995480591)
          ·
            refine ⟨26236845794402990993220887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17491230529601993995480591 26236845794402990993220887)
            ·
              refine ⟨39355268691604486489831331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26236845794402990993220887 39355268691604486489831331)
              ·
                refine ⟨59032903037406729734746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39355268691604486489831331 59032903037406729734746997)
                ·
                  refine ⟨5534334659756880912632531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59032903037406729734746997 5534334659756880912632531)
                  ·
                    refine ⟨8301501989635321368948797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5534334659756880912632531 8301501989635321368948797)
                    ·
                      refine ⟨3113063246113245513355799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8301501989635321368948797 3113063246113245513355799)
                      ·
                        rfl

theorem cell23_6062669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6062669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062669 prefixEnd_6062669 := by exact prefixLift 6062669
  have htrace : WordTrace (prefixWord ++ tailWord_6062669) baseStart_6062669 baseEnd_6062669 := by
    simpa [prefixWord, tailWord_6062669, baseEnd_6062669] using wordTrace_append hprefix tailTrace_6062669
  have hstable : (prefixWord ++ tailWord_6062669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062669).length < 2 ^ (prefixWord ++ tailWord_6062669).sum := by decide
  have hdescent : baseEnd_6062669 < baseStart_6062669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062689 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_6062689 : Nat := 118140960795 + 6062689 * 2 ^ 59
def prefixEnd_6062689 : Nat := 4983230072969 + 3 ^ 40 * 6062689 * 2
def baseEnd_6062689 : Nat := 1037691171908778478368569

theorem tailTrace_6062689 : CollatzResearch.WordTrace tailWord_6062689 prefixEnd_6062689 1037691171908778478368569 := by
  unfold tailWord_6062689
  simp only [CollatzResearch.WordTrace]
  refine ⟨221124433932920652691927121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147416289288613768461284747 221124433932920652691927121)
  ·
    refine ⟨165843325449690489518945341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221124433932920652691927121 165843325449690489518945341)
    ·
      refine ⟨62191247043633933569604503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165843325449690489518945341 62191247043633933569604503)
      ·
        refine ⟨93286870565450900354406755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62191247043633933569604503 93286870565450900354406755)
        ·
          refine ⟨139930305848176350531610133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93286870565450900354406755 139930305848176350531610133)
          ·
            refine ⟨6559233086633266431169225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139930305848176350531610133 6559233086633266431169225)
            ·
              refine ⟨4919424814974949823376919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6559233086633266431169225 4919424814974949823376919)
              ·
                refine ⟨7379137222462424735065379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919424814974949823376919 7379137222462424735065379)
                ·
                  refine ⟨11068705833693637102598069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379137222462424735065379 11068705833693637102598069)
                  ·
                    refine ⟨1037691171908778478368569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11068705833693637102598069 1037691171908778478368569)
                    ·
                      rfl

theorem cell23_6062689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_6062689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062689 prefixEnd_6062689 := by exact prefixLift 6062689
  have htrace : WordTrace (prefixWord ++ tailWord_6062689) baseStart_6062689 baseEnd_6062689 := by
    simpa [prefixWord, tailWord_6062689, baseEnd_6062689] using wordTrace_append hprefix tailTrace_6062689
  have hstable : (prefixWord ++ tailWord_6062689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062689).length < 2 ^ (prefixWord ++ tailWord_6062689).sum := by decide
  have hdescent : baseEnd_6062689 < baseStart_6062689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6062692 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_6062692 : Nat := 118140960795 + 6062692 * 2 ^ 59
def prefixEnd_6062692 : Nat := 4983230072969 + 3 ^ 40 * 6062692 * 2
def baseEnd_6062692 : Nat := 3113075056168298923368193

theorem tailTrace_6062692 : CollatzResearch.WordTrace tailWord_6062692 prefixEnd_6062692 3113075056168298923368193 := by
  unfold tailWord_6062692
  simp only [CollatzResearch.WordTrace]
  refine ⟨110562271675954892102143165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147416362234606522802857553 110562271675954892102143165)
  ·
    refine ⟨41460851878483084538303687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110562271675954892102143165 41460851878483084538303687)
    ·
      refine ⟨62191277817724626807455531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41460851878483084538303687 62191277817724626807455531)
      ·
        refine ⟨93286916726586940211183297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62191277817724626807455531 93286916726586940211183297)
        ·
          refine ⟨69965187544940205158387473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93286916726586940211183297 69965187544940205158387473)
          ·
            refine ⟨52473890658705153868790605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69965187544940205158387473 52473890658705153868790605)
            ·
              refine ⟨19677708997014432700796477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52473890658705153868790605 19677708997014432700796477)
              ·
                refine ⟨7379140873880412262798679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19677708997014432700796477 7379140873880412262798679)
                ·
                  refine ⟨11068711310820618394198019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7379140873880412262798679 11068711310820618394198019)
                  ·
                    refine ⟨16603066966230927591297029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11068711310820618394198019 16603066966230927591297029)
                    ·
                      refine ⟨3113075056168298923368193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16603066966230927591297029 3113075056168298923368193)
                      ·
                        rfl

theorem cell23_6062692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_6062692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6062692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6062692 prefixEnd_6062692 := by exact prefixLift 6062692
  have htrace : WordTrace (prefixWord ++ tailWord_6062692) baseStart_6062692 baseEnd_6062692 := by
    simpa [prefixWord, tailWord_6062692, baseEnd_6062692] using wordTrace_append hprefix tailTrace_6062692
  have hstable : (prefixWord ++ tailWord_6062692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6062692).length < 2 ^ (prefixWord ++ tailWord_6062692).sum := by decide
  have hdescent : baseEnd_6062692 < baseStart_6062692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6062692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
