import V185TrunkScan22Chunk032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_296161 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_296161 : Nat := 118140960795 + 296161 * 2 ^ 59
def prefixEnd_296161 : Nat := 4983230072969 + 3 ^ 40 * 296161 * 2
def baseEnd_296161 : Nat := 101381962744214001616991

theorem tailTrace_296161 : CollatzResearch.WordTrace tailWord_296161 prefixEnd_296161 101381962744214001616991 := by
  unfold tailWord_296161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801879080066752117008337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7201252720044501411338891 10801879080066752117008337)
  ·
    refine ⟨8101409310050064087756253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10801879080066752117008337 8101409310050064087756253)
    ·
      refine ⟨3038028491268774032908595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8101409310050064087756253 3038028491268774032908595)
      ·
        refine ⟨4557042736903161049362893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038028491268774032908595 4557042736903161049362893)
        ·
          refine ⟨1708891026338685393511085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4557042736903161049362893 1708891026338685393511085)
          ·
            refine ⟨640834134877007022566657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1708891026338685393511085 640834134877007022566657)
            ·
              refine ⟨480625601157755266924993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640834134877007022566657 480625601157755266924993)
              ·
                refine ⟨360469200868316450193745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480625601157755266924993 360469200868316450193745)
                ·
                  refine ⟨270351900651237337645309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360469200868316450193745 270351900651237337645309)
                  ·
                    refine ⟨101381962744214001616991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270351900651237337645309 101381962744214001616991)
                    ·
                      rfl

theorem cell22_296161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_296161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296161 prefixEnd_296161 := by exact prefixLift 296161
  have htrace : WordTrace (prefixWord ++ tailWord_296161) baseStart_296161 baseEnd_296161 := by
    simpa [prefixWord, tailWord_296161, baseEnd_296161] using wordTrace_append hprefix tailTrace_296161
  have hstable : (prefixWord ++ tailWord_296161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296161).length < 2 ^ (prefixWord ++ tailWord_296161).sum := by decide
  have hdescent : baseEnd_296161 < baseStart_296161 := by decide
  rcases family_descends (prefixWord ++ tailWord_296161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296202 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_296202 : Nat := 118140960795 + 296202 * 2 ^ 59
def prefixEnd_296202 : Nat := 4983230072969 + 3 ^ 40 * 296202 * 2
def baseEnd_296202 : Nat := 33798665960701187113955

theorem tailTrace_296202 : CollatzResearch.WordTrace tailWord_296202 prefixEnd_296202 33798665960701187113955 := by
  unfold tailWord_296202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700843618229554029812715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7202249648612144079500573 2700843618229554029812715)
  ·
    refine ⟨4051265427344331044719073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700843618229554029812715 4051265427344331044719073)
    ·
      refine ⟨3038449070508248283539305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051265427344331044719073 3038449070508248283539305)
      ·
        refine ⟨2278836802881186212654479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3038449070508248283539305 2278836802881186212654479)
        ·
          refine ⟨3418255204321779318981719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278836802881186212654479 3418255204321779318981719)
          ·
            refine ⟨5127382806482668978472579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418255204321779318981719 5127382806482668978472579)
            ·
              refine ⟨7691074209724003467708869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127382806482668978472579 7691074209724003467708869)
              ·
                refine ⟨1442076414323250650195413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7691074209724003467708869 1442076414323250650195413)
                ·
                  refine ⟨33798665960701187113955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1442076414323250650195413 33798665960701187113955)
                  ·
                    rfl

theorem cell22_296202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_296202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296202 prefixEnd_296202 := by exact prefixLift 296202
  have htrace : WordTrace (prefixWord ++ tailWord_296202) baseStart_296202 baseEnd_296202 := by
    simpa [prefixWord, tailWord_296202, baseEnd_296202] using wordTrace_append hprefix tailTrace_296202
  have hstable : (prefixWord ++ tailWord_296202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296202).length < 2 ^ (prefixWord ++ tailWord_296202).sum := by decide
  have hdescent : baseEnd_296202 < baseStart_296202 := by decide
  rcases family_descends (prefixWord ++ tailWord_296202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296369 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_296369 : Nat := 118140960795 + 296369 * 2 ^ 59
def prefixEnd_296369 : Nat := 4983230072969 + 3 ^ 40 * 296369 * 2
def baseEnd_296369 : Nat := 101453165394970792416353

theorem tailTrace_296369 : CollatzResearch.WordTrace tailWord_296369 prefixEnd_296369 101453165394970792416353 := by
  unfold tailWord_296369
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809465463313203640580161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7206310308875469093720107 10809465463313203640580161)
  ·
    refine ⟨8107099097484902730435121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10809465463313203640580161 8107099097484902730435121)
    ·
      refine ⟨6080324323113677047826341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8107099097484902730435121 6080324323113677047826341)
      ·
        refine ⟨1140060810583814446467439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6080324323113677047826341 1140060810583814446467439)
        ·
          refine ⟨1710091215875721669701159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140060810583814446467439 1710091215875721669701159)
          ·
            refine ⟨2565136823813582504551739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710091215875721669701159 2565136823813582504551739)
            ·
              refine ⟨3847705235720373756827609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565136823813582504551739 3847705235720373756827609)
              ·
                refine ⟨2885778926790280317620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847705235720373756827609 2885778926790280317620707)
                ·
                  refine ⟨4328668390185420476431061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885778926790280317620707 4328668390185420476431061)
                  ·
                    refine ⟨101453165394970792416353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4328668390185420476431061 101453165394970792416353)
                    ·
                      rfl

theorem cell22_296369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_296369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296369 prefixEnd_296369 := by exact prefixLift 296369
  have htrace : WordTrace (prefixWord ++ tailWord_296369) baseStart_296369 baseEnd_296369 := by
    simpa [prefixWord, tailWord_296369, baseEnd_296369] using wordTrace_append hprefix tailTrace_296369
  have hstable : (prefixWord ++ tailWord_296369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296369).length < 2 ^ (prefixWord ++ tailWord_296369).sum := by decide
  have hdescent : baseEnd_296369 < baseStart_296369 := by decide
  rcases family_descends (prefixWord ++ tailWord_296369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296388 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_296388 : Nat := 118140960795 + 296388 * 2 ^ 59
def prefixEnd_296388 : Nat := 4983230072969 + 3 ^ 40 * 296388 * 2
def baseEnd_296388 : Nat := 33819889827753692063765

theorem tailTrace_296388 : CollatzResearch.WordTrace tailWord_296388 prefixEnd_296388 33819889827753692063765 := by
  unfold tailWord_296388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405079225122184942760909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7206772300162913257014545 5405079225122184942760909)
  ·
    refine ⟨2026904709420819353535341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5405079225122184942760909 2026904709420819353535341)
    ·
      refine ⟨760089266032807257575753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2026904709420819353535341 760089266032807257575753)
      ·
        refine ⟨570066949524605443181815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760089266032807257575753 570066949524605443181815)
        ·
          refine ⟨855100424286908164772723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570066949524605443181815 855100424286908164772723)
          ·
            refine ⟨1282650636430362247159085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855100424286908164772723 1282650636430362247159085)
            ·
              refine ⟨480993988661385842684657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282650636430362247159085 480993988661385842684657)
              ·
                refine ⟨360745491496039382013493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480993988661385842684657 360745491496039382013493)
                ·
                  refine ⟨33819889827753692063765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360745491496039382013493 33819889827753692063765)
                  ·
                    rfl

theorem cell22_296388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_296388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296388 prefixEnd_296388 := by exact prefixLift 296388
  have htrace : WordTrace (prefixWord ++ tailWord_296388) baseStart_296388 baseEnd_296388 := by
    simpa [prefixWord, tailWord_296388, baseEnd_296388] using wordTrace_append hprefix tailTrace_296388
  have hstable : (prefixWord ++ tailWord_296388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296388).length < 2 ^ (prefixWord ++ tailWord_296388).sum := by decide
  have hdescent : baseEnd_296388 < baseStart_296388 := by decide
  rcases family_descends (prefixWord ++ tailWord_296388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296399 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 6]
def baseStart_296399 : Nat := 118140960795 + 296399 * 2 ^ 59
def prefixEnd_296399 : Nat := 4983230072969 + 3 ^ 40 * 296399 * 2
def baseEnd_296399 : Nat := 33821145002686904722087

theorem tailTrace_296399 : CollatzResearch.WordTrace tailWord_296399 prefixEnd_296399 33821145002686904722087 := by
  unfold tailWord_296399
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810559653204518764172251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207039768803012509448167 10810559653204518764172251)
  ·
    refine ⟨16215839479806778146258377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810559653204518764172251 16215839479806778146258377)
    ·
      refine ⟨12161879609855083609693783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215839479806778146258377 12161879609855083609693783)
      ·
        refine ⟨18242819414782625414540675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161879609855083609693783 18242819414782625414540675)
        ·
          refine ⟨27364229122173938121811013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18242819414782625414540675 27364229122173938121811013)
          ·
            refine ⟨5130792960407613397839565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27364229122173938121811013 5130792960407613397839565)
            ·
              refine ⟨1924047360152855024189837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5130792960407613397839565 1924047360152855024189837)
              ·
                refine ⟨721517760057320634071189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924047360152855024189837 721517760057320634071189)
                ·
                  refine ⟨33821145002686904722087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 721517760057320634071189 33821145002686904722087)
                  ·
                    rfl

theorem cell22_296399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_296399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296399 prefixEnd_296399 := by exact prefixLift 296399
  have htrace : WordTrace (prefixWord ++ tailWord_296399) baseStart_296399 baseEnd_296399 := by
    simpa [prefixWord, tailWord_296399, baseEnd_296399] using wordTrace_append hprefix tailTrace_296399
  have hstable : (prefixWord ++ tailWord_296399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296399).length < 2 ^ (prefixWord ++ tailWord_296399).sum := by decide
  have hdescent : baseEnd_296399 < baseStart_296399 := by decide
  rcases family_descends (prefixWord ++ tailWord_296399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296431 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 4, 3]
def baseStart_296431 : Nat := 118140960795 + 296431 * 2 ^ 59
def prefixEnd_296431 : Nat := 4983230072969 + 3 ^ 40 * 296431 * 2
def baseEnd_296431 : Nat := 101474389262023297366163

theorem tailTrace_296431 : CollatzResearch.WordTrace tailWord_296431 prefixEnd_296431 101474389262023297366163 := by
  unfold tailWord_296431
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811726789088588229337147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207817859392392152891431 10811726789088588229337147)
  ·
    refine ⟨16217590183632882344005721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811726789088588229337147 16217590183632882344005721)
    ·
      refine ⟨12163192637724661758004291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16217590183632882344005721 12163192637724661758004291)
      ·
        refine ⟨18244788956586992637006437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12163192637724661758004291 18244788956586992637006437)
        ·
          refine ⟨3420897929360061119438707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18244788956586992637006437 3420897929360061119438707)
          ·
            refine ⟨5131346894040091679158061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420897929360061119438707 5131346894040091679158061)
            ·
              refine ⟨1924255085265034379684273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5131346894040091679158061 1924255085265034379684273)
              ·
                refine ⟨1443191313948775784763205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924255085265034379684273 1443191313948775784763205)
                ·
                  refine ⟨270598371365395459643101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443191313948775784763205 270598371365395459643101)
                  ·
                    refine ⟨101474389262023297366163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270598371365395459643101 101474389262023297366163)
                    ·
                      rfl

theorem cell22_296431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_296431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296431 prefixEnd_296431 := by exact prefixLift 296431
  have htrace : WordTrace (prefixWord ++ tailWord_296431) baseStart_296431 baseEnd_296431 := by
    simpa [prefixWord, tailWord_296431, baseEnd_296431] using wordTrace_append hprefix tailTrace_296431
  have hstable : (prefixWord ++ tailWord_296431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296431).length < 2 ^ (prefixWord ++ tailWord_296431).sum := by decide
  have hdescent : baseEnd_296431 < baseStart_296431 := by decide
  rcases family_descends (prefixWord ++ tailWord_296431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296433 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 4]
def baseStart_296433 : Nat := 118140960795 + 296433 * 2 ^ 59
def prefixEnd_296433 : Nat := 4983230072969 + 3 ^ 40 * 296433 * 2
def baseEnd_296433 : Nat := 33825024634298652938719

theorem tailTrace_296433 : CollatzResearch.WordTrace tailWord_296433 prefixEnd_296433 33825024634298652938719 := by
  unfold tailWord_296433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811799735081342570909953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207866490054228380606635 10811799735081342570909953)
  ·
    refine ⟨8108849801311006928182465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10811799735081342570909953 8108849801311006928182465)
    ·
      refine ⟨6081637350983255196136849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8108849801311006928182465 6081637350983255196136849)
      ·
        refine ⟨4561228013237441397102637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6081637350983255196136849 4561228013237441397102637)
        ·
          refine ⟨1710460504964040523913489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4561228013237441397102637 1710460504964040523913489)
          ·
            refine ⟨1282845378723030392935117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710460504964040523913489 1282845378723030392935117)
            ·
              refine ⟨481067017021136397350669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282845378723030392935117 481067017021136397350669)
              ·
                refine ⟨180400131382926149006501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481067017021136397350669 180400131382926149006501)
                ·
                  refine ⟨33825024634298652938719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180400131382926149006501 33825024634298652938719)
                  ·
                    rfl

theorem cell22_296433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_296433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296433 prefixEnd_296433 := by exact prefixLift 296433
  have htrace : WordTrace (prefixWord ++ tailWord_296433) baseStart_296433 baseEnd_296433 := by
    simpa [prefixWord, tailWord_296433, baseEnd_296433] using wordTrace_append hprefix tailTrace_296433
  have hstable : (prefixWord ++ tailWord_296433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296433).length < 2 ^ (prefixWord ++ tailWord_296433).sum := by decide
  have hdescent : baseEnd_296433 < baseStart_296433 := by decide
  rcases family_descends (prefixWord ++ tailWord_296433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296444 : List Nat := [2, 2, 2, 1, 2, 1, 12]
def baseStart_296444 : Nat := 118140960795 + 296444 * 2 ^ 59
def prefixEnd_296444 : Nat := 4983230072969 + 3 ^ 40 * 296444 * 2
def baseEnd_296444 : Nat := 3758475534359096177449

theorem tailTrace_296444 : CollatzResearch.WordTrace tailWord_296444 prefixEnd_296444 3758475534359096177449 := by
  unfold tailWord_296444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406100469020745724780193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7208133958694327633040257 5406100469020745724780193)
  ·
    refine ⟨4054575351765559293585145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5406100469020745724780193 4054575351765559293585145)
    ·
      refine ⟨3040931513824169470188859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4054575351765559293585145 3040931513824169470188859)
      ·
        refine ⟨4561397270736254205283289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040931513824169470188859 4561397270736254205283289)
        ·
          refine ⟨3421047953052190653962467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4561397270736254205283289 3421047953052190653962467)
          ·
            refine ⟨5131571929578285980943701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421047953052190653962467 5131571929578285980943701)
            ·
              refine ⟨3758475534359096177449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 5131571929578285980943701 3758475534359096177449)
              ·
                rfl

theorem cell22_296444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 12].length) (baseStart_296444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296444 prefixEnd_296444 := by exact prefixLift 296444
  have htrace : WordTrace (prefixWord ++ tailWord_296444) baseStart_296444 baseEnd_296444 := by
    simpa [prefixWord, tailWord_296444, baseEnd_296444] using wordTrace_append hprefix tailTrace_296444
  have hstable : (prefixWord ++ tailWord_296444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296444).length < 2 ^ (prefixWord ++ tailWord_296444).sum := by decide
  have hdescent : baseEnd_296444 < baseStart_296444 := by decide
  rcases family_descends (prefixWord ++ tailWord_296444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296450 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_296450 : Nat := 118140960795 + 296450 * 2 ^ 59
def prefixEnd_296450 : Nat := 4983230072969 + 3 ^ 40 * 296450 * 2
def baseEnd_296450 : Nat := 33826964450104527047035

theorem tailTrace_296450 : CollatzResearch.WordTrace tailWord_296450 prefixEnd_296450 33826964450104527047035 := by
  unfold tailWord_296450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703104944004938618569701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7208279850679836316185869 2703104944004938618569701)
  ·
    refine ⟨506832177000925990981819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2703104944004938618569701 506832177000925990981819)
    ·
      refine ⟨760248265501388986472729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506832177000925990981819 760248265501388986472729)
      ·
        refine ⟨570186199126041739854547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760248265501388986472729 570186199126041739854547)
        ·
          refine ⟨855279298689062609781821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570186199126041739854547 855279298689062609781821)
          ·
            refine ⟨320729737008398478668183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 855279298689062609781821 320729737008398478668183)
            ·
              refine ⟨481094605512597718002275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320729737008398478668183 481094605512597718002275)
              ·
                refine ⟨721641908268896577003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481094605512597718002275 721641908268896577003413)
                ·
                  refine ⟨33826964450104527047035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 721641908268896577003413 33826964450104527047035)
                  ·
                    rfl

theorem cell22_296450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_296450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296450 prefixEnd_296450 := by exact prefixLift 296450
  have htrace : WordTrace (prefixWord ++ tailWord_296450) baseStart_296450 baseEnd_296450 := by
    simpa [prefixWord, tailWord_296450, baseEnd_296450] using wordTrace_append hprefix tailTrace_296450
  have hstable : (prefixWord ++ tailWord_296450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296450).length < 2 ^ (prefixWord ++ tailWord_296450).sum := by decide
  have hdescent : baseEnd_296450 < baseStart_296450 := by decide
  rcases family_descends (prefixWord ++ tailWord_296450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296557 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 5]
def baseStart_296557 : Nat := 118140960795 + 296557 * 2 ^ 59
def prefixEnd_296557 : Nat := 4983230072969 + 3 ^ 40 * 296557 * 2
def baseEnd_296557 : Nat := 33839173879000322905259

theorem tailTrace_296557 : CollatzResearch.WordTrace tailWord_296557 prefixEnd_296557 33839173879000322905259 := by
  unfold tailWord_296557
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816322386632111748423925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7210881591088074498949283 10816322386632111748423925)
  ·
    refine ⟨1014030223746760476414743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10816322386632111748423925 1014030223746760476414743)
    ·
      refine ⟨1521045335620140714622115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014030223746760476414743 1521045335620140714622115)
      ·
        refine ⟨2281568003430211071933173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521045335620140714622115 2281568003430211071933173)
        ·
          refine ⟨213897000321582287993735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2281568003430211071933173 213897000321582287993735)
          ·
            refine ⟨320845500482373431990603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213897000321582287993735 320845500482373431990603)
            ·
              refine ⟨481268250723560147985905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320845500482373431990603 481268250723560147985905)
              ·
                refine ⟨360951188042670110989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481268250723560147985905 360951188042670110989429)
                ·
                  refine ⟨33839173879000322905259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360951188042670110989429 33839173879000322905259)
                  ·
                    rfl

theorem cell22_296557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_296557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296557 prefixEnd_296557 := by exact prefixLift 296557
  have htrace : WordTrace (prefixWord ++ tailWord_296557) baseStart_296557 baseEnd_296557 := by
    simpa [prefixWord, tailWord_296557, baseEnd_296557] using wordTrace_append hprefix tailTrace_296557
  have hstable : (prefixWord ++ tailWord_296557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296557).length < 2 ^ (prefixWord ++ tailWord_296557).sum := by decide
  have hdescent : baseEnd_296557 < baseStart_296557 := by decide
  rcases family_descends (prefixWord ++ tailWord_296557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296581 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_296581 : Nat := 118140960795 + 296581 * 2 ^ 59
def prefixEnd_296581 : Nat := 4983230072969 + 3 ^ 40 * 296581 * 2
def baseEnd_296581 : Nat := 101525737327472906115703

theorem tailTrace_296581 : CollatzResearch.WordTrace tailWord_296581 prefixEnd_296581 101525737327472906115703 := by
  unfold tailWord_296581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817197738545163847297597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7211465159030109231531731 10817197738545163847297597)
  ·
    refine ⟨4056449151954436442736599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10817197738545163847297597 4056449151954436442736599)
    ·
      refine ⟨6084673727931654664104899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4056449151954436442736599 6084673727931654664104899)
      ·
        refine ⟨9127010591897481996157349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6084673727931654664104899 9127010591897481996157349)
        ·
          refine ⟨1711314485980777874279503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9127010591897481996157349 1711314485980777874279503)
          ·
            refine ⟨2566971728971166811419255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711314485980777874279503 2566971728971166811419255)
            ·
              refine ⟨3850457593456750217128883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566971728971166811419255 3850457593456750217128883)
              ·
                refine ⟨5775686390185125325693325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850457593456750217128883 5775686390185125325693325)
                ·
                  refine ⟨2165882396319421997134997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5775686390185125325693325 2165882396319421997134997)
                  ·
                    refine ⟨101525737327472906115703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2165882396319421997134997 101525737327472906115703)
                    ·
                      rfl

theorem cell22_296581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_296581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296581 prefixEnd_296581 := by exact prefixLift 296581
  have htrace : WordTrace (prefixWord ++ tailWord_296581) baseStart_296581 baseEnd_296581 := by
    simpa [prefixWord, tailWord_296581, baseEnd_296581] using wordTrace_append hprefix tailTrace_296581
  have hstable : (prefixWord ++ tailWord_296581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296581).length < 2 ^ (prefixWord ++ tailWord_296581).sum := by decide
  have hdescent : baseEnd_296581 < baseStart_296581 := by decide
  rcases family_descends (prefixWord ++ tailWord_296581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296583 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_296583 : Nat := 118140960795 + 296583 * 2 ^ 59
def prefixEnd_296583 : Nat := 4983230072969 + 3 ^ 40 * 296583 * 2
def baseEnd_296583 : Nat := 101526421968345567565697

theorem tailTrace_296583 : CollatzResearch.WordTrace tailWord_296583 prefixEnd_296583 101526421968345567565697 := by
  unfold tailWord_296583
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817270684537918188870403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7211513789691945459246935 10817270684537918188870403)
  ·
    refine ⟨16225906026806877283305605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10817270684537918188870403 16225906026806877283305605)
    ·
      refine ⟨3042357380026289490619801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16225906026806877283305605 3042357380026289490619801)
      ·
        refine ⟨2281768035019717117964851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3042357380026289490619801 2281768035019717117964851)
        ·
          refine ⟨3422652052529575676947277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281768035019717117964851 3422652052529575676947277)
          ·
            refine ⟨1283494519698590878855229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3422652052529575676947277 1283494519698590878855229)
            ·
              refine ⟨481310444886971579570711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1283494519698590878855229 481310444886971579570711)
              ·
                refine ⟨721965667330457369356067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481310444886971579570711 721965667330457369356067)
                ·
                  refine ⟨1082948500995686054034101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721965667330457369356067 1082948500995686054034101)
                  ·
                    refine ⟨101526421968345567565697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1082948500995686054034101 101526421968345567565697)
                    ·
                      rfl

theorem cell22_296583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_296583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296583 prefixEnd_296583 := by exact prefixLift 296583
  have htrace : WordTrace (prefixWord ++ tailWord_296583) baseStart_296583 baseEnd_296583 := by
    simpa [prefixWord, tailWord_296583, baseEnd_296583] using wordTrace_append hprefix tailTrace_296583
  have hstable : (prefixWord ++ tailWord_296583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296583).length < 2 ^ (prefixWord ++ tailWord_296583).sum := by decide
  have hdescent : baseEnd_296583 < baseStart_296583 := by decide
  rcases family_descends (prefixWord ++ tailWord_296583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296630 : List Nat := [5, 1, 3, 1, 1, 1, 1, 9]
def baseStart_296630 : Nat := 118140960795 + 296630 * 2 ^ 59
def prefixEnd_296630 : Nat := 4983230072969 + 3 ^ 40 * 296630 * 2
def baseEnd_296630 : Nat := 11282501225428123515617

theorem tailTrace_296630 : CollatzResearch.WordTrace tailWord_296630 prefixEnd_296630 11282501225428123515617 := by
  unfold tailWord_296630
  simp only [CollatzResearch.WordTrace]
  refine ⟨676186557210477825989459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7212656610245096810554229 676186557210477825989459)
  ·
    refine ⟨1014279835815716738984189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676186557210477825989459 1014279835815716738984189)
    ·
      refine ⟨380354938430893777119071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1014279835815716738984189 380354938430893777119071)
      ·
        refine ⟨570532407646340665678607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380354938430893777119071 570532407646340665678607)
        ·
          refine ⟨855798611469510998517911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570532407646340665678607 855798611469510998517911)
          ·
            refine ⟨1283697917204266497776867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855798611469510998517911 1283697917204266497776867)
            ·
              refine ⟨1925546875806399746665301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283697917204266497776867 1925546875806399746665301)
              ·
                refine ⟨11282501225428123515617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1925546875806399746665301 11282501225428123515617)
                ·
                  rfl

theorem cell22_296630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_296630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296630 prefixEnd_296630 := by exact prefixLift 296630
  have htrace : WordTrace (prefixWord ++ tailWord_296630) baseStart_296630 baseEnd_296630 := by
    simpa [prefixWord, tailWord_296630, baseEnd_296630] using wordTrace_append hprefix tailTrace_296630
  have hstable : (prefixWord ++ tailWord_296630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296630).length < 2 ^ (prefixWord ++ tailWord_296630).sum := by decide
  have hdescent : baseEnd_296630 < baseStart_296630 := by decide
  rcases family_descends (prefixWord ++ tailWord_296630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_296656 : Nat := 118140960795 + 296656 * 2 ^ 59
def prefixEnd_296656 : Nat := 4983230072969 + 3 ^ 40 * 296656 * 2
def baseEnd_296656 : Nat := 101551411360197710490473

theorem tailTrace_296656 : CollatzResearch.WordTrace tailWord_296656 prefixEnd_296656 101551411360197710490473 := by
  unfold tailWord_296656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409966606636725828138911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7213288808848967770851881 5409966606636725828138911)
  ·
    refine ⟨8114949909955088742208367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409966606636725828138911 8114949909955088742208367)
    ·
      refine ⟨12172424864932633113312551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8114949909955088742208367 12172424864932633113312551)
      ·
        refine ⟨18258637297398949669968827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12172424864932633113312551 18258637297398949669968827)
        ·
          refine ⟨27387955946098424504953241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18258637297398949669968827 27387955946098424504953241)
          ·
            refine ⟨20540966959573818378714931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27387955946098424504953241 20540966959573818378714931)
            ·
              refine ⟨30811450439360727568072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20540966959573818378714931 30811450439360727568072397)
              ·
                refine ⟨11554293914760272838027149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30811450439360727568072397 11554293914760272838027149)
                ·
                  refine ⟨4332860218035102314260181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11554293914760272838027149 4332860218035102314260181)
                  ·
                    refine ⟨101551411360197710490473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4332860218035102314260181 101551411360197710490473)
                    ·
                      rfl

theorem cell22_296656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_296656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296656 prefixEnd_296656 := by exact prefixLift 296656
  have htrace : WordTrace (prefixWord ++ tailWord_296656) baseStart_296656 baseEnd_296656 := by
    simpa [prefixWord, tailWord_296656, baseEnd_296656] using wordTrace_append hprefix tailTrace_296656
  have hstable : (prefixWord ++ tailWord_296656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296656).length < 2 ^ (prefixWord ++ tailWord_296656).sum := by decide
  have hdescent : baseEnd_296656 < baseStart_296656 := by decide
  rcases family_descends (prefixWord ++ tailWord_296656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296735 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 4, 3]
def baseStart_296735 : Nat := 118140960795 + 296735 * 2 ^ 59
def prefixEnd_296735 : Nat := 4983230072969 + 3 ^ 40 * 296735 * 2
def baseEnd_296735 : Nat := 101578454674667837765231

theorem tailTrace_296735 : CollatzResearch.WordTrace tailWord_296735 prefixEnd_296735 101578454674667837765231 := by
  unfold tailWord_296735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822814579987248148403659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7215209719991498765602439 10822814579987248148403659)
  ·
    refine ⟨16234221869980872222605489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10822814579987248148403659 16234221869980872222605489)
    ·
      refine ⟨12175666402485654166954117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16234221869980872222605489 12175666402485654166954117)
      ·
        refine ⟨2282937450466060156303897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12175666402485654166954117 2282937450466060156303897)
        ·
          refine ⟨1712203087849545117227923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282937450466060156303897 1712203087849545117227923)
          ·
            refine ⟨2568304631774317675841885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712203087849545117227923 2568304631774317675841885)
            ·
              refine ⟨963114236915369128440707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2568304631774317675841885 963114236915369128440707)
              ·
                refine ⟨1444671355373053692661061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963114236915369128440707 1444671355373053692661061)
                ·
                  refine ⟨270875879132447567373949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444671355373053692661061 270875879132447567373949)
                  ·
                    refine ⟨101578454674667837765231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270875879132447567373949 101578454674667837765231)
                    ·
                      rfl

theorem cell22_296735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_296735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296735 prefixEnd_296735 := by exact prefixLift 296735
  have htrace : WordTrace (prefixWord ++ tailWord_296735) baseStart_296735 baseEnd_296735 := by
    simpa [prefixWord, tailWord_296735, baseEnd_296735] using wordTrace_append hprefix tailTrace_296735
  have hstable : (prefixWord ++ tailWord_296735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296735).length < 2 ^ (prefixWord ++ tailWord_296735).sum := by decide
  have hdescent : baseEnd_296735 < baseStart_296735 := by decide
  rcases family_descends (prefixWord ++ tailWord_296735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296765 : List Nat := [1, 4, 1, 4, 1, 2, 1, 8]
def baseStart_296765 : Nat := 118140960795 + 296765 * 2 ^ 59
def prefixEnd_296765 : Nat := 4983230072969 + 3 ^ 40 * 296765 * 2
def baseEnd_296765 : Nat := 11287636031973084390571

theorem tailTrace_296765 : CollatzResearch.WordTrace tailWord_296765 prefixEnd_296765 11287636031973084390571 := by
  unfold tailWord_296765
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823908769878563271995749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7215939179919042181330499 10823908769878563271995749)
  ·
    refine ⟨2029482894352230613499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10823908769878563271995749 2029482894352230613499203)
    ·
      refine ⟨3044224341528345920248805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029482894352230613499203 3044224341528345920248805)
      ·
        refine ⟨570792064036564860046651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3044224341528345920248805 570792064036564860046651)
        ·
          refine ⟨856188096054847290069977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570792064036564860046651 856188096054847290069977)
          ·
            refine ⟨642141072041135467552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856188096054847290069977 642141072041135467552483)
            ·
              refine ⟨963211608061703201328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642141072041135467552483 963211608061703201328725)
              ·
                refine ⟨11287636031973084390571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 963211608061703201328725 11287636031973084390571)
                ·
                  rfl

theorem cell22_296765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 8].length) (baseStart_296765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296765 prefixEnd_296765 := by exact prefixLift 296765
  have htrace : WordTrace (prefixWord ++ tailWord_296765) baseStart_296765 baseEnd_296765 := by
    simpa [prefixWord, tailWord_296765, baseEnd_296765] using wordTrace_append hprefix tailTrace_296765
  have hstable : (prefixWord ++ tailWord_296765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296765).length < 2 ^ (prefixWord ++ tailWord_296765).sum := by decide
  have hdescent : baseEnd_296765 < baseStart_296765 := by decide
  rcases family_descends (prefixWord ++ tailWord_296765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296793 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 7]
def baseStart_296793 : Nat := 118140960795 + 296793 * 2 ^ 59
def prefixEnd_296793 : Nat := 4983230072969 + 3 ^ 40 * 296793 * 2
def baseEnd_296793 : Nat := 33866103086658339938351

theorem tailTrace_296793 : CollatzResearch.WordTrace tailWord_296793 prefixEnd_296793 33866103086658339938351 := by
  unfold tailWord_296793
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824930013777124054015033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7216620009184749369343355 10824930013777124054015033)
  ·
    refine ⟨8118697510332843040511275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10824930013777124054015033 8118697510332843040511275)
    ·
      refine ⟨12178046265499264560766913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8118697510332843040511275 12178046265499264560766913)
      ·
        refine ⟨9133534699124448420575185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12178046265499264560766913 9133534699124448420575185)
        ·
          refine ⟨6850151024343336315431389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9133534699124448420575185 6850151024343336315431389)
          ·
            refine ⟨2568806634128751118286771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6850151024343336315431389 2568806634128751118286771)
            ·
              refine ⟨3853209951193126677430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568806634128751118286771 3853209951193126677430157)
              ·
                refine ⟨1444953731697422504036309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3853209951193126677430157 1444953731697422504036309)
                ·
                  refine ⟨33866103086658339938351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1444953731697422504036309 33866103086658339938351)
                  ·
                    rfl

theorem cell22_296793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_296793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296793 prefixEnd_296793 := by exact prefixLift 296793
  have htrace : WordTrace (prefixWord ++ tailWord_296793) baseStart_296793 baseEnd_296793 := by
    simpa [prefixWord, tailWord_296793, baseEnd_296793] using wordTrace_append hprefix tailTrace_296793
  have hstable : (prefixWord ++ tailWord_296793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296793).length < 2 ^ (prefixWord ++ tailWord_296793).sum := by decide
  have hdescent : baseEnd_296793 < baseStart_296793 := by decide
  rcases family_descends (prefixWord ++ tailWord_296793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296904 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_296904 : Nat := 118140960795 + 296904 * 2 ^ 59
def prefixEnd_296904 : Nat := 4983230072969 + 3 ^ 40 * 296904 * 2
def baseEnd_296904 : Nat := 101636306828407730289713

theorem tailTrace_296904 : CollatzResearch.WordTrace tailWord_296904 prefixEnd_296904 101636306828407730289713 := by
  unfold tailWord_296904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414489258187495005652883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7219319010916660007537177 5414489258187495005652883)
  ·
    refine ⟨8121733887281242508479325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5414489258187495005652883 8121733887281242508479325)
    ·
      refine ⟨3045650207730465940679747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8121733887281242508479325 3045650207730465940679747)
      ·
        refine ⟨4568475311595698911019621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045650207730465940679747 4568475311595698911019621)
        ·
          refine ⟨856589120924193545816179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4568475311595698911019621 856589120924193545816179)
          ·
            refine ⟨1284883681386290318724269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856589120924193545816179 1284883681386290318724269)
            ·
              refine ⟨481831380519858869521601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284883681386290318724269 481831380519858869521601)
              ·
                refine ⟨361373535389894152141201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481831380519858869521601 361373535389894152141201)
                ·
                  refine ⟨271030151542420614105901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361373535389894152141201 271030151542420614105901)
                  ·
                    refine ⟨101636306828407730289713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271030151542420614105901 101636306828407730289713)
                    ·
                      rfl

theorem cell22_296904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_296904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296904 prefixEnd_296904 := by exact prefixLift 296904
  have htrace : WordTrace (prefixWord ++ tailWord_296904) baseStart_296904 baseEnd_296904 := by
    simpa [prefixWord, tailWord_296904, baseEnd_296904] using wordTrace_append hprefix tailTrace_296904
  have hstable : (prefixWord ++ tailWord_296904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296904).length < 2 ^ (prefixWord ++ tailWord_296904).sum := by decide
  have hdescent : baseEnd_296904 < baseStart_296904 := by decide
  rcases family_descends (prefixWord ++ tailWord_296904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296921 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_296921 : Nat := 118140960795 + 296921 * 2 ^ 59
def prefixEnd_296921 : Nat := 4983230072969 + 3 ^ 40 * 296921 * 2
def baseEnd_296921 : Nat := 101642126275825352614661

theorem tailTrace_296921 : CollatzResearch.WordTrace tailWord_296921 prefixEnd_296921 101642126275825352614661 := by
  unfold tailWord_296921
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829598557313401914674617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7219732371542267943116411 10829598557313401914674617)
  ·
    refine ⟨8122198917985051436005963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10829598557313401914674617 8122198917985051436005963)
    ·
      refine ⟨12183298376977577154008945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122198917985051436005963 12183298376977577154008945)
      ·
        refine ⟨9137473782733182865506709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12183298376977577154008945 9137473782733182865506709)
        ·
          refine ⟨428319083565617946820627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9137473782733182865506709 428319083565617946820627)
          ·
            refine ⟨642478625348426920230941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428319083565617946820627 642478625348426920230941)
            ·
              refine ⟨240929484505660095086603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642478625348426920230941 240929484505660095086603)
              ·
                refine ⟨361394226758490142629905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240929484505660095086603 361394226758490142629905)
                ·
                  refine ⟨271045670068867606972429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361394226758490142629905 271045670068867606972429)
                  ·
                    refine ⟨101642126275825352614661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271045670068867606972429 101642126275825352614661)
                    ·
                      rfl

theorem cell22_296921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_296921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296921 prefixEnd_296921 := by exact prefixLift 296921
  have htrace : WordTrace (prefixWord ++ tailWord_296921) baseStart_296921 baseEnd_296921 := by
    simpa [prefixWord, tailWord_296921, baseEnd_296921] using wordTrace_append hprefix tailTrace_296921
  have hstable : (prefixWord ++ tailWord_296921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296921).length < 2 ^ (prefixWord ++ tailWord_296921).sum := by decide
  have hdescent : baseEnd_296921 < baseStart_296921 := by decide
  rcases family_descends (prefixWord ++ tailWord_296921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296932 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_296932 : Nat := 118140960795 + 296932 * 2 ^ 59
def prefixEnd_296932 : Nat := 4983230072969 + 3 ^ 40 * 296932 * 2
def baseEnd_296932 : Nat := 101645891800624990589627

theorem tailTrace_296932 : CollatzResearch.WordTrace tailWord_296932 prefixEnd_296932 101645891800624990589627 := by
  unfold tailWord_296932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414999880136775396662525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7219999840182367195550033 5414999880136775396662525)
  ·
    refine ⟨2030624955051290773748447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5414999880136775396662525 2030624955051290773748447)
    ·
      refine ⟨3045937432576936160622671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030624955051290773748447 3045937432576936160622671)
      ·
        refine ⟨4568906148865404240934007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045937432576936160622671 4568906148865404240934007)
        ·
          refine ⟨6853359223298106361401011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568906148865404240934007 6853359223298106361401011)
          ·
            refine ⟨10280038834947159542101517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6853359223298106361401011 10280038834947159542101517)
            ·
              refine ⟨3855014563105184828288069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10280038834947159542101517 3855014563105184828288069)
              ·
                refine ⟨722815230582222155304013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3855014563105184828288069 722815230582222155304013)
                ·
                  refine ⟨271055711468333308239005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722815230582222155304013 271055711468333308239005)
                  ·
                    refine ⟨101645891800624990589627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271055711468333308239005 101645891800624990589627)
                    ·
                      rfl

theorem cell22_296932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_296932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296932 prefixEnd_296932 := by exact prefixLift 296932
  have htrace : WordTrace (prefixWord ++ tailWord_296932) baseStart_296932 baseEnd_296932 := by
    simpa [prefixWord, tailWord_296932, baseEnd_296932] using wordTrace_append hprefix tailTrace_296932
  have hstable : (prefixWord ++ tailWord_296932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296932).length < 2 ^ (prefixWord ++ tailWord_296932).sum := by decide
  have hdescent : baseEnd_296932 < baseStart_296932 := by decide
  rcases family_descends (prefixWord ++ tailWord_296932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_296960 : Nat := 118140960795 + 296960 * 2 ^ 59
def prefixEnd_296960 : Nat := 4983230072969 + 3 ^ 40 * 296960 * 2
def baseEnd_296960 : Nat := 101655476772842250889541

theorem tailTrace_296960 : CollatzResearch.WordTrace tailWord_296960 prefixEnd_296960 101655476772842250889541 := by
  unfold tailWord_296960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415510502086055787672167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7220680669448074383562889 5415510502086055787672167)
  ·
    refine ⟨8123265753129083681508251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415510502086055787672167 8123265753129083681508251)
    ·
      refine ⟨12184898629693625522262377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8123265753129083681508251 12184898629693625522262377)
      ·
        refine ⟨9138673972270219141696783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12184898629693625522262377 9138673972270219141696783)
        ·
          refine ⟨13708010958405328712545175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138673972270219141696783 13708010958405328712545175)
          ·
            refine ⟨20562016437607993068817763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13708010958405328712545175 20562016437607993068817763)
            ·
              refine ⟨30843024656411989603226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20562016437607993068817763 30843024656411989603226645)
              ·
                refine ⟨1445766780769312012651249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30843024656411989603226645 1445766780769312012651249)
                ·
                  refine ⟨1084325085576984009488437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445766780769312012651249 1084325085576984009488437)
                  ·
                    refine ⟨101655476772842250889541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1084325085576984009488437 101655476772842250889541)
                    ·
                      rfl

theorem cell22_296960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_296960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_296960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_296960 prefixEnd_296960 := by exact prefixLift 296960
  have htrace : WordTrace (prefixWord ++ tailWord_296960) baseStart_296960 baseEnd_296960 := by
    simpa [prefixWord, tailWord_296960, baseEnd_296960] using wordTrace_append hprefix tailTrace_296960
  have hstable : (prefixWord ++ tailWord_296960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296960).length < 2 ^ (prefixWord ++ tailWord_296960).sum := by decide
  have hdescent : baseEnd_296960 < baseStart_296960 := by decide
  rcases family_descends (prefixWord ++ tailWord_296960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297024 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_297024 : Nat := 118140960795 + 297024 * 2 ^ 59
def prefixEnd_297024 : Nat := 4983230072969 + 3 ^ 40 * 297024 * 2
def baseEnd_297024 : Nat := 33892461760255805763115

theorem tailTrace_297024 : CollatzResearch.WordTrace tailWord_297024 prefixEnd_297024 33892461760255805763115 := by
  unfold tailWord_297024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416677637970125252837063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7222236850626833670449417 5416677637970125252837063)
  ·
    refine ⟨8125016456955187879255595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416677637970125252837063 8125016456955187879255595)
    ·
      refine ⟨12187524685432781818883393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125016456955187879255595 12187524685432781818883393)
      ·
        refine ⟨9140643514074586364162545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12187524685432781818883393 9140643514074586364162545)
        ·
          refine ⟨6855482635555939773121909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9140643514074586364162545 6855482635555939773121909)
          ·
            refine ⟨642701497083369353730179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6855482635555939773121909 642701497083369353730179)
            ·
              refine ⟨964052245625054030595269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642701497083369353730179 964052245625054030595269)
              ·
                refine ⟨180759796054697630736613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 964052245625054030595269 180759796054697630736613)
                ·
                  refine ⟨33892461760255805763115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180759796054697630736613 33892461760255805763115)
                  ·
                    rfl

theorem cell22_297024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_297024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297024 prefixEnd_297024 := by exact prefixLift 297024
  have htrace : WordTrace (prefixWord ++ tailWord_297024) baseStart_297024 baseEnd_297024 := by
    simpa [prefixWord, tailWord_297024, baseEnd_297024] using wordTrace_append hprefix tailTrace_297024
  have hstable : (prefixWord ++ tailWord_297024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297024).length < 2 ^ (prefixWord ++ tailWord_297024).sum := by decide
  have hdescent : baseEnd_297024 < baseStart_297024 := by decide
  rcases family_descends (prefixWord ++ tailWord_297024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297058 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_297058 : Nat := 118140960795 + 297058 * 2 ^ 59
def prefixEnd_297058 : Nat := 4983230072969 + 3 ^ 40 * 297058 * 2
def baseEnd_297058 : Nat := 33896341391867553979747

theorem tailTrace_297058 : CollatzResearch.WordTrace tailWord_297058 prefixEnd_297058 33896341391867553979747 := by
  unfold tailWord_297058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708648839454268578102957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7223063571878049541607885 2708648839454268578102957)
  ·
    refine ⟨1015743314795350716788609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2708648839454268578102957 1015743314795350716788609)
    ·
      refine ⟨761807486096513037591457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015743314795350716788609 761807486096513037591457)
      ·
        refine ⟨571355614572384778193593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761807486096513037591457 571355614572384778193593)
        ·
          refine ⟨428516710929288583645195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571355614572384778193593 428516710929288583645195)
          ·
            refine ⟨642775066393932875467793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428516710929288583645195 642775066393932875467793)
            ·
              refine ⟨482081299795449656600845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642775066393932875467793 482081299795449656600845)
              ·
                refine ⟨180780487423293621225317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482081299795449656600845 180780487423293621225317)
                ·
                  refine ⟨33896341391867553979747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180780487423293621225317 33896341391867553979747)
                  ·
                    rfl

theorem cell22_297058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_297058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297058 prefixEnd_297058 := by exact prefixLift 297058
  have htrace : WordTrace (prefixWord ++ tailWord_297058) baseStart_297058 baseEnd_297058 := by
    simpa [prefixWord, tailWord_297058, baseEnd_297058] using wordTrace_append hprefix tailTrace_297058
  have hstable : (prefixWord ++ tailWord_297058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297058).length < 2 ^ (prefixWord ++ tailWord_297058).sum := by decide
  have hdescent : baseEnd_297058 < baseStart_297058 := by decide
  rcases family_descends (prefixWord ++ tailWord_297058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297084 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_297084 : Nat := 118140960795 + 297084 * 2 ^ 59
def prefixEnd_297084 : Nat := 4983230072969 + 3 ^ 40 * 297084 * 2
def baseEnd_297084 : Nat := 101697924506947260789161

theorem tailTrace_297084 : CollatzResearch.WordTrace tailWord_297084 prefixEnd_297084 101697924506947260789161 := by
  unfold tailWord_297084
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417771827861440376429153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7223695770481920501905537 5417771827861440376429153)
  ·
    refine ⟨4063328870896080282321865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5417771827861440376429153 4063328870896080282321865)
    ·
      refine ⟨3047496653172060211741399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4063328870896080282321865 3047496653172060211741399)
      ·
        refine ⟨4571244979758090317612099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047496653172060211741399 4571244979758090317612099)
        ·
          refine ⟨6856867469637135476418149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571244979758090317612099 6856867469637135476418149)
          ·
            refine ⟨1285662650556962901828403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6856867469637135476418149 1285662650556962901828403)
            ·
              refine ⟨1928493975835444352742605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285662650556962901828403 1928493975835444352742605)
              ·
                refine ⟨723185240938291632278477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1928493975835444352742605 723185240938291632278477)
                ·
                  refine ⟨271194465351859362104429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723185240938291632278477 271194465351859362104429)
                  ·
                    refine ⟨101697924506947260789161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271194465351859362104429 101697924506947260789161)
                    ·
                      rfl

theorem cell22_297084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_297084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297084 prefixEnd_297084 := by exact prefixLift 297084
  have htrace : WordTrace (prefixWord ++ tailWord_297084) baseStart_297084 baseEnd_297084 := by
    simpa [prefixWord, tailWord_297084, baseEnd_297084] using wordTrace_append hprefix tailTrace_297084
  have hstable : (prefixWord ++ tailWord_297084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297084).length < 2 ^ (prefixWord ++ tailWord_297084).sum := by decide
  have hdescent : baseEnd_297084 < baseStart_297084 := by decide
  rcases family_descends (prefixWord ++ tailWord_297084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297148 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_297148 : Nat := 118140960795 + 297148 * 2 ^ 59
def prefixEnd_297148 : Nat := 4983230072969 + 3 ^ 40 * 297148 * 2
def baseEnd_297148 : Nat := 33906611004957475729655

theorem tailTrace_297148 : CollatzResearch.WordTrace tailWord_297148 prefixEnd_297148 33906611004957475729655 := by
  unfold tailWord_297148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418938963745509841594049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7225251951660679788792065 5418938963745509841594049)
  ·
    refine ⟨4064204222809132381195537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5418938963745509841594049 4064204222809132381195537)
    ·
      refine ⟨3048153167106849285896653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4064204222809132381195537 3048153167106849285896653)
      ·
        refine ⟨1143057437665068482211245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3048153167106849285896653 1143057437665068482211245)
        ·
          refine ⟨428646539124400680829217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143057437665068482211245 428646539124400680829217)
          ·
            refine ⟨321484904343300510621913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428646539124400680829217 321484904343300510621913)
            ·
              refine ⟨241113678257475382966435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321484904343300510621913 241113678257475382966435)
              ·
                refine ⟨361670517386213074449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241113678257475382966435 361670517386213074449653)
                ·
                  refine ⟨33906611004957475729655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 361670517386213074449653 33906611004957475729655)
                  ·
                    rfl

theorem cell22_297148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_297148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297148 prefixEnd_297148 := by exact prefixLift 297148
  have htrace : WordTrace (prefixWord ++ tailWord_297148) baseStart_297148 baseEnd_297148 := by
    simpa [prefixWord, tailWord_297148, baseEnd_297148] using wordTrace_append hprefix tailTrace_297148
  have hstable : (prefixWord ++ tailWord_297148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297148).length < 2 ^ (prefixWord ++ tailWord_297148).sum := by decide
  have hdescent : baseEnd_297148 < baseStart_297148 := by decide
  rcases family_descends (prefixWord ++ tailWord_297148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297186 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_297186 : Nat := 118140960795 + 297186 * 2 ^ 59
def prefixEnd_297186 : Nat := 4983230072969 + 3 ^ 40 * 297186 * 2
def baseEnd_297186 : Nat := 101732841191452994738849

theorem tailTrace_297186 : CollatzResearch.WordTrace tailWord_297186 prefixEnd_297186 101732841191452994738849 := by
  unfold tailWord_297186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709815975338338043267853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7226175934235568115380941 2709815975338338043267853)
  ·
    refine ⟨1016180990751876766225445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2709815975338338043267853 1016180990751876766225445)
    ·
      refine ⟨190533935765976893667271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1016180990751876766225445 190533935765976893667271)
      ·
        refine ⟨285800903648965340500907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190533935765976893667271 285800903648965340500907)
        ·
          refine ⟨428701355473448010751361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285800903648965340500907 428701355473448010751361)
          ·
            refine ⟨321526016605086008063521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428701355473448010751361 321526016605086008063521)
            ·
              refine ⟨241144512453814506047641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321526016605086008063521 241144512453814506047641)
              ·
                refine ⟨180858384340360879535731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241144512453814506047641 180858384340360879535731)
                ·
                  refine ⟨271287576510541319303597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180858384340360879535731 271287576510541319303597)
                  ·
                    refine ⟨101732841191452994738849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271287576510541319303597 101732841191452994738849)
                    ·
                      rfl

theorem cell22_297186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_297186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297186 prefixEnd_297186 := by exact prefixLift 297186
  have htrace : WordTrace (prefixWord ++ tailWord_297186) baseStart_297186 baseEnd_297186 := by
    simpa [prefixWord, tailWord_297186, baseEnd_297186] using wordTrace_append hprefix tailTrace_297186
  have hstable : (prefixWord ++ tailWord_297186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297186).length < 2 ^ (prefixWord ++ tailWord_297186).sum := by decide
  have hdescent : baseEnd_297186 < baseStart_297186 := by decide
  rcases family_descends (prefixWord ++ tailWord_297186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297253 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_297253 : Nat := 118140960795 + 297253 * 2 ^ 59
def prefixEnd_297253 : Nat := 4983230072969 + 3 ^ 40 * 297253 * 2
def baseEnd_297253 : Nat := 101755776660687153313643

theorem tailTrace_297253 : CollatzResearch.WordTrace tailWord_297253 prefixEnd_297253 101755776660687153313643 := by
  unfold tailWord_297253
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841707592110622615760413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7227805061407081743840275 10841707592110622615760413)
  ·
    refine ⟨4065640347041483480910155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10841707592110622615760413 4065640347041483480910155)
    ·
      refine ⟨6098460520562225221365233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4065640347041483480910155 6098460520562225221365233)
      ·
        refine ⟨4573845390421668916023925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6098460520562225221365233 4573845390421668916023925)
        ·
          refine ⟨428798005352031460877243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4573845390421668916023925 428798005352031460877243)
          ·
            refine ⟨643197008028047191315865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428798005352031460877243 643197008028047191315865)
            ·
              refine ⟨482397756021035393486899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643197008028047191315865 482397756021035393486899)
              ·
                refine ⟨723596634031553090230349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482397756021035393486899 723596634031553090230349)
                ·
                  refine ⟨271348737761832408836381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723596634031553090230349 271348737761832408836381)
                  ·
                    refine ⟨101755776660687153313643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271348737761832408836381 101755776660687153313643)
                    ·
                      rfl

theorem cell22_297253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_297253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297253 prefixEnd_297253 := by exact prefixLift 297253
  have htrace : WordTrace (prefixWord ++ tailWord_297253) baseStart_297253 baseEnd_297253 := by
    simpa [prefixWord, tailWord_297253, baseEnd_297253] using wordTrace_append hprefix tailTrace_297253
  have hstable : (prefixWord ++ tailWord_297253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297253).length < 2 ^ (prefixWord ++ tailWord_297253).sum := by decide
  have hdescent : baseEnd_297253 < baseStart_297253 := by decide
  rcases family_descends (prefixWord ++ tailWord_297253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297296 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_297296 : Nat := 118140960795 + 297296 * 2 ^ 59
def prefixEnd_297296 : Nat := 4983230072969 + 3 ^ 40 * 297296 * 2
def baseEnd_297296 : Nat := 101770496439449374488511

theorem tailTrace_297296 : CollatzResearch.WordTrace tailWord_297296 prefixEnd_297296 101770496439449374488511 := by
  unfold tailWord_297296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421637965477420479787871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7228850620636560639717161 5421637965477420479787871)
  ·
    refine ⟨8132456948216130719681807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5421637965477420479787871 8132456948216130719681807)
    ·
      refine ⟨12198685422324196079522711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8132456948216130719681807 12198685422324196079522711)
      ·
        refine ⟨18298028133486294119284067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12198685422324196079522711 18298028133486294119284067)
        ·
          refine ⟨27447042200229441178926101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18298028133486294119284067 27447042200229441178926101)
          ·
            refine ⟨1286580103135755055262161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27447042200229441178926101 1286580103135755055262161)
            ·
              refine ⟨964935077351816291446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286580103135755055262161 964935077351816291446621)
              ·
                refine ⟨361850654006931109292483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964935077351816291446621 361850654006931109292483)
                ·
                  refine ⟨542775981010396663938725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361850654006931109292483 542775981010396663938725)
                  ·
                    refine ⟨101770496439449374488511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542775981010396663938725 101770496439449374488511)
                    ·
                      rfl

theorem cell22_297296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_297296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297296 prefixEnd_297296 := by exact prefixLift 297296
  have htrace : WordTrace (prefixWord ++ tailWord_297296) baseStart_297296 baseEnd_297296 := by
    simpa [prefixWord, tailWord_297296, baseEnd_297296] using wordTrace_append hprefix tailTrace_297296
  have hstable : (prefixWord ++ tailWord_297296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297296).length < 2 ^ (prefixWord ++ tailWord_297296).sum := by decide
  have hdescent : baseEnd_297296 < baseStart_297296 := by decide
  rcases family_descends (prefixWord ++ tailWord_297296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297311 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 4]
def baseStart_297311 : Nat := 118140960795 + 297311 * 2 ^ 59
def prefixEnd_297311 : Nat := 4983230072969 + 3 ^ 40 * 297311 * 2
def baseEnd_297311 : Nat := 33925210415331445121155

theorem tailTrace_297311 : CollatzResearch.WordTrace tailWord_297311 prefixEnd_297311 33925210415331445121155 := by
  unfold tailWord_297311
  simp only [CollatzResearch.WordTrace]
  refine ⟨10843823025900498521371787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7229215350600332347581191 10843823025900498521371787)
  ·
    refine ⟨16265734538850747782057681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10843823025900498521371787 16265734538850747782057681)
    ·
      refine ⟨12199300904138060836543261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16265734538850747782057681 12199300904138060836543261)
      ·
        refine ⟨4574737839051772813703723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12199300904138060836543261 4574737839051772813703723)
        ·
          refine ⟨6862106758577659220555585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574737839051772813703723 6862106758577659220555585)
          ·
            refine ⟨5146580068933244415416689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6862106758577659220555585 5146580068933244415416689)
            ·
              refine ⟨3859935051699933311562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146580068933244415416689 3859935051699933311562517)
              ·
                refine ⟨180934455548434373979493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3859935051699933311562517 180934455548434373979493)
                ·
                  refine ⟨33925210415331445121155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180934455548434373979493 33925210415331445121155)
                  ·
                    rfl

theorem cell22_297311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 4].length) (baseStart_297311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297311 prefixEnd_297311 := by exact prefixLift 297311
  have htrace : WordTrace (prefixWord ++ tailWord_297311) baseStart_297311 baseEnd_297311 := by
    simpa [prefixWord, tailWord_297311, baseEnd_297311] using wordTrace_append hprefix tailTrace_297311
  have hstable : (prefixWord ++ tailWord_297311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297311).length < 2 ^ (prefixWord ++ tailWord_297311).sum := by decide
  have hdescent : baseEnd_297311 < baseStart_297311 := by decide
  rcases family_descends (prefixWord ++ tailWord_297311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297339 : List Nat := [1, 1, 1, 1, 1, 7, 2, 8]
def baseStart_297339 : Nat := 118140960795 + 297339 * 2 ^ 59
def prefixEnd_297339 : Nat := 4983230072969 + 3 ^ 40 * 297339 * 2
def baseEnd_297339 : Nat := 11309468468690177295931

theorem tailTrace_297339 : CollatzResearch.WordTrace tailWord_297339 prefixEnd_297339 11309468468690177295931 := by
  unfold tailWord_297339
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844844269799059303391071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7229896179866039535594047 10844844269799059303391071)
  ·
    refine ⟨16267266404698588955086607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844844269799059303391071 16267266404698588955086607)
    ·
      refine ⟨24400899607047883432629911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16267266404698588955086607 24400899607047883432629911)
      ·
        refine ⟨36601349410571825148944867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24400899607047883432629911 36601349410571825148944867)
        ·
          refine ⟨54902024115857737723417301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36601349410571825148944867 54902024115857737723417301)
          ·
            refine ⟨1286766190215415727892593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54902024115857737723417301 1286766190215415727892593)
            ·
              refine ⟨965074642661561795919445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286766190215415727892593 965074642661561795919445)
              ·
                refine ⟨11309468468690177295931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 965074642661561795919445 11309468468690177295931)
                ·
                  rfl

theorem cell22_297339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_297339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297339 prefixEnd_297339 := by exact prefixLift 297339
  have htrace : WordTrace (prefixWord ++ tailWord_297339) baseStart_297339 baseEnd_297339 := by
    simpa [prefixWord, tailWord_297339, baseEnd_297339] using wordTrace_append hprefix tailTrace_297339
  have hstable : (prefixWord ++ tailWord_297339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297339).length < 2 ^ (prefixWord ++ tailWord_297339).sum := by decide
  have hdescent : baseEnd_297339 < baseStart_297339 := by decide
  rcases family_descends (prefixWord ++ tailWord_297339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297341 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_297341 : Nat := 118140960795 + 297341 * 2 ^ 59
def prefixEnd_297341 : Nat := 4983230072969 + 3 ^ 40 * 297341 * 2
def baseEnd_297341 : Nat := 101785900859084257113373

theorem tailTrace_297341 : CollatzResearch.WordTrace tailWord_297341 prefixEnd_297341 101785900859084257113373 := by
  unfold tailWord_297341
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844917215791813644963877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7229944810527875763309251 10844917215791813644963877)
  ·
    refine ⟨2033421977960965058430727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10844917215791813644963877 2033421977960965058430727)
    ·
      refine ⟨3050132966941447587646091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033421977960965058430727 3050132966941447587646091)
      ·
        refine ⟨4575199450412171381469137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050132966941447587646091 4575199450412171381469137)
        ·
          refine ⟨3431399587809128536101853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575199450412171381469137 3431399587809128536101853)
          ·
            refine ⟨1286774845428423201038195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3431399587809128536101853 1286774845428423201038195)
            ·
              refine ⟨1930162268142634801557293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286774845428423201038195 1930162268142634801557293)
              ·
                refine ⟨723810850553488050583985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1930162268142634801557293 723810850553488050583985)
                ·
                  refine ⟨542858137915116037937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723810850553488050583985 542858137915116037937989)
                  ·
                    refine ⟨101785900859084257113373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542858137915116037937989 101785900859084257113373)
                    ·
                      rfl

theorem cell22_297341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_297341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297341 prefixEnd_297341 := by exact prefixLift 297341
  have htrace : WordTrace (prefixWord ++ tailWord_297341) baseStart_297341 baseEnd_297341 := by
    simpa [prefixWord, tailWord_297341, baseEnd_297341] using wordTrace_append hprefix tailTrace_297341
  have hstable : (prefixWord ++ tailWord_297341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297341).length < 2 ^ (prefixWord ++ tailWord_297341).sum := by decide
  have hdescent : baseEnd_297341 < baseStart_297341 := by decide
  rcases family_descends (prefixWord ++ tailWord_297341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297358 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_297358 : Nat := 118140960795 + 297358 * 2 ^ 59
def prefixEnd_297358 : Nat := 4983230072969 + 3 ^ 40 * 297358 * 2
def baseEnd_297358 : Nat := 101791720306501879438321

theorem tailTrace_297358 : CollatzResearch.WordTrace tailWord_297358 prefixEnd_297358 101791720306501879438321 := by
  unfold tailWord_297358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355692157091278193541591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7230358171153483698888485 1355692157091278193541591)
  ·
    refine ⟨2033538235636917290312387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355692157091278193541591 2033538235636917290312387)
    ·
      refine ⟨3050307353455375935468581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033538235636917290312387 3050307353455375935468581)
      ·
        refine ⟨571932628772882987900359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3050307353455375935468581 571932628772882987900359)
        ·
          refine ⟨857898943159324481850539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571932628772882987900359 857898943159324481850539)
          ·
            refine ⟨1286848414738986722775809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857898943159324481850539 1286848414738986722775809)
            ·
              refine ⟨965136311054240042081857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286848414738986722775809 965136311054240042081857)
              ·
                refine ⟨723852233290680031561393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965136311054240042081857 723852233290680031561393)
                ·
                  refine ⟨542889174968010023671045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723852233290680031561393 542889174968010023671045)
                  ·
                    refine ⟨101791720306501879438321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542889174968010023671045 101791720306501879438321)
                    ·
                      rfl

theorem cell22_297358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_297358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297358 prefixEnd_297358 := by exact prefixLift 297358
  have htrace : WordTrace (prefixWord ++ tailWord_297358) baseStart_297358 baseEnd_297358 := by
    simpa [prefixWord, tailWord_297358, baseEnd_297358] using wordTrace_append hprefix tailTrace_297358
  have hstable : (prefixWord ++ tailWord_297358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297358).length < 2 ^ (prefixWord ++ tailWord_297358).sum := by decide
  have hdescent : baseEnd_297358 < baseStart_297358 := by decide
  rcases family_descends (prefixWord ++ tailWord_297358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297369 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_297369 : Nat := 118140960795 + 297369 * 2 ^ 59
def prefixEnd_297369 : Nat := 4983230072969 + 3 ^ 40 * 297369 * 2
def baseEnd_297369 : Nat := 101795485831301517413287

theorem tailTrace_297369 : CollatzResearch.WordTrace tailWord_297369 prefixEnd_297369 101795485831301517413287 := by
  unfold tailWord_297369
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845938459690374426983161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7230625639793582951322107 10845938459690374426983161)
  ·
    refine ⟨8134453844767780820237371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10845938459690374426983161 8134453844767780820237371)
    ·
      refine ⟨12201680767151671230356057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8134453844767780820237371 12201680767151671230356057)
      ·
        refine ⟨9151260575363753422767043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12201680767151671230356057 9151260575363753422767043)
        ·
          refine ⟨13726890863045630134150565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9151260575363753422767043 13726890863045630134150565)
          ·
            refine ⟨2573792036821055650153231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13726890863045630134150565 2573792036821055650153231)
            ·
              refine ⟨3860688055231583475229847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573792036821055650153231 3860688055231583475229847)
              ·
                refine ⟨5791032082847375212844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860688055231583475229847 5791032082847375212844771)
                ·
                  refine ⟨8686548124271062819267157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791032082847375212844771 8686548124271062819267157)
                  ·
                    refine ⟨101795485831301517413287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8686548124271062819267157 101795485831301517413287)
                    ·
                      rfl

theorem cell22_297369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_297369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297369 prefixEnd_297369 := by exact prefixLift 297369
  have htrace : WordTrace (prefixWord ++ tailWord_297369) baseStart_297369 baseEnd_297369 := by
    simpa [prefixWord, tailWord_297369, baseEnd_297369] using wordTrace_append hprefix tailTrace_297369
  have hstable : (prefixWord ++ tailWord_297369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297369).length < 2 ^ (prefixWord ++ tailWord_297369).sum := by decide
  have hdescent : baseEnd_297369 < baseStart_297369 := by decide
  rcases family_descends (prefixWord ++ tailWord_297369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297373 : List Nat := [1, 4, 2, 1, 4, 2, 1, 7]
def baseStart_297373 : Nat := 118140960795 + 297373 * 2 ^ 59
def prefixEnd_297373 : Nat := 4983230072969 + 3 ^ 40 * 297373 * 2
def baseEnd_297373 : Nat := 11310761679227426701475

theorem tailTrace_297373 : CollatzResearch.WordTrace tailWord_297373 prefixEnd_297373 11310761679227426701475 := by
  unfold tailWord_297373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10846084351675883110128773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7230722901117255406752515 10846084351675883110128773)
  ·
    refine ⟨2033640815939228083149145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10846084351675883110128773 2033640815939228083149145)
    ·
      refine ⟨1525230611954421062361859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2033640815939228083149145 1525230611954421062361859)
      ·
        refine ⟨2287845917931631593542789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525230611954421062361859 2287845917931631593542789)
        ·
          refine ⟨428971109612180923789273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2287845917931631593542789 428971109612180923789273)
          ·
            refine ⟨321728332209135692841955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428971109612180923789273 321728332209135692841955)
            ·
              refine ⟨482592498313703539262933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321728332209135692841955 482592498313703539262933)
              ·
                refine ⟨11310761679227426701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 482592498313703539262933 11310761679227426701475)
                ·
                  rfl

theorem cell22_297373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 7].length) (baseStart_297373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297373 prefixEnd_297373 := by exact prefixLift 297373
  have htrace : WordTrace (prefixWord ++ tailWord_297373) baseStart_297373 baseEnd_297373 := by
    simpa [prefixWord, tailWord_297373, baseEnd_297373] using wordTrace_append hprefix tailTrace_297373
  have hstable : (prefixWord ++ tailWord_297373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297373).length < 2 ^ (prefixWord ++ tailWord_297373).sum := by decide
  have hdescent : baseEnd_297373 < baseStart_297373 := by decide
  rcases family_descends (prefixWord ++ tailWord_297373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297405 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_297405 : Nat := 118140960795 + 297405 * 2 ^ 59
def prefixEnd_297405 : Nat := 4983230072969 + 3 ^ 40 * 297405 * 2
def baseEnd_297405 : Nat := 101807809367009423513177

theorem tailTrace_297405 : CollatzResearch.WordTrace tailWord_297405 prefixEnd_297405 101807809367009423513177 := by
  unfold tailWord_297405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847251487559952575293669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7231500991706635050195779 10847251487559952575293669)
  ·
    refine ⟨2033859653917491107867563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10847251487559952575293669 2033859653917491107867563)
    ·
      refine ⟨3050789480876236661801345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033859653917491107867563 3050789480876236661801345)
      ·
        refine ⟨2288092110657177496351009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3050789480876236661801345 2288092110657177496351009)
        ·
          refine ⟨1716069082992883122263257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288092110657177496351009 1716069082992883122263257)
          ·
            refine ⟨1287051812244662341697443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716069082992883122263257 1287051812244662341697443)
            ·
              refine ⟨1930577718366993512546165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287051812244662341697443 1930577718366993512546165)
              ·
                refine ⟨180991661096905641801203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1930577718366993512546165 180991661096905641801203)
                ·
                  refine ⟨271487491645358462701805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180991661096905641801203 271487491645358462701805)
                  ·
                    refine ⟨101807809367009423513177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271487491645358462701805 101807809367009423513177)
                    ·
                      rfl

theorem cell22_297405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_297405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297405 prefixEnd_297405 := by exact prefixLift 297405
  have htrace : WordTrace (prefixWord ++ tailWord_297405) baseStart_297405 baseEnd_297405 := by
    simpa [prefixWord, tailWord_297405, baseEnd_297405] using wordTrace_append hprefix tailTrace_297405
  have hstable : (prefixWord ++ tailWord_297405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297405).length < 2 ^ (prefixWord ++ tailWord_297405).sum := by decide
  have hdescent : baseEnd_297405 < baseStart_297405 := by decide
  rcases family_descends (prefixWord ++ tailWord_297405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297416 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_297416 : Nat := 118140960795 + 297416 * 2 ^ 59
def prefixEnd_297416 : Nat := 4983230072969 + 3 ^ 40 * 297416 * 2
def baseEnd_297416 : Nat := 101811574891809061488143

theorem tailTrace_297416 : CollatzResearch.WordTrace tailWord_297416 prefixEnd_297416 101811574891809061488143 := by
  unfold tailWord_297416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423826345260050726972051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7231768460346734302629401 5423826345260050726972051)
  ·
    refine ⟨8135739517890076090458077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5423826345260050726972051 8135739517890076090458077)
    ·
      refine ⟨3050902319208778533921779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8135739517890076090458077 3050902319208778533921779)
      ·
        refine ⟨4576353478813167800882669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050902319208778533921779 4576353478813167800882669)
        ·
          refine ⟨1716132554554937925331001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4576353478813167800882669 1716132554554937925331001)
          ·
            refine ⟨1287099415916203443998251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716132554554937925331001 1287099415916203443998251)
            ·
              refine ⟨1930649123874305165997377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287099415916203443998251 1930649123874305165997377)
              ·
                refine ⟨1447986842905728874498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930649123874305165997377 1447986842905728874498033)
                ·
                  refine ⟨1085990132179296655873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447986842905728874498033 1085990132179296655873525)
                  ·
                    refine ⟨101811574891809061488143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1085990132179296655873525 101811574891809061488143)
                    ·
                      rfl

theorem cell22_297416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_297416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297416 prefixEnd_297416 := by exact prefixLift 297416
  have htrace : WordTrace (prefixWord ++ tailWord_297416) baseStart_297416 baseEnd_297416 := by
    simpa [prefixWord, tailWord_297416, baseEnd_297416] using wordTrace_append hprefix tailTrace_297416
  have hstable : (prefixWord ++ tailWord_297416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297416).length < 2 ^ (prefixWord ++ tailWord_297416).sum := by decide
  have hdescent : baseEnd_297416 < baseStart_297416 := by decide
  rcases family_descends (prefixWord ++ tailWord_297416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297448 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_297448 : Nat := 118140960795 + 297448 * 2 ^ 59
def prefixEnd_297448 : Nat := 4983230072969 + 3 ^ 40 * 297448 * 2
def baseEnd_297448 : Nat := 101822529145771644688045

theorem tailTrace_297448 : CollatzResearch.WordTrace tailWord_297448 prefixEnd_297448 101822529145771644688045 := by
  unfold tailWord_297448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424409913202085459554499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7232546550936113946072665 5424409913202085459554499)
  ·
    refine ⟨8136614869803128189331749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424409913202085459554499 8136614869803128189331749)
    ·
      refine ⟨1525615288088086535499703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8136614869803128189331749 1525615288088086535499703)
      ·
        refine ⟨2288422932132129803249555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525615288088086535499703 2288422932132129803249555)
        ·
          refine ⟨3432634398198194704874333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288422932132129803249555 3432634398198194704874333)
          ·
            refine ⟨1287237899324323014327875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3432634398198194704874333 1287237899324323014327875)
            ·
              refine ⟨1930856848986484521491813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287237899324323014327875 1930856848986484521491813)
              ·
                refine ⟨362035659184965847779715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1930856848986484521491813 362035659184965847779715)
                ·
                  refine ⟨543053488777448771669573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362035659184965847779715 543053488777448771669573)
                  ·
                    refine ⟨101822529145771644688045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 543053488777448771669573 101822529145771644688045)
                    ·
                      rfl

theorem cell22_297448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_297448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297448 prefixEnd_297448 := by exact prefixLift 297448
  have htrace : WordTrace (prefixWord ++ tailWord_297448) baseStart_297448 baseEnd_297448 := by
    simpa [prefixWord, tailWord_297448, baseEnd_297448] using wordTrace_append hprefix tailTrace_297448
  have hstable : (prefixWord ++ tailWord_297448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297448).length < 2 ^ (prefixWord ++ tailWord_297448).sum := by decide
  have hdescent : baseEnd_297448 < baseStart_297448 := by decide
  rcases family_descends (prefixWord ++ tailWord_297448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297491 : List Nat := [1, 1, 1, 2, 1, 5, 4, 7]
def baseStart_297491 : Nat := 118140960795 + 297491 * 2 ^ 59
def prefixEnd_297491 : Nat := 4983230072969 + 3 ^ 40 * 297491 * 2
def baseEnd_297491 : Nat := 11315249880503762873657

theorem tailTrace_297491 : CollatzResearch.WordTrace tailWord_297491 prefixEnd_297491 11315249880503762873657 := by
  unfold tailWord_297491
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850388165248389262924327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7233592110165592841949551 10850388165248389262924327)
  ·
    refine ⟨16275582247872583894386491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10850388165248389262924327 16275582247872583894386491)
    ·
      refine ⟨24413373371808875841579737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275582247872583894386491 24413373371808875841579737)
      ·
        refine ⟨18310030028856656881184803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24413373371808875841579737 18310030028856656881184803)
        ·
          refine ⟨27465045043284985321777205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18310030028856656881184803 27465045043284985321777205)
          ·
            refine ⟨2574847972807967373916613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27465045043284985321777205 2574847972807967373916613)
            ·
              refine ⟨482783994901493882609365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2574847972807967373916613 482783994901493882609365)
              ·
                refine ⟨11315249880503762873657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 482783994901493882609365 11315249880503762873657)
                ·
                  rfl

theorem cell22_297491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 7].length) (baseStart_297491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297491 prefixEnd_297491 := by exact prefixLift 297491
  have htrace : WordTrace (prefixWord ++ tailWord_297491) baseStart_297491 baseEnd_297491 := by
    simpa [prefixWord, tailWord_297491, baseEnd_297491] using wordTrace_append hprefix tailTrace_297491
  have hstable : (prefixWord ++ tailWord_297491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297491).length < 2 ^ (prefixWord ++ tailWord_297491).sum := by decide
  have hdescent : baseEnd_297491 < baseStart_297491 := by decide
  rcases family_descends (prefixWord ++ tailWord_297491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297536 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_297536 : Nat := 118140960795 + 297536 * 2 ^ 59
def prefixEnd_297536 : Nat := 4983230072969 + 3 ^ 40 * 297536 * 2
def baseEnd_297536 : Nat := 33950884448056249495925

theorem tailTrace_297536 : CollatzResearch.WordTrace tailWord_297536 prefixEnd_297536 33950884448056249495925 := by
  unfold tailWord_297536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5426014725042680974156231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7234686300056907965541641 5426014725042680974156231)
  ·
    refine ⟨8139022087564021461234347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5426014725042680974156231 8139022087564021461234347)
    ·
      refine ⟨12208533131346032191851521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8139022087564021461234347 12208533131346032191851521)
      ·
        refine ⟨9156399848509524143888641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12208533131346032191851521 9156399848509524143888641)
        ·
          refine ⟨6867299886382143107916481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9156399848509524143888641 6867299886382143107916481)
          ·
            refine ⟨5150474914786607330937361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6867299886382143107916481 5150474914786607330937361)
            ·
              refine ⟨3862856186089955498203021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5150474914786607330937361 3862856186089955498203021)
              ·
                refine ⟨1448571069783733311826133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3862856186089955498203021 1448571069783733311826133)
                ·
                  refine ⟨33950884448056249495925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1448571069783733311826133 33950884448056249495925)
                  ·
                    rfl

theorem cell22_297536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_297536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297536 prefixEnd_297536 := by exact prefixLift 297536
  have htrace : WordTrace (prefixWord ++ tailWord_297536) baseStart_297536 baseEnd_297536 := by
    simpa [prefixWord, tailWord_297536, baseEnd_297536] using wordTrace_append hprefix tailTrace_297536
  have hstable : (prefixWord ++ tailWord_297536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297536).length < 2 ^ (prefixWord ++ tailWord_297536).sum := by decide
  have hdescent : baseEnd_297536 < baseStart_297536 := by decide
  rcases family_descends (prefixWord ++ tailWord_297536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297542 : List Nat := [6, 1, 1, 1, 2, 3, 1, 7]
def baseStart_297542 : Nat := 118140960795 + 297542 * 2 ^ 59
def prefixEnd_297542 : Nat := 4983230072969 + 3 ^ 40 * 297542 * 2
def baseEnd_297542 : Nat := 11317189696309636981973

theorem tailTrace_297542 : CollatzResearch.WordTrace tailWord_297542 prefixEnd_297542 11317189696309636981973 := by
  unfold tailWord_297542
  simp only [CollatzResearch.WordTrace]
  refine ⟨339132759001988280407215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7234832192042416648687253 339132759001988280407215)
  ·
    refine ⟨508699138502982420610823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339132759001988280407215 508699138502982420610823)
    ·
      refine ⟨763048707754473630916235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508699138502982420610823 763048707754473630916235)
      ·
        refine ⟨1144573061631710446374353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763048707754473630916235 1144573061631710446374353)
        ·
          refine ⟨858429796223782834780765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1144573061631710446374353 858429796223782834780765)
          ·
            refine ⟨321911173583918563042787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 858429796223782834780765 321911173583918563042787)
            ·
              refine ⟨482866760375877844564181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321911173583918563042787 482866760375877844564181)
              ·
                refine ⟨11317189696309636981973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 482866760375877844564181 11317189696309636981973)
                ·
                  rfl

theorem cell22_297542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_297542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297542 prefixEnd_297542 := by exact prefixLift 297542
  have htrace : WordTrace (prefixWord ++ tailWord_297542) baseStart_297542 baseEnd_297542 := by
    simpa [prefixWord, tailWord_297542, baseEnd_297542] using wordTrace_append hprefix tailTrace_297542
  have hstable : (prefixWord ++ tailWord_297542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297542).length < 2 ^ (prefixWord ++ tailWord_297542).sum := by decide
  have hdescent : baseEnd_297542 < baseStart_297542 := by decide
  rcases family_descends (prefixWord ++ tailWord_297542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297551 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_297551 : Nat := 118140960795 + 297551 * 2 ^ 59
def prefixEnd_297551 : Nat := 4983230072969 + 3 ^ 40 * 297551 * 2
def baseEnd_297551 : Nat := 101857788150713709362729

theorem tailTrace_297551 : CollatzResearch.WordTrace tailWord_297551 prefixEnd_297551 101857788150713709362729 := by
  unfold tailWord_297551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852576545031019510108507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7235051030020679673405671 10852576545031019510108507)
  ·
    refine ⟨16278864817546529265162761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10852576545031019510108507 16278864817546529265162761)
    ·
      refine ⟨12209148613159896948872071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16278864817546529265162761 12209148613159896948872071)
      ·
        refine ⟨18313722919739845423308107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12209148613159896948872071 18313722919739845423308107)
        ·
          refine ⟨27470584379609768134962161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18313722919739845423308107 27470584379609768134962161)
          ·
            refine ⟨20602938284707326101221621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27470584379609768134962161 20602938284707326101221621)
            ·
              refine ⟨1931525464191311821989527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20602938284707326101221621 1931525464191311821989527)
              ·
                refine ⟨2897288196286967732984291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931525464191311821989527 2897288196286967732984291)
                ·
                  refine ⟨4345932294430451599476437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897288196286967732984291 4345932294430451599476437)
                  ·
                    refine ⟨101857788150713709362729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4345932294430451599476437 101857788150713709362729)
                    ·
                      rfl

theorem cell22_297551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_297551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297551 prefixEnd_297551 := by exact prefixLift 297551
  have htrace : WordTrace (prefixWord ++ tailWord_297551) baseStart_297551 baseEnd_297551 := by
    simpa [prefixWord, tailWord_297551, baseEnd_297551] using wordTrace_append hprefix tailTrace_297551
  have hstable : (prefixWord ++ tailWord_297551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297551).length < 2 ^ (prefixWord ++ tailWord_297551).sum := by decide
  have hdescent : baseEnd_297551 < baseStart_297551 := by decide
  rcases family_descends (prefixWord ++ tailWord_297551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297553 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 5]
def baseStart_297553 : Nat := 118140960795 + 297553 * 2 ^ 59
def prefixEnd_297553 : Nat := 4983230072969 + 3 ^ 40 * 297553 * 2
def baseEnd_297553 : Nat := 33952824263862123604241

theorem tailTrace_297553 : CollatzResearch.WordTrace tailWord_297553 prefixEnd_297553 33952824263862123604241 := by
  unfold tailWord_297553
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852649491023773851681313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7235099660682515901120875 10852649491023773851681313)
  ·
    refine ⟨8139487118267830388760985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10852649491023773851681313 8139487118267830388760985)
    ·
      refine ⟨6104615338700872791570739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8139487118267830388760985 6104615338700872791570739)
      ·
        refine ⟨9156923008051309187356109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6104615338700872791570739 9156923008051309187356109)
        ·
          refine ⟨3433846128019240945258541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9156923008051309187356109 3433846128019240945258541)
          ·
            refine ⟨1287692298007215354471953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3433846128019240945258541 1287692298007215354471953)
            ·
              refine ⟨965769223505411515853965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287692298007215354471953 965769223505411515853965)
              ·
                refine ⟨362163458814529318445237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965769223505411515853965 362163458814529318445237)
                ·
                  refine ⟨33952824263862123604241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 362163458814529318445237 33952824263862123604241)
                  ·
                    rfl

theorem cell22_297553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_297553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297553 prefixEnd_297553 := by exact prefixLift 297553
  have htrace : WordTrace (prefixWord ++ tailWord_297553) baseStart_297553 baseEnd_297553 := by
    simpa [prefixWord, tailWord_297553, baseEnd_297553] using wordTrace_append hprefix tailTrace_297553
  have hstable : (prefixWord ++ tailWord_297553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297553).length < 2 ^ (prefixWord ++ tailWord_297553).sum := by decide
  have hdescent : baseEnd_297553 < baseStart_297553 := by decide
  rcases family_descends (prefixWord ++ tailWord_297553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297630 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_297630 : Nat := 118140960795 + 297630 * 2 ^ 59
def prefixEnd_297630 : Nat := 4983230072969 + 3 ^ 40 * 297630 * 2
def baseEnd_297630 : Nat := 101884831465183836637487

theorem tailTrace_297630 : CollatzResearch.WordTrace tailWord_297630 prefixEnd_297630 101884831465183836637487 := by
  unfold tailWord_297630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356932238968102000279293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7236971941163210668156229 1356932238968102000279293)
  ·
    refine ⟨508849589613038250104735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1356932238968102000279293 508849589613038250104735)
    ·
      refine ⟨763274384419557375157103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508849589613038250104735 763274384419557375157103)
      ·
        refine ⟨1144911576629336062735655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763274384419557375157103 1144911576629336062735655)
        ·
          refine ⟨1717367364944004094103483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144911576629336062735655 1717367364944004094103483)
          ·
            refine ⟨2576051047416006141155225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717367364944004094103483 2576051047416006141155225)
            ·
              refine ⟨1932038285562004605866419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576051047416006141155225 1932038285562004605866419)
              ·
                refine ⟨2898057428343006908799629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932038285562004605866419 2898057428343006908799629)
                ·
                  refine ⟨1086771535628627590799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2898057428343006908799629 1086771535628627590799861)
                  ·
                    refine ⟨101884831465183836637487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1086771535628627590799861 101884831465183836637487)
                    ·
                      rfl

theorem cell22_297630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_297630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297630 prefixEnd_297630 := by exact prefixLift 297630
  have htrace : WordTrace (prefixWord ++ tailWord_297630) baseStart_297630 baseEnd_297630 := by
    simpa [prefixWord, tailWord_297630, baseEnd_297630] using wordTrace_append hprefix tailTrace_297630
  have hstable : (prefixWord ++ tailWord_297630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297630).length < 2 ^ (prefixWord ++ tailWord_297630).sum := by decide
  have hdescent : baseEnd_297630 < baseStart_297630 := by decide
  rcases family_descends (prefixWord ++ tailWord_297630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297645 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_297645 : Nat := 118140960795 + 297645 * 2 ^ 59
def prefixEnd_297645 : Nat := 4983230072969 + 3 ^ 40 * 297645 * 2
def baseEnd_297645 : Nat := 101889966271728797512441

theorem tailTrace_297645 : CollatzResearch.WordTrace tailWord_297645 prefixEnd_297645 101889966271728797512441 := by
  unfold tailWord_297645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856005006690473564030389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237336671126982376020259 10856005006690473564030389)
  ·
    refine ⟨1017750469377231896627849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10856005006690473564030389 1017750469377231896627849)
    ·
      refine ⟨763312852032923922470887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1017750469377231896627849 763312852032923922470887)
      ·
        refine ⟨1144969278049385883706331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763312852032923922470887 1144969278049385883706331)
        ·
          refine ⟨1717453917074078825559497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144969278049385883706331 1717453917074078825559497)
          ·
            refine ⟨1288090437805559119169623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717453917074078825559497 1288090437805559119169623)
            ·
              refine ⟨1932135656708338678754435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288090437805559119169623 1932135656708338678754435)
              ·
                refine ⟨2898203485062508018131653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932135656708338678754435 2898203485062508018131653)
                ·
                  refine ⟨543413153449220253399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2898203485062508018131653 543413153449220253399685)
                  ·
                    refine ⟨101889966271728797512441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 543413153449220253399685 101889966271728797512441)
                    ·
                      rfl

theorem cell22_297645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_297645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297645 prefixEnd_297645 := by exact prefixLift 297645
  have htrace : WordTrace (prefixWord ++ tailWord_297645) baseStart_297645 baseEnd_297645 := by
    simpa [prefixWord, tailWord_297645, baseEnd_297645] using wordTrace_append hprefix tailTrace_297645
  have hstable : (prefixWord ++ tailWord_297645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297645).length < 2 ^ (prefixWord ++ tailWord_297645).sum := by decide
  have hdescent : baseEnd_297645 < baseStart_297645 := by decide
  rcases family_descends (prefixWord ++ tailWord_297645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297649 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 6]
def baseStart_297649 : Nat := 118140960795 + 297649 * 2 ^ 59
def prefixEnd_297649 : Nat := 4983230072969 + 3 ^ 40 * 297649 * 2
def baseEnd_297649 : Nat := 33963778517824706804143

theorem tailTrace_297649 : CollatzResearch.WordTrace tailWord_297649 prefixEnd_297649 33963778517824706804143 := by
  unfold tailWord_297649
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856150898675982247176001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237433932450654831450667 10856150898675982247176001)
  ·
    refine ⟨8142113174006986685382001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10856150898675982247176001 8142113174006986685382001)
    ·
      refine ⟨6106584880505240014036501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8142113174006986685382001 6106584880505240014036501)
      ·
        refine ⟨286246166273683125657961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6106584880505240014036501 286246166273683125657961)
        ·
          refine ⟨214684624705262344243471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286246166273683125657961 214684624705262344243471)
          ·
            refine ⟨322026937057893516365207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214684624705262344243471 322026937057893516365207)
            ·
              refine ⟨483040405586840274547811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322026937057893516365207 483040405586840274547811)
              ·
                refine ⟨724560608380260411821717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483040405586840274547811 724560608380260411821717)
                ·
                  refine ⟨33963778517824706804143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 724560608380260411821717 33963778517824706804143)
                  ·
                    rfl

theorem cell22_297649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_297649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297649 prefixEnd_297649 := by exact prefixLift 297649
  have htrace : WordTrace (prefixWord ++ tailWord_297649) baseStart_297649 baseEnd_297649 := by
    simpa [prefixWord, tailWord_297649, baseEnd_297649] using wordTrace_append hprefix tailTrace_297649
  have hstable : (prefixWord ++ tailWord_297649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297649).length < 2 ^ (prefixWord ++ tailWord_297649).sum := by decide
  have hdescent : baseEnd_297649 < baseStart_297649 := by decide
  rcases family_descends (prefixWord ++ tailWord_297649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297664 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_297664 : Nat := 118140960795 + 297664 * 2 ^ 59
def prefixEnd_297664 : Nat := 4983230072969 + 3 ^ 40 * 297664 * 2
def baseEnd_297664 : Nat := 101896470360019081287383

theorem tailTrace_297664 : CollatzResearch.WordTrace tailWord_297664 prefixEnd_297664 101896470360019081287383 := by
  unfold tailWord_297664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428348996810819904486023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7237798662414426539314697 5428348996810819904486023)
  ·
    refine ⟨8142523495216229856729035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5428348996810819904486023 8142523495216229856729035)
    ·
      refine ⟨12213785242824344785093553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142523495216229856729035 12213785242824344785093553)
      ·
        refine ⟨9160338932118258588820165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12213785242824344785093553 9160338932118258588820165)
        ·
          refine ⟨1717563549772173485403781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9160338932118258588820165 1717563549772173485403781)
          ·
            refine ⟨322043165582282528513209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1717563549772173485403781 322043165582282528513209)
            ·
              refine ⟨241532374186711896384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322043165582282528513209 241532374186711896384907)
              ·
                refine ⟨362298561280067844577361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241532374186711896384907 362298561280067844577361)
                ·
                  refine ⟨271723920960050883433021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362298561280067844577361 271723920960050883433021)
                  ·
                    refine ⟨101896470360019081287383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271723920960050883433021 101896470360019081287383)
                    ·
                      rfl

theorem cell22_297664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_297664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297664 prefixEnd_297664 := by exact prefixLift 297664
  have htrace : WordTrace (prefixWord ++ tailWord_297664) baseStart_297664 baseEnd_297664 := by
    simpa [prefixWord, tailWord_297664, baseEnd_297664] using wordTrace_append hprefix tailTrace_297664
  have hstable : (prefixWord ++ tailWord_297664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297664).length < 2 ^ (prefixWord ++ tailWord_297664).sum := by decide
  have hdescent : baseEnd_297664 < baseStart_297664 := by decide
  rcases family_descends (prefixWord ++ tailWord_297664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297709 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_297709 : Nat := 118140960795 + 297709 * 2 ^ 59
def prefixEnd_297709 : Nat := 4983230072969 + 3 ^ 40 * 297709 * 2
def baseEnd_297709 : Nat := 101911874779653963912245

theorem tailTrace_297709 : CollatzResearch.WordTrace tailWord_297709 prefixEnd_297709 101911874779653963912245 := by
  unfold tailWord_297709
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858339278458612494360181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7238892852305741662906787 10858339278458612494360181)
  ·
    refine ⟨1017969307355494921346267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10858339278458612494360181 1017969307355494921346267)
    ·
      refine ⟨1526953961033242382019401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017969307355494921346267 1526953961033242382019401)
      ·
        refine ⟨1145215470774931786514551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1526953961033242382019401 1145215470774931786514551)
        ·
          refine ⟨1717823206162397679771827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145215470774931786514551 1717823206162397679771827)
          ·
            refine ⟨2576734809243596519657741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717823206162397679771827 2576734809243596519657741)
            ·
              refine ⟨966275553466348694871653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576734809243596519657741 966275553466348694871653)
              ·
                refine ⟨181176666274940380288435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 966275553466348694871653 181176666274940380288435)
                ·
                  refine ⟨271764999412410570432653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181176666274940380288435 271764999412410570432653)
                  ·
                    refine ⟨101911874779653963912245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271764999412410570432653 101911874779653963912245)
                    ·
                      rfl

theorem cell22_297709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_297709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297709 prefixEnd_297709 := by exact prefixLift 297709
  have htrace : WordTrace (prefixWord ++ tailWord_297709) baseStart_297709 baseEnd_297709 := by
    simpa [prefixWord, tailWord_297709, baseEnd_297709] using wordTrace_append hprefix tailTrace_297709
  have hstable : (prefixWord ++ tailWord_297709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297709).length < 2 ^ (prefixWord ++ tailWord_297709).sum := by decide
  have hdescent : baseEnd_297709 < baseStart_297709 := by decide
  rcases family_descends (prefixWord ++ tailWord_297709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297812 : List Nat := [2, 4, 1, 1, 4, 2, 8]
def baseStart_297812 : Nat := 118140960795 + 297812 * 2 ^ 59
def prefixEnd_297812 : Nat := 4983230072969 + 3 ^ 40 * 297812 * 2
def baseEnd_297812 : Nat := 3775819769799852910627

theorem tailTrace_297812 : CollatzResearch.WordTrace tailWord_297812 prefixEnd_297812 3775819769799852910627 := by
  unfold tailWord_297812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431047998542730542679845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7241397331390307390239793 5431047998542730542679845)
  ·
    refine ⟨1018321499726761976752471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5431047998542730542679845 1018321499726761976752471)
    ·
      refine ⟨1527482249590142965128707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018321499726761976752471 1527482249590142965128707)
      ·
        refine ⟨2291223374385214447693061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527482249590142965128707 2291223374385214447693061)
        ·
          refine ⟨429604382697227708942449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2291223374385214447693061 429604382697227708942449)
          ·
            refine ⟨322203287022920781706837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429604382697227708942449 322203287022920781706837)
            ·
              refine ⟨3775819769799852910627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 322203287022920781706837 3775819769799852910627)
              ·
                rfl

theorem cell22_297812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 8].length) (baseStart_297812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297812 prefixEnd_297812 := by exact prefixLift 297812
  have htrace : WordTrace (prefixWord ++ tailWord_297812) baseStart_297812 baseEnd_297812 := by
    simpa [prefixWord, tailWord_297812, baseEnd_297812] using wordTrace_append hprefix tailTrace_297812
  have hstable : (prefixWord ++ tailWord_297812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297812).length < 2 ^ (prefixWord ++ tailWord_297812).sum := by decide
  have hdescent : baseEnd_297812 < baseStart_297812 := by decide
  rcases family_descends (prefixWord ++ tailWord_297812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297887 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_297887 : Nat := 118140960795 + 297887 * 2 ^ 59
def prefixEnd_297887 : Nat := 4983230072969 + 3 ^ 40 * 297887 * 2
def baseEnd_297887 : Nat := 101972807817320832961699

theorem tailTrace_297887 : CollatzResearch.WordTrace tailWord_297887 prefixEnd_297887 101972807817320832961699 := by
  unfold tailWord_297887
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864831471813748894339915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243220981209165929559943 10864831471813748894339915)
  ·
    refine ⟨16297247207720623341509873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10864831471813748894339915 16297247207720623341509873)
    ·
      refine ⟨12222935405790467506132405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16297247207720623341509873 12222935405790467506132405)
      ·
        refine ⟨1145900194292856328699913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12222935405790467506132405 1145900194292856328699913)
        ·
          refine ⟨859425145719642246524935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1145900194292856328699913 859425145719642246524935)
          ·
            refine ⟨1289137718579463369787403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859425145719642246524935 1289137718579463369787403)
            ·
              refine ⟨1933706577869195054681105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289137718579463369787403 1933706577869195054681105)
              ·
                refine ⟨1450279933401896291010829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933706577869195054681105 1450279933401896291010829)
                ·
                  refine ⟨543854975025711109129061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1450279933401896291010829 543854975025711109129061)
                  ·
                    refine ⟨101972807817320832961699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 543854975025711109129061 101972807817320832961699)
                    ·
                      rfl

theorem cell22_297887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_297887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297887 prefixEnd_297887 := by exact prefixLift 297887
  have htrace : WordTrace (prefixWord ++ tailWord_297887) baseStart_297887 baseEnd_297887 := by
    simpa [prefixWord, tailWord_297887, baseEnd_297887] using wordTrace_append hprefix tailTrace_297887
  have hstable : (prefixWord ++ tailWord_297887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297887).length < 2 ^ (prefixWord ++ tailWord_297887).sum := by decide
  have hdescent : baseEnd_297887 < baseStart_297887 := by decide
  rcases family_descends (prefixWord ++ tailWord_297887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297900 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_297900 : Nat := 118140960795 + 297900 * 2 ^ 59
def prefixEnd_297900 : Nat := 4983230072969 + 3 ^ 40 * 297900 * 2
def baseEnd_297900 : Nat := 101977257982993132386659

theorem tailTrace_297900 : CollatzResearch.WordTrace tailWord_297900 prefixEnd_297900 101977257982993132386659 := by
  unfold tailWord_297900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432652810383326057281577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7243537080511101409708769 5432652810383326057281577)
  ·
    refine ⟨4074489607787494542961183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5432652810383326057281577 4074489607787494542961183)
    ·
      refine ⟨6111734411681241814441775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074489607787494542961183 6111734411681241814441775)
      ·
        refine ⟨9167601617521862721662663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111734411681241814441775 9167601617521862721662663)
        ·
          refine ⟨13751402426282794082493995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9167601617521862721662663 13751402426282794082493995)
          ·
            refine ⟨20627103639424191123740993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13751402426282794082493995 20627103639424191123740993)
            ·
              refine ⟨15470327729568143342805745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20627103639424191123740993 15470327729568143342805745)
              ·
                refine ⟨11602745797176107507104309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15470327729568143342805745 11602745797176107507104309)
                ·
                  refine ⟨1087757418485260078791029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11602745797176107507104309 1087757418485260078791029)
                  ·
                    refine ⟨101977257982993132386659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1087757418485260078791029 101977257982993132386659)
                    ·
                      rfl

theorem cell22_297900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_297900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297900 prefixEnd_297900 := by exact prefixLift 297900
  have htrace : WordTrace (prefixWord ++ tailWord_297900) baseStart_297900 baseEnd_297900 := by
    simpa [prefixWord, tailWord_297900, baseEnd_297900] using wordTrace_append hprefix tailTrace_297900
  have hstable : (prefixWord ++ tailWord_297900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297900).length < 2 ^ (prefixWord ++ tailWord_297900).sum := by decide
  have hdescent : baseEnd_297900 < baseStart_297900 := by decide
  rcases family_descends (prefixWord ++ tailWord_297900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297932 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_297932 : Nat := 118140960795 + 297932 * 2 ^ 59
def prefixEnd_297932 : Nat := 4983230072969 + 3 ^ 40 * 297932 * 2
def baseEnd_297932 : Nat := 101988212236955715586561

theorem tailTrace_297932 : CollatzResearch.WordTrace tailWord_297932 prefixEnd_297932 101988212236955715586561 := by
  unfold tailWord_297932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433236378325360789864025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7244315171100481053152033 5433236378325360789864025)
  ·
    refine ⟨4074927283744020592398019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5433236378325360789864025 4074927283744020592398019)
    ·
      refine ⟨6112390925616030888597029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074927283744020592398019 6112390925616030888597029)
      ·
        refine ⟨1146073298553005791611943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6112390925616030888597029 1146073298553005791611943)
        ·
          refine ⟨1719109947829508687417915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146073298553005791611943 1719109947829508687417915)
          ·
            refine ⟨2578664921744263031126873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719109947829508687417915 2578664921744263031126873)
            ·
              refine ⟨1933998691308197273345155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2578664921744263031126873 1933998691308197273345155)
              ·
                refine ⟨2900998036962295910017733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933998691308197273345155 2900998036962295910017733)
                ·
                  refine ⟨543937131930430483128325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2900998036962295910017733 543937131930430483128325)
                  ·
                    refine ⟨101988212236955715586561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 543937131930430483128325 101988212236955715586561)
                    ·
                      rfl

theorem cell22_297932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_297932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297932 prefixEnd_297932 := by exact prefixLift 297932
  have htrace : WordTrace (prefixWord ++ tailWord_297932) baseStart_297932 baseEnd_297932 := by
    simpa [prefixWord, tailWord_297932, baseEnd_297932] using wordTrace_append hprefix tailTrace_297932
  have hstable : (prefixWord ++ tailWord_297932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297932).length < 2 ^ (prefixWord ++ tailWord_297932).sum := by decide
  have hdescent : baseEnd_297932 < baseStart_297932 := by decide
  rcases family_descends (prefixWord ++ tailWord_297932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297934 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_297934 : Nat := 118140960795 + 297934 * 2 ^ 59
def prefixEnd_297934 : Nat := 4983230072969 + 3 ^ 40 * 297934 * 2
def baseEnd_297934 : Nat := 101988896877828377036555

theorem tailTrace_297934 : CollatzResearch.WordTrace tailWord_297934 prefixEnd_297934 101988896877828377036555 := by
  unfold tailWord_297934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358318212830434490162607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7244363801762317280867237 1358318212830434490162607)
  ·
    refine ⟨2037477319245651735243911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358318212830434490162607 2037477319245651735243911)
    ·
      refine ⟨3056215978868477602865867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037477319245651735243911 3056215978868477602865867)
      ·
        refine ⟨4584323968302716404298801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056215978868477602865867 4584323968302716404298801)
        ·
          refine ⟨3438242976227037303224101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4584323968302716404298801 3438242976227037303224101)
          ·
            refine ⟨644670558042569494354519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3438242976227037303224101 644670558042569494354519)
            ·
              refine ⟨967005837063854241531779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644670558042569494354519 967005837063854241531779)
              ·
                refine ⟨1450508755595781362297669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967005837063854241531779 1450508755595781362297669)
                ·
                  refine ⟨271970391674209005430813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450508755595781362297669 271970391674209005430813)
                  ·
                    refine ⟨101988896877828377036555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271970391674209005430813 101988896877828377036555)
                    ·
                      rfl

theorem cell22_297934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_297934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297934 prefixEnd_297934 := by exact prefixLift 297934
  have htrace : WordTrace (prefixWord ++ tailWord_297934) baseStart_297934 baseEnd_297934 := by
    simpa [prefixWord, tailWord_297934, baseEnd_297934] using wordTrace_append hprefix tailTrace_297934
  have hstable : (prefixWord ++ tailWord_297934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297934).length < 2 ^ (prefixWord ++ tailWord_297934).sum := by decide
  have hdescent : baseEnd_297934 < baseStart_297934 := by decide
  rcases family_descends (prefixWord ++ tailWord_297934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297951 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 5]
def baseStart_297951 : Nat := 118140960795 + 297951 * 2 ^ 59
def prefixEnd_297951 : Nat := 4983230072969 + 3 ^ 40 * 297951 * 2
def baseEnd_297951 : Nat := 101994716325245999361503

theorem tailTrace_297951 : CollatzResearch.WordTrace tailWord_297951 prefixEnd_297951 101994716325245999361503 := by
  unfold tailWord_297951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867165743581887824669707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7244777162387925216446471 10867165743581887824669707)
  ·
    refine ⟨16300748615372831737004561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10867165743581887824669707 16300748615372831737004561)
    ·
      refine ⟨12225561461529623802753421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16300748615372831737004561 12225561461529623802753421)
      ·
        refine ⟨4584585548073608926032533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12225561461529623802753421 4584585548073608926032533)
        ·
          refine ⟨214902447565950418407775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4584585548073608926032533 214902447565950418407775)
          ·
            refine ⟨322353671348925627611663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214902447565950418407775 322353671348925627611663)
            ·
              refine ⟨483530507023388441417495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322353671348925627611663 483530507023388441417495)
              ·
                refine ⟨725295760535082662126243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483530507023388441417495 725295760535082662126243)
                ·
                  refine ⟨1087943640802623993189365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725295760535082662126243 1087943640802623993189365)
                  ·
                    refine ⟨101994716325245999361503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1087943640802623993189365 101994716325245999361503)
                    ·
                      rfl

theorem cell22_297951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_297951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297951 prefixEnd_297951 := by exact prefixLift 297951
  have htrace : WordTrace (prefixWord ++ tailWord_297951) baseStart_297951 baseEnd_297951 := by
    simpa [prefixWord, tailWord_297951, baseEnd_297951] using wordTrace_append hprefix tailTrace_297951
  have hstable : (prefixWord ++ tailWord_297951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297951).length < 2 ^ (prefixWord ++ tailWord_297951).sum := by decide
  have hdescent : baseEnd_297951 < baseStart_297951 := by decide
  rcases family_descends (prefixWord ++ tailWord_297951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297970 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_297970 : Nat := 118140960795 + 297970 * 2 ^ 59
def prefixEnd_297970 : Nat := 4983230072969 + 3 ^ 40 * 297970 * 2
def baseEnd_297970 : Nat := 34000406804512094378815

theorem tailTrace_297970 : CollatzResearch.WordTrace tailWord_297970 prefixEnd_297970 34000406804512094378815 := by
  unfold tailWord_297970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716964682628263517402841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7245239153675369379740909 2716964682628263517402841)
  ·
    refine ⟨2037723511971197638052131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2716964682628263517402841 2037723511971197638052131)
    ·
      refine ⟨3056585267956796457078197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037723511971197638052131 3056585267956796457078197)
      ·
        refine ⟨286554868870949667851081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3056585267956796457078197 286554868870949667851081)
        ·
          refine ⟨214916151653212250888311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286554868870949667851081 214916151653212250888311)
          ·
            refine ⟨322374227479818376332467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214916151653212250888311 322374227479818376332467)
            ·
              refine ⟨483561341219727564498701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322374227479818376332467 483561341219727564498701)
              ·
                refine ⟨181335502957397836687013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483561341219727564498701 181335502957397836687013)
                ·
                  refine ⟨34000406804512094378815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181335502957397836687013 34000406804512094378815)
                  ·
                    rfl

theorem cell22_297970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_297970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297970 prefixEnd_297970 := by exact prefixLift 297970
  have htrace : WordTrace (prefixWord ++ tailWord_297970) baseStart_297970 baseEnd_297970 := by
    simpa [prefixWord, tailWord_297970, baseEnd_297970] using wordTrace_append hprefix tailTrace_297970
  have hstable : (prefixWord ++ tailWord_297970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297970).length < 2 ^ (prefixWord ++ tailWord_297970).sum := by decide
  have hdescent : baseEnd_297970 < baseStart_297970 := by decide
  rcases family_descends (prefixWord ++ tailWord_297970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297992 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 7]
def baseStart_297992 : Nat := 118140960795 + 297992 * 2 ^ 59
def prefixEnd_297992 : Nat := 4983230072969 + 3 ^ 40 * 297992 * 2
def baseEnd_297992 : Nat := 34002917154378519695459

theorem tailTrace_297992 : CollatzResearch.WordTrace tailWord_297992 prefixEnd_297992 34002917154378519695459 := by
  unfold tailWord_297992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434330568216675913456115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7245774090955567884608153 5434330568216675913456115)
  ·
    refine ⟨8151495852325013870184173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5434330568216675913456115 8151495852325013870184173)
    ·
      refine ⟨3056810944621880201319065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8151495852325013870184173 3056810944621880201319065)
      ·
        refine ⟨2292608208466410150989299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3056810944621880201319065 2292608208466410150989299)
        ·
          refine ⟨3438912312699615226483949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292608208466410150989299 3438912312699615226483949)
          ·
            refine ⟨1289592117262355709931481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3438912312699615226483949 1289592117262355709931481)
            ·
              refine ⟨967194087946766782448611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289592117262355709931481 967194087946766782448611)
              ·
                refine ⟨1450791131920150173672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967194087946766782448611 1450791131920150173672917)
                ·
                  refine ⟨34002917154378519695459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1450791131920150173672917 34002917154378519695459)
                  ·
                    rfl

theorem cell22_297992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_297992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297992 prefixEnd_297992 := by exact prefixLift 297992
  have htrace : WordTrace (prefixWord ++ tailWord_297992) baseStart_297992 baseEnd_297992 := by
    simpa [prefixWord, tailWord_297992, baseEnd_297992] using wordTrace_append hprefix tailTrace_297992
  have hstable : (prefixWord ++ tailWord_297992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297992).length < 2 ^ (prefixWord ++ tailWord_297992).sum := by decide
  have hdescent : baseEnd_297992 < baseStart_297992 := by decide
  rcases family_descends (prefixWord ++ tailWord_297992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297996 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_297996 : Nat := 118140960795 + 297996 * 2 ^ 59
def prefixEnd_297996 : Nat := 4983230072969 + 3 ^ 40 * 297996 * 2
def baseEnd_297996 : Nat := 102010120744880881986365

theorem tailTrace_297996 : CollatzResearch.WordTrace tailWord_297996 prefixEnd_297996 102010120744880881986365 := by
  unfold tailWord_297996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434403514209430255028921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7245871352279240340038561 5434403514209430255028921)
  ·
    refine ⟨4075802635657072691271691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5434403514209430255028921 4075802635657072691271691)
    ·
      refine ⟨6113703953485609036907537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075802635657072691271691 6113703953485609036907537)
      ·
        refine ⟨4585277965114206777680653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6113703953485609036907537 4585277965114206777680653)
        ·
          refine ⟨1719479236917827541630245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4585277965114206777680653 1719479236917827541630245)
          ·
            refine ⟨322402356922092664055671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1719479236917827541630245 322402356922092664055671)
            ·
              refine ⟨483603535383138996083507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322402356922092664055671 483603535383138996083507)
              ·
                refine ⟨725405303074708494125261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483603535383138996083507 725405303074708494125261)
                ·
                  refine ⟨272026988653015685296973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725405303074708494125261 272026988653015685296973)
                  ·
                    refine ⟨102010120744880881986365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272026988653015685296973 102010120744880881986365)
                    ·
                      rfl

theorem cell22_297996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_297996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_297996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_297996 prefixEnd_297996 := by exact prefixLift 297996
  have htrace : WordTrace (prefixWord ++ tailWord_297996) baseStart_297996 baseEnd_297996 := by
    simpa [prefixWord, tailWord_297996, baseEnd_297996] using wordTrace_append hprefix tailTrace_297996
  have hstable : (prefixWord ++ tailWord_297996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297996).length < 2 ^ (prefixWord ++ tailWord_297996).sum := by decide
  have hdescent : baseEnd_297996 < baseStart_297996 := by decide
  rcases family_descends (prefixWord ++ tailWord_297996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298009 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 5]
def baseStart_298009 : Nat := 118140960795 + 298009 * 2 ^ 59
def prefixEnd_298009 : Nat := 4983230072969 + 3 ^ 40 * 298009 * 2
def baseEnd_298009 : Nat := 34004856970184393803775

theorem tailTrace_298009 : CollatzResearch.WordTrace tailWord_298009 prefixEnd_298009 34004856970184393803775 := by
  unfold tailWord_298009
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869281177371763730281081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246187451581175820187387 10869281177371763730281081)
  ·
    refine ⟨8151960883028822797710811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10869281177371763730281081 8151960883028822797710811)
    ·
      refine ⟨12227941324543234196566217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8151960883028822797710811 12227941324543234196566217)
      ·
        refine ⟨9170955993407425647424663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12227941324543234196566217 9170955993407425647424663)
        ·
          refine ⟨13756433990111138471136995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170955993407425647424663 13756433990111138471136995)
          ·
            refine ⟨20634650985166707706705493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756433990111138471136995 20634650985166707706705493)
            ·
              refine ⟨241812316232422355937955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 20634650985166707706705493 241812316232422355937955)
              ·
                refine ⟨362718474348633533906933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241812316232422355937955 362718474348633533906933)
                ·
                  refine ⟨34004856970184393803775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 362718474348633533906933 34004856970184393803775)
                  ·
                    rfl

theorem cell22_298009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_298009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298009 prefixEnd_298009 := by exact prefixLift 298009
  have htrace : WordTrace (prefixWord ++ tailWord_298009) baseStart_298009 baseEnd_298009 := by
    simpa [prefixWord, tailWord_298009, baseEnd_298009] using wordTrace_append hprefix tailTrace_298009
  have hstable : (prefixWord ++ tailWord_298009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298009).length < 2 ^ (prefixWord ++ tailWord_298009).sum := by decide
  have hdescent : baseEnd_298009 < baseStart_298009 := by decide
  rcases family_descends (prefixWord ++ tailWord_298009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_298067 : Nat := 118140960795 + 298067 * 2 ^ 59
def prefixEnd_298067 : Nat := 4983230072969 + 3 ^ 40 * 298067 * 2
def baseEnd_298067 : Nat := 102034425495860363461147

theorem tailTrace_298067 : CollatzResearch.WordTrace tailWord_298067 prefixEnd_298067 102034425495860363461147 := by
  unfold tailWord_298067
  simp only [CollatzResearch.WordTrace]
  refine ⟨10871396611161639635892455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7247597740774426423928303 10871396611161639635892455)
  ·
    refine ⟨16307094916742459453838683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10871396611161639635892455 16307094916742459453838683)
    ·
      refine ⟨24460642375113689180758025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16307094916742459453838683 24460642375113689180758025)
      ·
        refine ⟨18345481781335266885568519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24460642375113689180758025 18345481781335266885568519)
        ·
          refine ⟨27518222672002900328352779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18345481781335266885568519 27518222672002900328352779)
          ·
            refine ⟨41277334008004350492529169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27518222672002900328352779 41277334008004350492529169)
            ·
              refine ⟨30958000506003262869396877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41277334008004350492529169 30958000506003262869396877)
              ·
                refine ⟨11609250189751223576023829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30958000506003262869396877 11609250189751223576023829)
                ·
                  refine ⟨544183602644588605126117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11609250189751223576023829 544183602644588605126117)
                  ·
                    refine ⟨102034425495860363461147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544183602644588605126117 102034425495860363461147)
                    ·
                      rfl

theorem cell22_298067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_298067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298067 prefixEnd_298067 := by exact prefixLift 298067
  have htrace : WordTrace (prefixWord ++ tailWord_298067) baseStart_298067 baseEnd_298067 := by
    simpa [prefixWord, tailWord_298067, baseEnd_298067] using wordTrace_append hprefix tailTrace_298067
  have hstable : (prefixWord ++ tailWord_298067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298067).length < 2 ^ (prefixWord ++ tailWord_298067).sum := by decide
  have hdescent : baseEnd_298067 < baseStart_298067 := by decide
  rcases family_descends (prefixWord ++ tailWord_298067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298069 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_298069 : Nat := 118140960795 + 298069 * 2 ^ 59
def prefixEnd_298069 : Nat := 4983230072969 + 3 ^ 40 * 298069 * 2
def baseEnd_298069 : Nat := 102035110136733024911141

theorem tailTrace_298069 : CollatzResearch.WordTrace tailWord_298069 prefixEnd_298069 102035110136733024911141 := by
  unfold tailWord_298069
  simp only [CollatzResearch.WordTrace]
  refine ⟨10871469557154393977465261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7247646371436262651643507 10871469557154393977465261)
  ·
    refine ⟨4076801083932897741549473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10871469557154393977465261 4076801083932897741549473)
    ·
      refine ⟨3057600812949673306162105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4076801083932897741549473 3057600812949673306162105)
      ·
        refine ⟨2293200609712254979621579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057600812949673306162105 2293200609712254979621579)
        ·
          refine ⟨3439800914568382469432369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293200609712254979621579 3439800914568382469432369)
          ·
            refine ⟨2579850685926286852074277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439800914568382469432369 2579850685926286852074277)
            ·
              refine ⟨483722003611178784763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2579850685926286852074277 483722003611178784763927)
              ·
                refine ⟨725583005416768177145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483722003611178784763927 725583005416768177145891)
                ·
                  refine ⟨1088374508125152265718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725583005416768177145891 1088374508125152265718837)
                  ·
                    refine ⟨102035110136733024911141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1088374508125152265718837 102035110136733024911141)
                    ·
                      rfl

theorem cell22_298069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_298069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298069 prefixEnd_298069 := by exact prefixLift 298069
  have htrace : WordTrace (prefixWord ++ tailWord_298069) baseStart_298069 baseEnd_298069 := by
    simpa [prefixWord, tailWord_298069, baseEnd_298069] using wordTrace_append hprefix tailTrace_298069
  have hstable : (prefixWord ++ tailWord_298069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298069).length < 2 ^ (prefixWord ++ tailWord_298069).sum := by decide
  have hdescent : baseEnd_298069 < baseStart_298069 := by decide
  rcases family_descends (prefixWord ++ tailWord_298069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298112 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_298112 : Nat := 118140960795 + 298112 * 2 ^ 59
def prefixEnd_298112 : Nat := 4983230072969 + 3 ^ 40 * 298112 * 2
def baseEnd_298112 : Nat := 102049829915495246086009

theorem tailTrace_298112 : CollatzResearch.WordTrace tailWord_298112 prefixEnd_298112 102049829915495246086009 := by
  unfold tailWord_298112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436518947999306160640295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7248691930665741547520393 5436518947999306160640295)
  ·
    refine ⟨8154778421998959240960443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436518947999306160640295 8154778421998959240960443)
    ·
      refine ⟨12232167632998438861440665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8154778421998959240960443 12232167632998438861440665)
      ·
        refine ⟨9174125724748829146080499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12232167632998438861440665 9174125724748829146080499)
        ·
          refine ⟨13761188587123243719120749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174125724748829146080499 13761188587123243719120749)
          ·
            refine ⟨5160445720171216394670281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13761188587123243719120749 5160445720171216394670281)
            ·
              refine ⟨3870334290128412296002711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160445720171216394670281 3870334290128412296002711)
              ·
                refine ⟨5805501435192618444004067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870334290128412296002711 5805501435192618444004067)
                ·
                  refine ⟨8708252152788927666006101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5805501435192618444004067 8708252152788927666006101)
                  ·
                    refine ⟨102049829915495246086009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8708252152788927666006101 102049829915495246086009)
                    ·
                      rfl

theorem cell22_298112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_298112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298112 prefixEnd_298112 := by exact prefixLift 298112
  have htrace : WordTrace (prefixWord ++ tailWord_298112) baseStart_298112 baseEnd_298112 := by
    simpa [prefixWord, tailWord_298112, baseEnd_298112] using wordTrace_append hprefix tailTrace_298112
  have hstable : (prefixWord ++ tailWord_298112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298112).length < 2 ^ (prefixWord ++ tailWord_298112).sum := by decide
  have hdescent : baseEnd_298112 < baseStart_298112 := by decide
  rcases family_descends (prefixWord ++ tailWord_298112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298120 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_298120 : Nat := 118140960795 + 298120 * 2 ^ 59
def prefixEnd_298120 : Nat := 4983230072969 + 3 ^ 40 * 298120 * 2
def baseEnd_298120 : Nat := 102052568478985891885985

theorem tailTrace_298120 : CollatzResearch.WordTrace tailWord_298120 prefixEnd_298120 102052568478985891885985 := by
  unfold tailWord_298120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436664839984814843785907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7248886453313086458381209 5436664839984814843785907)
  ·
    refine ⟨8154997259977222265678861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436664839984814843785907 8154997259977222265678861)
    ·
      refine ⟨3058123972491458349629573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8154997259977222265678861 3058123972491458349629573)
      ·
        refine ⟨573398244842148440555545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3058123972491458349629573 573398244842148440555545)
        ·
          refine ⟨430048683631611330416659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 573398244842148440555545 430048683631611330416659)
          ·
            refine ⟨645073025447416995624989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430048683631611330416659 645073025447416995624989)
            ·
              refine ⟨241902384542781373359371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645073025447416995624989 241902384542781373359371)
              ·
                refine ⟨362853576814172060039057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241902384542781373359371 362853576814172060039057)
                ·
                  refine ⟨272140182610629045029293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362853576814172060039057 272140182610629045029293)
                  ·
                    refine ⟨102052568478985891885985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272140182610629045029293 102052568478985891885985)
                    ·
                      rfl

theorem cell22_298120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_298120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298120 prefixEnd_298120 := by exact prefixLift 298120
  have htrace : WordTrace (prefixWord ++ tailWord_298120) baseStart_298120 baseEnd_298120 := by
    simpa [prefixWord, tailWord_298120, baseEnd_298120] using wordTrace_append hprefix tailTrace_298120
  have hstable : (prefixWord ++ tailWord_298120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298120).length < 2 ^ (prefixWord ++ tailWord_298120).sum := by decide
  have hdescent : baseEnd_298120 < baseStart_298120 := by decide
  rcases family_descends (prefixWord ++ tailWord_298120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298208 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_298208 : Nat := 118140960795 + 298208 * 2 ^ 59
def prefixEnd_298208 : Nat := 4983230072969 + 3 ^ 40 * 298208 * 2
def baseEnd_298208 : Nat := 102082692677382995685715

theorem tailTrace_298208 : CollatzResearch.WordTrace tailWord_298208 prefixEnd_298208 102082692677382995685715 := by
  unfold tailWord_298208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438269651825410358387639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7251026202433880477850185 5438269651825410358387639)
  ·
    refine ⟨8157404477738115537581459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5438269651825410358387639 8157404477738115537581459)
    ·
      refine ⟨12236106716607173306372189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8157404477738115537581459 12236106716607173306372189)
      ·
        refine ⟨4588540018727689989889571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12236106716607173306372189 4588540018727689989889571)
        ·
          refine ⟨6882810028091534984834357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588540018727689989889571 6882810028091534984834357)
          ·
            refine ⟨645263440133581404828221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6882810028091534984834357 645263440133581404828221)
            ·
              refine ⟨241973790050093026810583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645263440133581404828221 241973790050093026810583)
              ·
                refine ⟨362960685075139540215875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241973790050093026810583 362960685075139540215875)
                ·
                  refine ⟨544441027612709310323813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362960685075139540215875 544441027612709310323813)
                  ·
                    refine ⟨102082692677382995685715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 544441027612709310323813 102082692677382995685715)
                    ·
                      rfl

theorem cell22_298208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_298208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298208 prefixEnd_298208 := by exact prefixLift 298208
  have htrace : WordTrace (prefixWord ++ tailWord_298208) baseStart_298208 baseEnd_298208 := by
    simpa [prefixWord, tailWord_298208, baseEnd_298208] using wordTrace_append hprefix tailTrace_298208
  have hstable : (prefixWord ++ tailWord_298208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298208).length < 2 ^ (prefixWord ++ tailWord_298208).sum := by decide
  have hdescent : baseEnd_298208 < baseStart_298208 := by decide
  rcases family_descends (prefixWord ++ tailWord_298208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298223 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 4]
def baseStart_298223 : Nat := 118140960795 + 298223 * 2 ^ 59
def prefixEnd_298223 : Nat := 4983230072969 + 3 ^ 40 * 298223 * 2
def baseEnd_298223 : Nat := 34029275827975985520223

theorem tailTrace_298223 : CollatzResearch.WordTrace tailWord_298223 prefixEnd_298223 34029275827975985520223 := by
  unfold tailWord_298223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877086398596478278571323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7251390932397652185714215 10877086398596478278571323)
  ·
    refine ⟨16315629597894717417856985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10877086398596478278571323 16315629597894717417856985)
    ·
      refine ⟨12236722198421038063392739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16315629597894717417856985 12236722198421038063392739)
      ·
        refine ⟨18355083297631557095089109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12236722198421038063392739 18355083297631557095089109)
        ·
          refine ⟨430197264788239619416151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18355083297631557095089109 430197264788239619416151)
          ·
            refine ⟨645295897182359429124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430197264788239619416151 645295897182359429124227)
            ·
              refine ⟨967943845773539143686341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645295897182359429124227 967943845773539143686341)
              ·
                refine ⟨181489471082538589441189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 967943845773539143686341 181489471082538589441189)
                ·
                  refine ⟨34029275827975985520223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181489471082538589441189 34029275827975985520223)
                  ·
                    rfl

theorem cell22_298223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 4].length) (baseStart_298223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298223 prefixEnd_298223 := by exact prefixLift 298223
  have htrace : WordTrace (prefixWord ++ tailWord_298223) baseStart_298223 baseEnd_298223 := by
    simpa [prefixWord, tailWord_298223, baseEnd_298223] using wordTrace_append hprefix tailTrace_298223
  have hstable : (prefixWord ++ tailWord_298223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298223).length < 2 ^ (prefixWord ++ tailWord_298223).sum := by decide
  have hdescent : baseEnd_298223 < baseStart_298223 := by decide
  rcases family_descends (prefixWord ++ tailWord_298223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298238 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_298238 : Nat := 118140960795 + 298238 * 2 ^ 59
def prefixEnd_298238 : Nat := 4983230072969 + 3 ^ 40 * 298238 * 2
def baseEnd_298238 : Nat := 102092962290472917435623

theorem tailTrace_298238 : CollatzResearch.WordTrace tailWord_298238 prefixEnd_298238 102092962290472917435623 := by
  unfold tailWord_298238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359704186692766980045921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7251755662361423893578245 1359704186692766980045921)
  ·
    refine ⟨1019778140019575235034441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1359704186692766980045921 1019778140019575235034441)
    ·
      refine ⟨764833605014681426275831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1019778140019575235034441 764833605014681426275831)
      ·
        refine ⟨1147250407522022139413747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764833605014681426275831 1147250407522022139413747)
        ·
          refine ⟨1720875611283033209120621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147250407522022139413747 1720875611283033209120621)
          ·
            refine ⟨645328354231137453420233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1720875611283033209120621 645328354231137453420233)
            ·
              refine ⟨483996265673353090065175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645328354231137453420233 483996265673353090065175)
              ·
                refine ⟨725994398510029635097763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483996265673353090065175 725994398510029635097763)
                ·
                  refine ⟨1088991597765044452646645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725994398510029635097763 1088991597765044452646645)
                  ·
                    refine ⟨102092962290472917435623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1088991597765044452646645 102092962290472917435623)
                    ·
                      rfl

theorem cell22_298238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_298238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298238 prefixEnd_298238 := by exact prefixLift 298238
  have htrace : WordTrace (prefixWord ++ tailWord_298238) baseStart_298238 baseEnd_298238 := by
    simpa [prefixWord, tailWord_298238, baseEnd_298238] using wordTrace_append hprefix tailTrace_298238
  have hstable : (prefixWord ++ tailWord_298238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298238).length < 2 ^ (prefixWord ++ tailWord_298238).sum := by decide
  have hdescent : baseEnd_298238 < baseStart_298238 := by decide
  rcases family_descends (prefixWord ++ tailWord_298238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298251 : List Nat := [1, 1, 1, 1, 5, 4, 3, 6]
def baseStart_298251 : Nat := 118140960795 + 298251 * 2 ^ 59
def prefixEnd_298251 : Nat := 4983230072969 + 3 ^ 40 * 298251 * 2
def baseEnd_298251 : Nat := 11344156939571690762287

theorem tailTrace_298251 : CollatzResearch.WordTrace tailWord_298251 prefixEnd_298251 11344156939571690762287 := by
  unfold tailWord_298251
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878107642495039060590607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252071761663359373727071 10878107642495039060590607)
  ·
    refine ⟨16317161463742558590885911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10878107642495039060590607 16317161463742558590885911)
    ·
      refine ⟨24475742195613837886328867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16317161463742558590885911 24475742195613837886328867)
      ·
        refine ⟨36713613293420756829493301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24475742195613837886328867 36713613293420756829493301)
        ·
          refine ⟨3441901246258195952764997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36713613293420756829493301 3441901246258195952764997)
          ·
            refine ⟨645356483673411741143437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3441901246258195952764997 645356483673411741143437)
            ·
              refine ⟨242008681377529402928789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645356483673411741143437 242008681377529402928789)
              ·
                refine ⟨11344156939571690762287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 242008681377529402928789 11344156939571690762287)
                ·
                  rfl

theorem cell22_298251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 6].length) (baseStart_298251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298251 prefixEnd_298251 := by exact prefixLift 298251
  have htrace : WordTrace (prefixWord ++ tailWord_298251) baseStart_298251 baseEnd_298251 := by
    simpa [prefixWord, tailWord_298251, baseEnd_298251] using wordTrace_append hprefix tailTrace_298251
  have hstable : (prefixWord ++ tailWord_298251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298251).length < 2 ^ (prefixWord ++ tailWord_298251).sum := by decide
  have hdescent : baseEnd_298251 < baseStart_298251 := by decide
  rcases family_descends (prefixWord ++ tailWord_298251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298272 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_298272 : Nat := 118140960795 + 298272 * 2 ^ 59
def prefixEnd_298272 : Nat := 4983230072969 + 3 ^ 40 * 298272 * 2
def baseEnd_298272 : Nat := 102104601185308162085519

theorem tailTrace_298272 : CollatzResearch.WordTrace tailWord_298272 prefixEnd_298272 102104601185308162085519 := by
  unfold tailWord_298272
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439436787709479823552535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7252582383612639764736713 5439436787709479823552535)
  ·
    refine ⟨8159155181564219735328803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439436787709479823552535 8159155181564219735328803)
    ·
      refine ⟨12238732772346329602993205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8159155181564219735328803 12238732772346329602993205)
      ·
        refine ⟨1147381197407468400280613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12238732772346329602993205 1147381197407468400280613)
        ·
          refine ⟨215133974513900325052615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1147381197407468400280613 215133974513900325052615)
          ·
            refine ⟨322700961770850487578923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215133974513900325052615 322700961770850487578923)
            ·
              refine ⟨484051442656275731368385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322700961770850487578923 484051442656275731368385)
              ·
                refine ⟨363038581992206798526289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484051442656275731368385 363038581992206798526289)
                ·
                  refine ⟨272278936494155098894717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363038581992206798526289 272278936494155098894717)
                  ·
                    refine ⟨102104601185308162085519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272278936494155098894717 102104601185308162085519)
                    ·
                      rfl

theorem cell22_298272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_298272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298272 prefixEnd_298272 := by exact prefixLift 298272
  have htrace : WordTrace (prefixWord ++ tailWord_298272) baseStart_298272 baseEnd_298272 := by
    simpa [prefixWord, tailWord_298272, baseEnd_298272] using wordTrace_append hprefix tailTrace_298272
  have hstable : (prefixWord ++ tailWord_298272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298272).length < 2 ^ (prefixWord ++ tailWord_298272).sum := by decide
  have hdescent : baseEnd_298272 < baseStart_298272 := by decide
  rcases family_descends (prefixWord ++ tailWord_298272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298309 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_298309 : Nat := 118140960795 + 298309 * 2 ^ 59
def prefixEnd_298309 : Nat := 4983230072969 + 3 ^ 40 * 298309 * 2
def baseEnd_298309 : Nat := 102117267041452398910405

theorem tailTrace_298309 : CollatzResearch.WordTrace tailWord_298309 prefixEnd_298309 102117267041452398910405 := by
  unfold tailWord_298309
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880223076284914966201981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7253482050856609977467987 10880223076284914966201981)
  ·
    refine ⟨4080083653606843112325743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10880223076284914966201981 4080083653606843112325743)
    ·
      refine ⟨6120125480410264668488615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4080083653606843112325743 6120125480410264668488615)
      ·
        refine ⟨9180188220615397002732923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6120125480410264668488615 9180188220615397002732923)
        ·
          refine ⟨13770282330923095504099385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9180188220615397002732923 13770282330923095504099385)
          ·
            refine ⟨10327711748192321628074539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13770282330923095504099385 10327711748192321628074539)
            ·
              refine ⟨15491567622288482442111809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327711748192321628074539 15491567622288482442111809)
              ·
                refine ⟨11618675716716361831583857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15491567622288482442111809 11618675716716361831583857)
                ·
                  refine ⟨8714006787537271373687893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11618675716716361831583857 8714006787537271373687893)
                  ·
                    refine ⟨102117267041452398910405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8714006787537271373687893 102117267041452398910405)
                    ·
                      rfl

theorem cell22_298309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_298309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298309 prefixEnd_298309 := by exact prefixLift 298309
  have htrace : WordTrace (prefixWord ++ tailWord_298309) baseStart_298309 baseEnd_298309 := by
    simpa [prefixWord, tailWord_298309, baseEnd_298309] using wordTrace_append hprefix tailTrace_298309
  have hstable : (prefixWord ++ tailWord_298309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298309).length < 2 ^ (prefixWord ++ tailWord_298309).sum := by decide
  have hdescent : baseEnd_298309 < baseStart_298309 := by decide
  rcases family_descends (prefixWord ++ tailWord_298309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298435 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 1, 3]
def baseStart_298435 : Nat := 118140960795 + 298435 * 2 ^ 59
def prefixEnd_298435 : Nat := 4983230072969 + 3 ^ 40 * 298435 * 2
def baseEnd_298435 : Nat := 102160399416430070260019

theorem tailTrace_298435 : CollatzResearch.WordTrace tailWord_298435 prefixEnd_298435 102160399416430070260019 := by
  unfold tailWord_298435
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884818673828438485288759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256545782552292323525839 10884818673828438485288759)
  ·
    refine ⟨16327228010742657727933139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884818673828438485288759 16327228010742657727933139)
    ·
      refine ⟨24490842016113986591899709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16327228010742657727933139 24490842016113986591899709)
      ·
        refine ⟨9184065756042744971962391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24490842016113986591899709 9184065756042744971962391)
        ·
          refine ⟨13776098634064117457943587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9184065756042744971962391 13776098634064117457943587)
          ·
            refine ⟨20664147951096176186915381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13776098634064117457943587 20664147951096176186915381)
            ·
              refine ⟨1937263870415266517523317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20664147951096176186915381 1937263870415266517523317)
              ·
                refine ⟨181618487851431236017811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1937263870415266517523317 181618487851431236017811)
                ·
                  refine ⟨272427731777146854026717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181618487851431236017811 272427731777146854026717)
                  ·
                    refine ⟨102160399416430070260019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272427731777146854026717 102160399416430070260019)
                    ·
                      rfl

theorem cell22_298435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 1, 3].length) (baseStart_298435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298435 prefixEnd_298435 := by exact prefixLift 298435
  have htrace : WordTrace (prefixWord ++ tailWord_298435) baseStart_298435 baseEnd_298435 := by
    simpa [prefixWord, tailWord_298435, baseEnd_298435] using wordTrace_append hprefix tailTrace_298435
  have hstable : (prefixWord ++ tailWord_298435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298435).length < 2 ^ (prefixWord ++ tailWord_298435).sum := by decide
  have hdescent : baseEnd_298435 < baseStart_298435 := by decide
  rcases family_descends (prefixWord ++ tailWord_298435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298452 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_298452 : Nat := 118140960795 + 298452 * 2 ^ 59
def prefixEnd_298452 : Nat := 4983230072969 + 3 ^ 40 * 298452 * 2
def baseEnd_298452 : Nat := 102166218863847692584967

theorem tailTrace_298452 : CollatzResearch.WordTrace tailWord_298452 prefixEnd_298452 102166218863847692584967 := by
  unfold tailWord_298452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442719357383425194328805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7256959143177900259105073 5442719357383425194328805)
  ·
    refine ⟨1020509879509392223936651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5442719357383425194328805 1020509879509392223936651)
    ·
      refine ⟨1530764819264088335904977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020509879509392223936651 1530764819264088335904977)
      ·
        refine ⟨1148073614448066251928733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530764819264088335904977 1148073614448066251928733)
        ·
          refine ⟨430527605418024844473275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1148073614448066251928733 430527605418024844473275)
          ·
            refine ⟨645791408127037266709913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430527605418024844473275 645791408127037266709913)
            ·
              refine ⟨484343556095277950032435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645791408127037266709913 484343556095277950032435)
              ·
                refine ⟨726515334142916925048653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484343556095277950032435 726515334142916925048653)
                ·
                  refine ⟨272443250303593846893245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726515334142916925048653 272443250303593846893245)
                  ·
                    refine ⟨102166218863847692584967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272443250303593846893245 102166218863847692584967)
                    ·
                      rfl

theorem cell22_298452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_298452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298452 prefixEnd_298452 := by exact prefixLift 298452
  have htrace : WordTrace (prefixWord ++ tailWord_298452) baseStart_298452 baseEnd_298452 := by
    simpa [prefixWord, tailWord_298452, baseEnd_298452] using wordTrace_append hprefix tailTrace_298452
  have hstable : (prefixWord ++ tailWord_298452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298452).length < 2 ^ (prefixWord ++ tailWord_298452).sum := by decide
  have hdescent : baseEnd_298452 < baseStart_298452 := by decide
  rcases family_descends (prefixWord ++ tailWord_298452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298465 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 5]
def baseStart_298465 : Nat := 118140960795 + 298465 * 2 ^ 59
def prefixEnd_298465 : Nat := 4983230072969 + 3 ^ 40 * 298465 * 2
def baseEnd_298465 : Nat := 34056889676506664003309

theorem tailTrace_298465 : CollatzResearch.WordTrace tailWord_298465 prefixEnd_298465 34056889676506664003309 := by
  unfold tailWord_298465
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885912863719753608880849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7257275242479835739253899 10885912863719753608880849)
  ·
    refine ⟨8164434647789815206660637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10885912863719753608880849 8164434647789815206660637)
    ·
      refine ⟨3061662992921180702497739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8164434647789815206660637 3061662992921180702497739)
      ·
        refine ⟨4592494489381771053746609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061662992921180702497739 4592494489381771053746609)
        ·
          refine ⟨3444370867036328290309957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4592494489381771053746609 3444370867036328290309957)
          ·
            refine ⟨645819537569311554433117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3444370867036328290309957 645819537569311554433117)
            ·
              refine ⟨242182326588491832912419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 645819537569311554433117 242182326588491832912419)
              ·
                refine ⟨363273489882737749368629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242182326588491832912419 363273489882737749368629)
                ·
                  refine ⟨34056889676506664003309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363273489882737749368629 34056889676506664003309)
                  ·
                    rfl

theorem cell22_298465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_298465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298465 prefixEnd_298465 := by exact prefixLift 298465
  have htrace : WordTrace (prefixWord ++ tailWord_298465) baseStart_298465 baseEnd_298465 := by
    simpa [prefixWord, tailWord_298465, baseEnd_298465] using wordTrace_append hprefix tailTrace_298465
  have hstable : (prefixWord ++ tailWord_298465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298465).length < 2 ^ (prefixWord ++ tailWord_298465).sum := by decide
  have hdescent : baseEnd_298465 < baseStart_298465 := by decide
  rcases family_descends (prefixWord ++ tailWord_298465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298476 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_298476 : Nat := 118140960795 + 298476 * 2 ^ 59
def prefixEnd_298476 : Nat := 4983230072969 + 3 ^ 40 * 298476 * 2
def baseEnd_298476 : Nat := 34058144851439876661631

theorem tailTrace_298476 : CollatzResearch.WordTrace tailWord_298476 prefixEnd_298476 34058144851439876661631 := by
  unfold tailWord_298476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443157033339951243765641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7257542711119934991687521 5443157033339951243765641)
  ·
    refine ⟨4082367775004963432824231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5443157033339951243765641 4082367775004963432824231)
    ·
      refine ⟨6123551662507445149236347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082367775004963432824231 6123551662507445149236347)
      ·
        refine ⟨9185327493761167723854521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123551662507445149236347 9185327493761167723854521)
        ·
          refine ⟨6888995620320875792890891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9185327493761167723854521 6888995620320875792890891)
          ·
            refine ⟨10333493430481313689336337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888995620320875792890891 10333493430481313689336337)
            ·
              refine ⟨7750120072860985267002253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10333493430481313689336337 7750120072860985267002253)
              ·
                refine ⟨2906295027322869475125845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7750120072860985267002253 2906295027322869475125845)
                ·
                  refine ⟨34058144851439876661631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2906295027322869475125845 34058144851439876661631)
                  ·
                    rfl

theorem cell22_298476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_298476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298476 prefixEnd_298476 := by exact prefixLift 298476
  have htrace : WordTrace (prefixWord ++ tailWord_298476) baseStart_298476 baseEnd_298476 := by
    simpa [prefixWord, tailWord_298476, baseEnd_298476] using wordTrace_append hprefix tailTrace_298476
  have hstable : (prefixWord ++ tailWord_298476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298476).length < 2 ^ (prefixWord ++ tailWord_298476).sum := by decide
  have hdescent : baseEnd_298476 < baseStart_298476 := by decide
  rcases family_descends (prefixWord ++ tailWord_298476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298516 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_298516 : Nat := 118140960795 + 298516 * 2 ^ 59
def prefixEnd_298516 : Nat := 4983230072969 + 3 ^ 40 * 298516 * 2
def baseEnd_298516 : Nat := 34062709123924286328257

theorem tailTrace_298516 : CollatzResearch.WordTrace tailWord_298516 prefixEnd_298516 34062709123924286328257 := by
  unfold tailWord_298516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443886493267494659493701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7258515324356659545991601 5443886493267494659493701)
  ·
    refine ⟨1020728717487655248655069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5443886493267494659493701 1020728717487655248655069)
    ·
      refine ⟨382773269057870718245651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1020728717487655248655069 382773269057870718245651)
      ·
        refine ⟨574159903586806077368477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382773269057870718245651 574159903586806077368477)
        ·
          refine ⟨215309963845052279013179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574159903586806077368477 215309963845052279013179)
          ·
            refine ⟨322964945767578418519769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215309963845052279013179 322964945767578418519769)
            ·
              refine ⟨242223709325683813889827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322964945767578418519769 242223709325683813889827)
              ·
                refine ⟨363335563988525720834741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242223709325683813889827 363335563988525720834741)
                ·
                  refine ⟨34062709123924286328257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363335563988525720834741 34062709123924286328257)
                  ·
                    rfl

theorem cell22_298516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_298516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298516 prefixEnd_298516 := by exact prefixLift 298516
  have htrace : WordTrace (prefixWord ++ tailWord_298516) baseStart_298516 baseEnd_298516 := by
    simpa [prefixWord, tailWord_298516, baseEnd_298516] using wordTrace_append hprefix tailTrace_298516
  have hstable : (prefixWord ++ tailWord_298516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298516).length < 2 ^ (prefixWord ++ tailWord_298516).sum := by decide
  have hdescent : baseEnd_298516 < baseStart_298516 := by decide
  rcases family_descends (prefixWord ++ tailWord_298516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298538 : List Nat := [3, 1, 4, 1, 1, 1, 1, 10]
def baseStart_298538 : Nat := 118140960795 + 298538 * 2 ^ 59
def prefixEnd_298538 : Nat := 4983230072969 + 3 ^ 40 * 298538 * 2
def baseEnd_298538 : Nat := 11355073157930237214967

theorem tailTrace_298538 : CollatzResearch.WordTrace tailWord_298538 prefixEnd_298538 11355073157930237214967 := by
  unfold tailWord_298538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722143848113821769072067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7259050261636858050858845 2722143848113821769072067)
  ·
    refine ⟨4083215772170732653608101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722143848113821769072067 4083215772170732653608101)
    ·
      refine ⟨765602957282012372551519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4083215772170732653608101 765602957282012372551519)
      ·
        refine ⟨1148404435923018558827279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765602957282012372551519 1148404435923018558827279)
        ·
          refine ⟨1722606653884527838240919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148404435923018558827279 1722606653884527838240919)
          ·
            refine ⟨2583909980826791757361379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722606653884527838240919 2583909980826791757361379)
            ·
              refine ⟨3875864971240187636042069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583909980826791757361379 3875864971240187636042069)
              ·
                refine ⟨11355073157930237214967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3875864971240187636042069 11355073157930237214967)
                ·
                  rfl

theorem cell22_298538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_298538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298538 prefixEnd_298538 := by exact prefixLift 298538
  have htrace : WordTrace (prefixWord ++ tailWord_298538) baseStart_298538 baseEnd_298538 := by
    simpa [prefixWord, tailWord_298538, baseEnd_298538] using wordTrace_append hprefix tailTrace_298538
  have hstable : (prefixWord ++ tailWord_298538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298538).length < 2 ^ (prefixWord ++ tailWord_298538).sum := by decide
  have hdescent : baseEnd_298538 < baseStart_298538 := by decide
  rcases family_descends (prefixWord ++ tailWord_298538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298570 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_298570 : Nat := 118140960795 + 298570 * 2 ^ 59
def prefixEnd_298570 : Nat := 4983230072969 + 3 ^ 40 * 298570 * 2
def baseEnd_298570 : Nat := 102206612675334718134605

theorem tailTrace_298570 : CollatzResearch.WordTrace tailWord_298570 prefixEnd_298570 102206612675334718134605 := by
  unfold tailWord_298570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722435632084839135363291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7259828352226237694302109 2722435632084839135363291)
  ·
    refine ⟨4083653448127258703044937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722435632084839135363291 4083653448127258703044937)
    ·
      refine ⟨3062740086095444027283703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4083653448127258703044937 3062740086095444027283703)
      ·
        refine ⟨4594110129143166040925555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062740086095444027283703 4594110129143166040925555)
        ·
          refine ⟨6891165193714749061388333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594110129143166040925555 6891165193714749061388333)
          ·
            refine ⟨2584186947643030898020625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6891165193714749061388333 2584186947643030898020625)
            ·
              refine ⟨1938140210732273173515469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584186947643030898020625 1938140210732273173515469)
              ·
                refine ⟨726802579024602440068301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1938140210732273173515469 726802579024602440068301)
                ·
                  refine ⟨272550967134225915025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726802579024602440068301 272550967134225915025613)
                  ·
                    refine ⟨102206612675334718134605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272550967134225915025613 102206612675334718134605)
                    ·
                      rfl

theorem cell22_298570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_298570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298570 prefixEnd_298570 := by exact prefixLift 298570
  have htrace : WordTrace (prefixWord ++ tailWord_298570) baseStart_298570 baseEnd_298570 := by
    simpa [prefixWord, tailWord_298570, baseEnd_298570] using wordTrace_append hprefix tailTrace_298570
  have hstable : (prefixWord ++ tailWord_298570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298570).length < 2 ^ (prefixWord ++ tailWord_298570).sum := by decide
  have hdescent : baseEnd_298570 < baseStart_298570 := by decide
  rcases family_descends (prefixWord ++ tailWord_298570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298589 : List Nat := [1, 4, 4, 2, 1, 1, 3, 6]
def baseStart_298589 : Nat := 118140960795 + 298589 * 2 ^ 59
def prefixEnd_298589 : Nat := 4983230072969 + 3 ^ 40 * 298589 * 2
def baseEnd_298589 : Nat := 11357012973736111323283

theorem tailTrace_298589 : CollatzResearch.WordTrace tailWord_298589 prefixEnd_298589 11357012973736111323283 := by
  unfold tailWord_298589
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890435515270522786394821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7260290343513681857596547 10890435515270522786394821)
  ·
    refine ⟨2041956659113223022449029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10890435515270522786394821 2041956659113223022449029)
    ·
      refine ⟨382866873583729316709193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2041956659113223022449029 382866873583729316709193)
      ·
        refine ⟨287150155187796987531895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382866873583729316709193 287150155187796987531895)
        ·
          refine ⟨430725232781695481297843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287150155187796987531895 430725232781695481297843)
          ·
            refine ⟨646087849172543221946765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430725232781695481297843 646087849172543221946765)
            ·
              refine ⟨242282943439703708230037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646087849172543221946765 242282943439703708230037)
              ·
                refine ⟨11357012973736111323283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 242282943439703708230037 11357012973736111323283)
                ·
                  rfl

theorem cell22_298589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 6].length) (baseStart_298589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298589 prefixEnd_298589 := by exact prefixLift 298589
  have htrace : WordTrace (prefixWord ++ tailWord_298589) baseStart_298589 baseEnd_298589 := by
    simpa [prefixWord, tailWord_298589, baseEnd_298589] using wordTrace_append hprefix tailTrace_298589
  have hstable : (prefixWord ++ tailWord_298589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298589).length < 2 ^ (prefixWord ++ tailWord_298589).sum := by decide
  have hdescent : baseEnd_298589 < baseStart_298589 := by decide
  rcases family_descends (prefixWord ++ tailWord_298589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298647 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 1, 4]
def baseStart_298647 : Nat := 118140960795 + 298647 * 2 ^ 59
def prefixEnd_298647 : Nat := 4983230072969 + 3 ^ 40 * 298647 * 2
def baseEnd_298647 : Nat := 102232971348932183959369

theorem tailTrace_298647 : CollatzResearch.WordTrace tailWord_298647 prefixEnd_298647 102232971348932183959369 := by
  unfold tailWord_298647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892550949060398692006195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7261700632706932461337463 10892550949060398692006195)
  ·
    refine ⟨16338826423590598038009293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10892550949060398692006195 16338826423590598038009293)
    ·
      refine ⟨6127059908846474264253485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16338826423590598038009293 6127059908846474264253485)
      ·
        refine ⟨2297647465817427849095057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6127059908846474264253485 2297647465817427849095057)
        ·
          refine ⟨1723235599363070886821293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297647465817427849095057 1723235599363070886821293)
          ·
            refine ⟨646213349761151582557985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1723235599363070886821293 646213349761151582557985)
            ·
              refine ⟨484660012320863686918489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646213349761151582557985 484660012320863686918489)
              ·
                refine ⟨363495009240647765188867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484660012320863686918489 363495009240647765188867)
                ·
                  refine ⟨545242513860971647783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363495009240647765188867 545242513860971647783301)
                  ·
                    refine ⟨102232971348932183959369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545242513860971647783301 102232971348932183959369)
                    ·
                      rfl

theorem cell22_298647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_298647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298647 prefixEnd_298647 := by exact prefixLift 298647
  have htrace : WordTrace (prefixWord ++ tailWord_298647) baseStart_298647 baseEnd_298647 := by
    simpa [prefixWord, tailWord_298647, baseEnd_298647] using wordTrace_append hprefix tailTrace_298647
  have hstable : (prefixWord ++ tailWord_298647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298647).length < 2 ^ (prefixWord ++ tailWord_298647).sum := by decide
  have hdescent : baseEnd_298647 < baseStart_298647 := by decide
  rcases family_descends (prefixWord ++ tailWord_298647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298675 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_298675 : Nat := 118140960795 + 298675 * 2 ^ 59
def prefixEnd_298675 : Nat := 4983230072969 + 3 ^ 40 * 298675 * 2
def baseEnd_298675 : Nat := 102242556321149444259283

theorem tailTrace_298675 : CollatzResearch.WordTrace tailWord_298675 prefixEnd_298675 102242556321149444259283 := by
  unfold tailWord_298675
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893572192958959474025479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7262381461972639649350319 10893572192958959474025479)
  ·
    refine ⟨16340358289438439211038219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10893572192958959474025479 16340358289438439211038219)
    ·
      refine ⟨24510537434157658816557329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16340358289438439211038219 24510537434157658816557329)
      ·
        refine ⟨18382903075618244112417997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24510537434157658816557329 18382903075618244112417997)
        ·
          refine ⟨6893588653356841542156749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18382903075618244112417997 6893588653356841542156749)
          ·
            refine ⟨2585095745008815578308781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6893588653356841542156749 2585095745008815578308781)
            ·
              refine ⟨969410904378305841865793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2585095745008815578308781 969410904378305841865793)
              ·
                refine ⟨727058178283729381399345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969410904378305841865793 727058178283729381399345)
                ·
                  refine ⟨545293633712797036049509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727058178283729381399345 545293633712797036049509)
                  ·
                    refine ⟨102242556321149444259283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545293633712797036049509 102242556321149444259283)
                    ·
                      rfl

theorem cell22_298675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_298675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298675 prefixEnd_298675 := by exact prefixLift 298675
  have htrace : WordTrace (prefixWord ++ tailWord_298675) baseStart_298675 baseEnd_298675 := by
    simpa [prefixWord, tailWord_298675, baseEnd_298675] using wordTrace_append hprefix tailTrace_298675
  have hstable : (prefixWord ++ tailWord_298675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298675).length < 2 ^ (prefixWord ++ tailWord_298675).sum := by decide
  have hdescent : baseEnd_298675 < baseStart_298675 := by decide
  rcases family_descends (prefixWord ++ tailWord_298675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298679 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 4]
def baseStart_298679 : Nat := 118140960795 + 298679 * 2 ^ 59
def prefixEnd_298679 : Nat := 4983230072969 + 3 ^ 40 * 298679 * 2
def baseEnd_298679 : Nat := 34081308534298255719757

theorem tailTrace_298679 : CollatzResearch.WordTrace tailWord_298679 prefixEnd_298679 34081308534298255719757 := by
  unfold tailWord_298679
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893718084944468157171091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7262478723296312104780727 10893718084944468157171091)
  ·
    refine ⟨16340577127416702235756637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10893718084944468157171091 16340577127416702235756637)
    ·
      refine ⟨6127716422781263338408739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16340577127416702235756637 6127716422781263338408739)
      ·
        refine ⟨9191574634171895007613109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127716422781263338408739 9191574634171895007613109)
        ·
          refine ⟨861710121953615156963729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9191574634171895007613109 861710121953615156963729)
          ·
            refine ⟨646282591465211367722797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861710121953615156963729 646282591465211367722797)
            ·
              refine ⟨242355971799454262896049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646282591465211367722797 242355971799454262896049)
              ·
                refine ⟨181766978849590697172037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242355971799454262896049 181766978849590697172037)
                ·
                  refine ⟨34081308534298255719757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181766978849590697172037 34081308534298255719757)
                  ·
                    rfl

theorem cell22_298679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 4].length) (baseStart_298679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298679 prefixEnd_298679 := by exact prefixLift 298679
  have htrace : WordTrace (prefixWord ++ tailWord_298679) baseStart_298679 baseEnd_298679 := by
    simpa [prefixWord, tailWord_298679, baseEnd_298679] using wordTrace_append hprefix tailTrace_298679
  have hstable : (prefixWord ++ tailWord_298679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298679).length < 2 ^ (prefixWord ++ tailWord_298679).sum := by decide
  have hdescent : baseEnd_298679 < baseStart_298679 := by decide
  rcases family_descends (prefixWord ++ tailWord_298679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298780 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_298780 : Nat := 118140960795 + 298780 * 2 ^ 59
def prefixEnd_298780 : Nat := 4983230072969 + 3 ^ 40 * 298780 * 2
def baseEnd_298780 : Nat := 34092833322321390127987

theorem tailTrace_298780 : CollatzResearch.WordTrace tailWord_298780 prefixEnd_298780 34092833322321390127987 := by
  unfold tailWord_298780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448700928789281203298897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7264934571719041604398529 5448700928789281203298897)
  ·
    refine ⟨4086525696591960902474173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5448700928789281203298897 4086525696591960902474173)
    ·
      refine ⟨1532447136221985338427815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4086525696591960902474173 1532447136221985338427815)
      ·
        refine ⟨2298670704332978007641723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532447136221985338427815 2298670704332978007641723)
        ·
          refine ⟨3448006056499467011462585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298670704332978007641723 3448006056499467011462585)
          ·
            refine ⟨2586004542374600258596939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448006056499467011462585 2586004542374600258596939)
            ·
              refine ⟨3879006813561900387895409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586004542374600258596939 3879006813561900387895409)
              ·
                refine ⟨2909255110171425290921557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3879006813561900387895409 2909255110171425290921557)
                ·
                  refine ⟨34092833322321390127987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2909255110171425290921557 34092833322321390127987)
                  ·
                    rfl

theorem cell22_298780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_298780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298780 prefixEnd_298780 := by exact prefixLift 298780
  have htrace : WordTrace (prefixWord ++ tailWord_298780) baseStart_298780 baseEnd_298780 := by
    simpa [prefixWord, tailWord_298780, baseEnd_298780] using wordTrace_append hprefix tailTrace_298780
  have hstable : (prefixWord ++ tailWord_298780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298780).length < 2 ^ (prefixWord ++ tailWord_298780).sum := by decide
  have hdescent : baseEnd_298780 < baseStart_298780 := by decide
  rcases family_descends (prefixWord ++ tailWord_298780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298812 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_298812 : Nat := 118140960795 + 298812 * 2 ^ 59
def prefixEnd_298812 : Nat := 4983230072969 + 3 ^ 40 * 298812 * 2
def baseEnd_298812 : Nat := 102289454220926753583863

theorem tailTrace_298812 : CollatzResearch.WordTrace tailWord_298812 prefixEnd_298812 102289454220926753583863 := by
  unfold tailWord_298812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449284496731315935881345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7265712662308421247841793 5449284496731315935881345)
  ·
    refine ⟨4086963372548486951911009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5449284496731315935881345 4086963372548486951911009)
    ·
      refine ⟨3065222529411365213933257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4086963372548486951911009 3065222529411365213933257)
      ·
        refine ⟨2298916897058523910449943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065222529411365213933257 2298916897058523910449943)
        ·
          refine ⟨3448375345587785865674915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298916897058523910449943 3448375345587785865674915)
          ·
            refine ⟨5172563018381678798512373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448375345587785865674915 5172563018381678798512373)
            ·
              refine ⟨484927782973282387360535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5172563018381678798512373 484927782973282387360535)
              ·
                refine ⟨727391674459923581040803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484927782973282387360535 727391674459923581040803)
                ·
                  refine ⟨1091087511689885371561205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727391674459923581040803 1091087511689885371561205)
                  ·
                    refine ⟨102289454220926753583863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1091087511689885371561205 102289454220926753583863)
                    ·
                      rfl

theorem cell22_298812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_298812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298812 prefixEnd_298812 := by exact prefixLift 298812
  have htrace : WordTrace (prefixWord ++ tailWord_298812) baseStart_298812 baseEnd_298812 := by
    simpa [prefixWord, tailWord_298812, baseEnd_298812] using wordTrace_append hprefix tailTrace_298812
  have hstable : (prefixWord ++ tailWord_298812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298812).length < 2 ^ (prefixWord ++ tailWord_298812).sum := by decide
  have hdescent : baseEnd_298812 < baseStart_298812 := by decide
  rcases family_descends (prefixWord ++ tailWord_298812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298825 : List Nat := [1, 2, 1, 1, 2, 4, 3, 8]
def baseStart_298825 : Nat := 118140960795 + 298825 * 2 ^ 59
def prefixEnd_298825 : Nat := 4983230072969 + 3 ^ 40 * 298825 * 2
def baseEnd_298825 : Nat := 11365989376288783667647

theorem tailTrace_298825 : CollatzResearch.WordTrace tailWord_298825 prefixEnd_298825 11365989376288783667647 := by
  unfold tailWord_298825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899043142415535091985929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7266028761610356727990619 10899043142415535091985929)
  ·
    refine ⟨8174282356811651318989447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10899043142415535091985929 8174282356811651318989447)
    ·
      refine ⟨12261423535217476978484171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174282356811651318989447 12261423535217476978484171)
      ·
        refine ⟨18392135302826215467726257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12261423535217476978484171 18392135302826215467726257)
        ·
          refine ⟨13794101477119661600794693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18392135302826215467726257 13794101477119661600794693)
          ·
            refine ⟨2586394026959936550149005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13794101477119661600794693 2586394026959936550149005)
            ·
              refine ⟨969897760109976206305877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2586394026959936550149005 969897760109976206305877)
              ·
                refine ⟨11365989376288783667647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 969897760109976206305877 11365989376288783667647)
                ·
                  rfl

theorem cell22_298825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 8].length) (baseStart_298825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298825 prefixEnd_298825 := by exact prefixLift 298825
  have htrace : WordTrace (prefixWord ++ tailWord_298825) baseStart_298825 baseEnd_298825 := by
    simpa [prefixWord, tailWord_298825, baseEnd_298825] using wordTrace_append hprefix tailTrace_298825
  have hstable : (prefixWord ++ tailWord_298825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298825).length < 2 ^ (prefixWord ++ tailWord_298825).sum := by decide
  have hdescent : baseEnd_298825 < baseStart_298825 := by decide
  rcases family_descends (prefixWord ++ tailWord_298825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298908 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_298908 : Nat := 118140960795 + 298908 * 2 ^ 59
def prefixEnd_298908 : Nat := 4983230072969 + 3 ^ 40 * 298908 * 2
def baseEnd_298908 : Nat := 102322316982814503183569

theorem tailTrace_298908 : CollatzResearch.WordTrace tailWord_298908 prefixEnd_298908 102322316982814503183569 := by
  unfold tailWord_298908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5451035200557420133628689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7268046934076560178171585 5451035200557420133628689)
  ·
    refine ⟨4088276400418065100221517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5451035200557420133628689 4088276400418065100221517)
    ·
      refine ⟨1533103650156774412583069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4088276400418065100221517 1533103650156774412583069)
      ·
        refine ⟨574913868808790404718651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1533103650156774412583069 574913868808790404718651)
        ·
          refine ⟨862370803213185607077977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574913868808790404718651 862370803213185607077977)
          ·
            refine ⟨646778102409889205308483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862370803213185607077977 646778102409889205308483)
            ·
              refine ⟨970167153614833807962725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646778102409889205308483 970167153614833807962725)
              ·
                refine ⟨181906341302781338993011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 970167153614833807962725 181906341302781338993011)
                ·
                  refine ⟨272859511954172008489517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181906341302781338993011 272859511954172008489517)
                  ·
                    refine ⟨102322316982814503183569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272859511954172008489517 102322316982814503183569)
                    ·
                      rfl

theorem cell22_298908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_298908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298908 prefixEnd_298908 := by exact prefixLift 298908
  have htrace : WordTrace (prefixWord ++ tailWord_298908) baseStart_298908 baseEnd_298908 := by
    simpa [prefixWord, tailWord_298908, baseEnd_298908] using wordTrace_append hprefix tailTrace_298908
  have hstable : (prefixWord ++ tailWord_298908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298908).length < 2 ^ (prefixWord ++ tailWord_298908).sum := by decide
  have hdescent : baseEnd_298908 < baseStart_298908 := by decide
  rcases family_descends (prefixWord ++ tailWord_298908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298919 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_298919 : Nat := 118140960795 + 298919 * 2 ^ 59
def prefixEnd_298919 : Nat := 4983230072969 + 3 ^ 40 * 298919 * 2
def baseEnd_298919 : Nat := 102326082507614141158535

theorem tailTrace_298919 : CollatzResearch.WordTrace tailWord_298919 prefixEnd_298919 102326082507614141158535 := by
  unfold tailWord_298919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902471604074989145907811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7268314402716659430605207 10902471604074989145907811)
  ·
    refine ⟨16353707406112483718861717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10902471604074989145907811 16353707406112483718861717)
    ·
      refine ⟨766580034661522674321643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16353707406112483718861717 766580034661522674321643)
      ·
        refine ⟨1149870051992284011482465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766580034661522674321643 1149870051992284011482465)
        ·
          refine ⟨862402538994213008611849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149870051992284011482465 862402538994213008611849)
          ·
            refine ⟨646801904245659756458887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862402538994213008611849 646801904245659756458887)
            ·
              refine ⟨970202856368489634688331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646801904245659756458887 970202856368489634688331)
              ·
                refine ⟨1455304284552734452032497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970202856368489634688331 1455304284552734452032497)
                ·
                  refine ⟨1091478213414550839024373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455304284552734452032497 1091478213414550839024373)
                  ·
                    refine ⟨102326082507614141158535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1091478213414550839024373 102326082507614141158535)
                    ·
                      rfl

theorem cell22_298919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_298919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_298919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_298919 prefixEnd_298919 := by exact prefixLift 298919
  have htrace : WordTrace (prefixWord ++ tailWord_298919) baseStart_298919 baseEnd_298919 := by
    simpa [prefixWord, tailWord_298919, baseEnd_298919] using wordTrace_append hprefix tailTrace_298919
  have hstable : (prefixWord ++ tailWord_298919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298919).length < 2 ^ (prefixWord ++ tailWord_298919).sum := by decide
  have hdescent : baseEnd_298919 < baseStart_298919 := by decide
  rcases family_descends (prefixWord ++ tailWord_298919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299028 : List Nat := [2, 4, 3, 2, 1, 1, 2, 7]
def baseStart_299028 : Nat := 118140960795 + 299028 * 2 ^ 59
def prefixEnd_299028 : Nat := 4983230072969 + 3 ^ 40 * 299028 * 2
def baseEnd_299028 : Nat := 11373710603908243353689

theorem tailTrace_299028 : CollatzResearch.WordTrace tailWord_299028 prefixEnd_299028 11373710603908243353689 := by
  unfold tailWord_299028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453223580340050380812869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7270964773786733841083825 5453223580340050380812869)
  ·
    refine ⟨1022479421313759446402413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5453223580340050380812869 1022479421313759446402413)
    ·
      refine ⟨383429782992659792400905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1022479421313759446402413 383429782992659792400905)
      ·
        refine ⟨287572337244494844300679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383429782992659792400905 287572337244494844300679)
        ·
          refine ⟨431358505866742266451019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287572337244494844300679 431358505866742266451019)
          ·
            refine ⟨647037758800113399676529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431358505866742266451019 647037758800113399676529)
            ·
              refine ⟨485278319100085049757397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647037758800113399676529 485278319100085049757397)
              ·
                refine ⟨11373710603908243353689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 485278319100085049757397 11373710603908243353689)
                ·
                  rfl

theorem cell22_299028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_299028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299028 prefixEnd_299028 := by exact prefixLift 299028
  have htrace : WordTrace (prefixWord ++ tailWord_299028) baseStart_299028 baseEnd_299028 := by
    simpa [prefixWord, tailWord_299028, baseEnd_299028] using wordTrace_append hprefix tailTrace_299028
  have hstable : (prefixWord ++ tailWord_299028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299028).length < 2 ^ (prefixWord ++ tailWord_299028).sum := by decide
  have hdescent : baseEnd_299028 < baseStart_299028 := by decide
  rcases family_descends (prefixWord ++ tailWord_299028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299039 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 5]
def baseStart_299039 : Nat := 118140960795 + 299039 * 2 ^ 59
def prefixEnd_299039 : Nat := 4983230072969 + 3 ^ 40 * 299039 * 2
def baseEnd_299039 : Nat := 34122386986657942719389

theorem tailTrace_299039 : CollatzResearch.WordTrace tailWord_299039 prefixEnd_299039 34122386986657942719389 := by
  unfold tailWord_299039
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906848363640249640276171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7271232242426833093517447 10906848363640249640276171)
  ·
    refine ⟨16360272545460374460414257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10906848363640249640276171 16360272545460374460414257)
    ·
      refine ⟨12270204409095280845310693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16360272545460374460414257 12270204409095280845310693)
      ·
        refine ⟨2300663326705365158495755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12270204409095280845310693 2300663326705365158495755)
        ·
          refine ⟨3450994990058047737743633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300663326705365158495755 3450994990058047737743633)
          ·
            refine ⟨2588246242543535803307725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450994990058047737743633 2588246242543535803307725)
            ·
              refine ⟨970592340953825926240397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2588246242543535803307725 970592340953825926240397)
              ·
                refine ⟨363972127857684722340149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970592340953825926240397 363972127857684722340149)
                ·
                  refine ⟨34122386986657942719389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363972127857684722340149 34122386986657942719389)
                  ·
                    rfl

theorem cell22_299039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 5].length) (baseStart_299039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299039 prefixEnd_299039 := by exact prefixLift 299039
  have htrace : WordTrace (prefixWord ++ tailWord_299039) baseStart_299039 baseEnd_299039 := by
    simpa [prefixWord, tailWord_299039, baseEnd_299039] using wordTrace_append hprefix tailTrace_299039
  have hstable : (prefixWord ++ tailWord_299039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299039).length < 2 ^ (prefixWord ++ tailWord_299039).sum := by decide
  have hdescent : baseEnd_299039 < baseStart_299039 := by decide
  rcases family_descends (prefixWord ++ tailWord_299039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299067 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 8]
def baseStart_299067 : Nat := 118140960795 + 299067 * 2 ^ 59
def prefixEnd_299067 : Nat := 4983230072969 + 3 ^ 40 * 299067 * 2
def baseEnd_299067 : Nat := 34125581977397029486027

theorem tailTrace_299067 : CollatzResearch.WordTrace tailWord_299067 prefixEnd_299067 34125581977397029486027 := by
  unfold tailWord_299067
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907869607538810422295455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7271913071692540281530303 10907869607538810422295455)
  ·
    refine ⟨16361804411308215633443183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10907869607538810422295455 16361804411308215633443183)
    ·
      refine ⟨24542706616962323450164775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16361804411308215633443183 24542706616962323450164775)
      ·
        refine ⟨36814059925443485175247163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24542706616962323450164775 36814059925443485175247163)
        ·
          refine ⟨55221089888165227762870745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36814059925443485175247163 55221089888165227762870745)
          ·
            refine ⟨41415817416123920822153059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55221089888165227762870745 41415817416123920822153059)
            ·
              refine ⟨62123726124185881233229589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41415817416123920822153059 62123726124185881233229589)
              ·
                refine ⟨2912049662071213182807637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62123726124185881233229589 2912049662071213182807637)
                ·
                  refine ⟨34125581977397029486027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2912049662071213182807637 34125581977397029486027)
                  ·
                    rfl

theorem cell22_299067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_299067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299067 prefixEnd_299067 := by exact prefixLift 299067
  have htrace : WordTrace (prefixWord ++ tailWord_299067) baseStart_299067 baseEnd_299067 := by
    simpa [prefixWord, tailWord_299067, baseEnd_299067] using wordTrace_append hprefix tailTrace_299067
  have hstable : (prefixWord ++ tailWord_299067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299067).length < 2 ^ (prefixWord ++ tailWord_299067).sum := by decide
  have hdescent : baseEnd_299067 < baseStart_299067 := by decide
  rcases family_descends (prefixWord ++ tailWord_299067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299101 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 8]
def baseStart_299101 : Nat := 118140960795 + 299101 * 2 ^ 59
def prefixEnd_299101 : Nat := 4983230072969 + 3 ^ 40 * 299101 * 2
def baseEnd_299101 : Nat := 34129461609008777702659

theorem tailTrace_299101 : CollatzResearch.WordTrace tailWord_299101 prefixEnd_299101 34129461609008777702659 := by
  unfold tailWord_299101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909109689415634229033157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7272739792943756152688771 10909109689415634229033157)
  ·
    refine ⟨2045458066765431417943717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10909109689415634229033157 2045458066765431417943717)
    ·
      refine ⟨383523387518518390864447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2045458066765431417943717 383523387518518390864447)
      ·
        refine ⟨575285081277777586296671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383523387518518390864447 575285081277777586296671)
        ·
          refine ⟨862927621916666379445007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575285081277777586296671 862927621916666379445007)
          ·
            refine ⟨1294391432874999569167511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862927621916666379445007 1294391432874999569167511)
            ·
              refine ⟨1941587149312499353751267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294391432874999569167511 1941587149312499353751267)
              ·
                refine ⟨2912380723968749030626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941587149312499353751267 2912380723968749030626901)
                ·
                  refine ⟨34129461609008777702659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2912380723968749030626901 34129461609008777702659)
                  ·
                    rfl

theorem cell22_299101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_299101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299101 prefixEnd_299101 := by exact prefixLift 299101
  have htrace : WordTrace (prefixWord ++ tailWord_299101) baseStart_299101 baseEnd_299101 := by
    simpa [prefixWord, tailWord_299101, baseEnd_299101] using wordTrace_append hprefix tailTrace_299101
  have hstable : (prefixWord ++ tailWord_299101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299101).length < 2 ^ (prefixWord ++ tailWord_299101).sum := by decide
  have hdescent : baseEnd_299101 < baseStart_299101 := by decide
  rcases family_descends (prefixWord ++ tailWord_299101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299118 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_299118 : Nat := 118140960795 + 299118 * 2 ^ 59
def prefixEnd_299118 : Nat := 4983230072969 + 3 ^ 40 * 299118 * 2
def baseEnd_299118 : Nat := 34131401424814651810975

theorem tailTrace_299118 : CollatzResearch.WordTrace tailWord_299118 prefixEnd_299118 34131401424814651810975 := by
  unfold tailWord_299118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363716216294255766550251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7273153153569364088268005 1363716216294255766550251)
  ·
    refine ⟨2045574324441383649825377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363716216294255766550251 2045574324441383649825377)
    ·
      refine ⟨1534180743331037737369033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2045574324441383649825377 1534180743331037737369033)
      ·
        refine ⟨1150635557498278303026775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1534180743331037737369033 1150635557498278303026775)
        ·
          refine ⟨1725953336247417454540163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150635557498278303026775 1725953336247417454540163)
          ·
            refine ⟨2588930004371126181810245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725953336247417454540163 2588930004371126181810245)
            ·
              refine ⟨485424375819586159089421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2588930004371126181810245 485424375819586159089421)
              ·
                refine ⟨182034140932344809658533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 485424375819586159089421 182034140932344809658533)
                ·
                  refine ⟨34131401424814651810975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182034140932344809658533 34131401424814651810975)
                  ·
                    rfl

theorem cell22_299118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_299118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299118 prefixEnd_299118 := by exact prefixLift 299118
  have htrace : WordTrace (prefixWord ++ tailWord_299118) baseStart_299118 baseEnd_299118 := by
    simpa [prefixWord, tailWord_299118, baseEnd_299118] using wordTrace_append hprefix tailTrace_299118
  have hstable : (prefixWord ++ tailWord_299118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299118).length < 2 ^ (prefixWord ++ tailWord_299118).sum := by decide
  have hdescent : baseEnd_299118 < baseStart_299118 := by decide
  rcases family_descends (prefixWord ++ tailWord_299118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299129 : List Nat := [1, 2, 1, 3, 4, 2, 9]
def baseStart_299129 : Nat := 118140960795 + 299129 * 2 ^ 59
def prefixEnd_299129 : Nat := 4983230072969 + 3 ^ 40 * 299129 * 2
def baseEnd_299129 : Nat := 3792517399971984941033

theorem tailTrace_299129 : CollatzResearch.WordTrace tailWord_299129 prefixEnd_299129 3792517399971984941033 := by
  unfold tailWord_299129
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910130933314195011052441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7273420622209463340701627 10910130933314195011052441)
  ·
    refine ⟨8182598199985646258289331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10910130933314195011052441 8182598199985646258289331)
    ·
      refine ⟨12273897299978469387433997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182598199985646258289331 12273897299978469387433997)
      ·
        refine ⟨4602711487491926020287749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12273897299978469387433997 4602711487491926020287749)
        ·
          refine ⟨863008403904736128803953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4602711487491926020287749 863008403904736128803953)
          ·
            refine ⟨647256302928552096602965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863008403904736128803953 647256302928552096602965)
            ·
              refine ⟨3792517399971984941033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 647256302928552096602965 3792517399971984941033)
              ·
                rfl

theorem cell22_299129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 9].length) (baseStart_299129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299129 prefixEnd_299129 := by exact prefixLift 299129
  have htrace : WordTrace (prefixWord ++ tailWord_299129) baseStart_299129 baseEnd_299129 := by
    simpa [prefixWord, tailWord_299129, baseEnd_299129] using wordTrace_append hprefix tailTrace_299129
  have hstable : (prefixWord ++ tailWord_299129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299129).length < 2 ^ (prefixWord ++ tailWord_299129).sum := by decide
  have hdescent : baseEnd_299129 < baseStart_299129 := by decide
  rcases family_descends (prefixWord ++ tailWord_299129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299133 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_299133 : Nat := 118140960795 + 299133 * 2 ^ 59
def prefixEnd_299133 : Nat := 4983230072969 + 3 ^ 40 * 299133 * 2
def baseEnd_299133 : Nat := 102399339080988916307879

theorem tailTrace_299133 : CollatzResearch.WordTrace tailWord_299133 prefixEnd_299133 102399339080988916307879 := by
  unfold tailWord_299133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910276825299703694198053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7273517883533135796132035 10910276825299703694198053)
  ·
    refine ⟨2045676904743694442662135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10910276825299703694198053 2045676904743694442662135)
    ·
      refine ⟨3068515357115541663993203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2045676904743694442662135 3068515357115541663993203)
      ·
        refine ⟨4602773035673312495989805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068515357115541663993203 4602773035673312495989805)
        ·
          refine ⟨1726039888377492185996177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4602773035673312495989805 1726039888377492185996177)
          ·
            refine ⟨1294529916283119139497133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1726039888377492185996177 1294529916283119139497133)
            ·
              refine ⟨485448718606169677311425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1294529916283119139497133 485448718606169677311425)
              ·
                refine ⟨364086538954627257983569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485448718606169677311425 364086538954627257983569)
                ·
                  refine ⟨273064904215970443487677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364086538954627257983569 273064904215970443487677)
                  ·
                    refine ⟨102399339080988916307879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273064904215970443487677 102399339080988916307879)
                    ·
                      rfl

theorem cell22_299133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_299133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299133 prefixEnd_299133 := by exact prefixLift 299133
  have htrace : WordTrace (prefixWord ++ tailWord_299133) baseStart_299133 baseEnd_299133 := by
    simpa [prefixWord, tailWord_299133, baseEnd_299133] using wordTrace_append hprefix tailTrace_299133
  have hstable : (prefixWord ++ tailWord_299133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299133).length < 2 ^ (prefixWord ++ tailWord_299133).sum := by decide
  have hdescent : baseEnd_299133 < baseStart_299133 := by decide
  rcases family_descends (prefixWord ++ tailWord_299133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299150 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_299150 : Nat := 118140960795 + 299150 * 2 ^ 59
def prefixEnd_299150 : Nat := 4983230072969 + 3 ^ 40 * 299150 * 2
def baseEnd_299150 : Nat := 102405158528406538632827

theorem tailTrace_299150 : CollatzResearch.WordTrace tailWord_299150 prefixEnd_299150 102405158528406538632827 := by
  unfold tailWord_299150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363862108279764449695863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7273931244158743731711269 1363862108279764449695863)
  ·
    refine ⟨2045793162419646674543795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363862108279764449695863 2045793162419646674543795)
    ·
      refine ⟨3068689743629470011815693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2045793162419646674543795 3068689743629470011815693)
      ·
        refine ⟨1150758653861051254430885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3068689743629470011815693 1150758653861051254430885)
        ·
          refine ⟨215767247598947110205791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1150758653861051254430885 215767247598947110205791)
          ·
            refine ⟨323650871398420665308687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215767247598947110205791 323650871398420665308687)
            ·
              refine ⟨485476307097630997963031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323650871398420665308687 485476307097630997963031)
              ·
                refine ⟨728214460646446496944547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485476307097630997963031 728214460646446496944547)
                ·
                  refine ⟨1092321690969669745416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728214460646446496944547 1092321690969669745416821)
                  ·
                    refine ⟨102405158528406538632827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1092321690969669745416821 102405158528406538632827)
                    ·
                      rfl

theorem cell22_299150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_299150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299150 prefixEnd_299150 := by exact prefixLift 299150
  have htrace : WordTrace (prefixWord ++ tailWord_299150) baseStart_299150 baseEnd_299150 := by
    simpa [prefixWord, tailWord_299150, baseEnd_299150] using wordTrace_append hprefix tailTrace_299150
  have hstable : (prefixWord ++ tailWord_299150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299150).length < 2 ^ (prefixWord ++ tailWord_299150).sum := by decide
  have hdescent : baseEnd_299150 < baseStart_299150 := by decide
  rcases family_descends (prefixWord ++ tailWord_299150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299195 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 1, 3]
def baseStart_299195 : Nat := 118140960795 + 299195 * 2 ^ 59
def prefixEnd_299195 : Nat := 4983230072969 + 3 ^ 40 * 299195 * 2
def baseEnd_299195 : Nat := 102420562948041421257689

theorem tailTrace_299195 : CollatzResearch.WordTrace tailWord_299195 prefixEnd_299195 102420562948041421257689 := by
  unfold tailWord_299195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912538151075088282955039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7275025434050058855303359 10912538151075088282955039)
  ·
    refine ⟨16368807226612632424432559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10912538151075088282955039 16368807226612632424432559)
    ·
      refine ⟨24553210839918948636648839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16368807226612632424432559 24553210839918948636648839)
      ·
        refine ⟨36829816259878422954973259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24553210839918948636648839 36829816259878422954973259)
        ·
          refine ⟨55244724389817634432459889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36829816259878422954973259 55244724389817634432459889)
          ·
            refine ⟨41433543292363225824344917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55244724389817634432459889 41433543292363225824344917)
            ·
              refine ⟨242774667728690776314521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 41433543292363225824344917 242774667728690776314521)
              ·
                refine ⟨182081000796518082235891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242774667728690776314521 182081000796518082235891)
                ·
                  refine ⟨273121501194777123353837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182081000796518082235891 273121501194777123353837)
                  ·
                    refine ⟨102420562948041421257689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273121501194777123353837 102420562948041421257689)
                    ·
                      rfl

theorem cell22_299195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 3].length) (baseStart_299195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299195 prefixEnd_299195 := by exact prefixLift 299195
  have htrace : WordTrace (prefixWord ++ tailWord_299195) baseStart_299195 baseEnd_299195 := by
    simpa [prefixWord, tailWord_299195, baseEnd_299195] using wordTrace_append hprefix tailTrace_299195
  have hstable : (prefixWord ++ tailWord_299195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299195).length < 2 ^ (prefixWord ++ tailWord_299195).sum := by decide
  have hdescent : baseEnd_299195 < baseStart_299195 := by decide
  rcases family_descends (prefixWord ++ tailWord_299195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299332 : List Nat := [2, 3, 4, 1, 2, 2, 2, 6]
def baseStart_299332 : Nat := 118140960795 + 299332 * 2 ^ 59
def prefixEnd_299332 : Nat := 4983230072969 + 3 ^ 40 * 299332 * 2
def baseEnd_299332 : Nat := 11385273427535414509141

theorem tailTrace_299332 : CollatzResearch.WordTrace tailWord_299332 prefixEnd_299332 11385273427535414509141 := by
  unfold tailWord_299332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458767475789380340346125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7278356634385840453794833 5458767475789380340346125)
  ·
    refine ⟨2047037803421017627629797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5458767475789380340346125 2047037803421017627629797)
    ·
      refine ⟨383819588141440805180587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2047037803421017627629797 383819588141440805180587)
      ·
        refine ⟨575729382212161207770881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383819588141440805180587 575729382212161207770881)
        ·
          refine ⟨431797036659120905828161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575729382212161207770881 431797036659120905828161)
          ·
            refine ⟨323847777494340679371121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431797036659120905828161 323847777494340679371121)
            ·
              refine ⟨242885833120755509528341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323847777494340679371121 242885833120755509528341)
              ·
                refine ⟨11385273427535414509141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 242885833120755509528341 11385273427535414509141)
                ·
                  rfl

theorem cell22_299332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_299332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299332 prefixEnd_299332 := by exact prefixLift 299332
  have htrace : WordTrace (prefixWord ++ tailWord_299332) baseStart_299332 baseEnd_299332 := by
    simpa [prefixWord, tailWord_299332, baseEnd_299332] using wordTrace_append hprefix tailTrace_299332
  have hstable : (prefixWord ++ tailWord_299332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299332).length < 2 ^ (prefixWord ++ tailWord_299332).sum := by decide
  have hdescent : baseEnd_299332 < baseStart_299332 := by decide
  rcases family_descends (prefixWord ++ tailWord_299332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299373 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_299373 : Nat := 118140960795 + 299373 * 2 ^ 59
def prefixEnd_299373 : Nat := 4983230072969 + 3 ^ 40 * 299373 * 2
def baseEnd_299373 : Nat := 102481495985708290307143

theorem tailTrace_299373 : CollatzResearch.WordTrace tailWord_299373 prefixEnd_299373 102481495985708290307143 := by
  unfold tailWord_299373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10919030344430224682934773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7279353562953483121956515 10919030344430224682934773)
  ·
    refine ⟨1023659094790333564025135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10919030344430224682934773 1023659094790333564025135)
    ·
      refine ⟨1535488642185500346037703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023659094790333564025135 1535488642185500346037703)
      ·
        refine ⟨2303232963278250519056555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535488642185500346037703 2303232963278250519056555)
        ·
          refine ⟨3454849444917375778584833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303232963278250519056555 3454849444917375778584833)
          ·
            refine ⟨2591137083688031833938625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454849444917375778584833 2591137083688031833938625)
            ·
              refine ⟨1943352812766023875453969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591137083688031833938625 1943352812766023875453969)
              ·
                refine ⟨1457514609574517906590477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943352812766023875453969 1457514609574517906590477)
                ·
                  refine ⟨546567978590444214971429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457514609574517906590477 546567978590444214971429)
                  ·
                    refine ⟨102481495985708290307143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546567978590444214971429 102481495985708290307143)
                    ·
                      rfl

theorem cell22_299373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_299373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299373 prefixEnd_299373 := by exact prefixLift 299373
  have htrace : WordTrace (prefixWord ++ tailWord_299373) baseStart_299373 baseEnd_299373 := by
    simpa [prefixWord, tailWord_299373, baseEnd_299373] using wordTrace_append hprefix tailTrace_299373
  have hstable : (prefixWord ++ tailWord_299373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299373).length < 2 ^ (prefixWord ++ tailWord_299373).sum := by decide
  have hdescent : baseEnd_299373 < baseStart_299373 := by decide
  rcases family_descends (prefixWord ++ tailWord_299373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299403 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_299403 : Nat := 118140960795 + 299403 * 2 ^ 59
def prefixEnd_299403 : Nat := 4983230072969 + 3 ^ 40 * 299403 * 2
def baseEnd_299403 : Nat := 102491765598798212057051

theorem tailTrace_299403 : CollatzResearch.WordTrace tailWord_299403 prefixEnd_299403 102491765598798212057051 := by
  unfold tailWord_299403
  simp only [CollatzResearch.WordTrace]
  refine ⟨10920124534321539806526863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7280083022881026537684575 10920124534321539806526863)
  ·
    refine ⟨16380186801482309709790295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10920124534321539806526863 16380186801482309709790295)
    ·
      refine ⟨24570280202223464564685443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16380186801482309709790295 24570280202223464564685443)
      ·
        refine ⟨36855420303335196847028165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24570280202223464564685443 36855420303335196847028165)
        ·
          refine ⟨6910391306875349408817781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36855420303335196847028165 6910391306875349408817781)
          ·
            refine ⟨647849185019564007076667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6910391306875349408817781 647849185019564007076667)
            ·
              refine ⟨971773777529346010615001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647849185019564007076667 971773777529346010615001)
              ·
                refine ⟨728830333147009507961251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971773777529346010615001 728830333147009507961251)
                ·
                  refine ⟨1093245499720514261941877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728830333147009507961251 1093245499720514261941877)
                  ·
                    refine ⟨102491765598798212057051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1093245499720514261941877 102491765598798212057051)
                    ·
                      rfl

theorem cell22_299403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_299403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299403 prefixEnd_299403 := by exact prefixLift 299403
  have htrace : WordTrace (prefixWord ++ tailWord_299403) baseStart_299403 baseEnd_299403 := by
    simpa [prefixWord, tailWord_299403, baseEnd_299403] using wordTrace_append hprefix tailTrace_299403
  have hstable : (prefixWord ++ tailWord_299403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299403).length < 2 ^ (prefixWord ++ tailWord_299403).sum := by decide
  have hdescent : baseEnd_299403 < baseStart_299403 := by decide
  rcases family_descends (prefixWord ++ tailWord_299403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299437 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_299437 : Nat := 118140960795 + 299437 * 2 ^ 59
def prefixEnd_299437 : Nat := 4983230072969 + 3 ^ 40 * 299437 * 2
def baseEnd_299437 : Nat := 102503404493633456706947

theorem tailTrace_299437 : CollatzResearch.WordTrace tailWord_299437 prefixEnd_299437 102503404493633456706947 := by
  unfold tailWord_299437
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921364616198363613264565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7280909744132242408843043 10921364616198363613264565)
  ·
    refine ⟨1023877932768596588743553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10921364616198363613264565 1023877932768596588743553)
    ·
      refine ⟨767908449576447441557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023877932768596588743553 767908449576447441557665)
      ·
        refine ⟨575931337182335581168249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 767908449576447441557665 575931337182335581168249)
        ·
          refine ⟨431948502886751685876187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575931337182335581168249 431948502886751685876187)
          ·
            refine ⟨647922754330127528814281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431948502886751685876187 647922754330127528814281)
            ·
              refine ⟨485942065747595646610711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647922754330127528814281 485942065747595646610711)
              ·
                refine ⟨728913098621393469916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485942065747595646610711 728913098621393469916067)
                ·
                  refine ⟨1093369647932090204874101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728913098621393469916067 1093369647932090204874101)
                  ·
                    refine ⟨102503404493633456706947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1093369647932090204874101 102503404493633456706947)
                    ·
                      rfl

theorem cell22_299437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_299437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299437 prefixEnd_299437 := by exact prefixLift 299437
  have htrace : WordTrace (prefixWord ++ tailWord_299437) baseStart_299437 baseEnd_299437 := by
    simpa [prefixWord, tailWord_299437, baseEnd_299437] using wordTrace_append hprefix tailTrace_299437
  have hstable : (prefixWord ++ tailWord_299437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299437).length < 2 ^ (prefixWord ++ tailWord_299437).sum := by decide
  have hdescent : baseEnd_299437 < baseStart_299437 := by decide
  rcases family_descends (prefixWord ++ tailWord_299437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299452 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_299452 : Nat := 118140960795 + 299452 * 2 ^ 59
def prefixEnd_299452 : Nat := 4983230072969 + 3 ^ 40 * 299452 * 2
def baseEnd_299452 : Nat := 102508539300178417581901

theorem tailTrace_299452 : CollatzResearch.WordTrace tailWord_299452 prefixEnd_299452 102508539300178417581901 := by
  unfold tailWord_299452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460955855572010587530305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7281274474096014116707073 5460955855572010587530305)
  ·
    refine ⟨4095716891679007940647729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5460955855572010587530305 4095716891679007940647729)
    ·
      refine ⟨3071787668759255955485797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4095716891679007940647729 3071787668759255955485797)
      ·
        refine ⟨575960187892360491653587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3071787668759255955485797 575960187892360491653587)
        ·
          refine ⟨863940281838540737480381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575960187892360491653587 863940281838540737480381)
          ·
            refine ⟨323977605689452776555143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863940281838540737480381 323977605689452776555143)
            ·
              refine ⟨485966408534179164832715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323977605689452776555143 485966408534179164832715)
              ·
                refine ⟨728949612801268747249073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485966408534179164832715 728949612801268747249073)
                ·
                  refine ⟨546712209600951560436805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728949612801268747249073 546712209600951560436805)
                  ·
                    refine ⟨102508539300178417581901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546712209600951560436805 102508539300178417581901)
                    ·
                      rfl

theorem cell22_299452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_299452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299452 prefixEnd_299452 := by exact prefixLift 299452
  have htrace : WordTrace (prefixWord ++ tailWord_299452) baseStart_299452 baseEnd_299452 := by
    simpa [prefixWord, tailWord_299452, baseEnd_299452] using wordTrace_append hprefix tailTrace_299452
  have hstable : (prefixWord ++ tailWord_299452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299452).length < 2 ^ (prefixWord ++ tailWord_299452).sum := by decide
  have hdescent : baseEnd_299452 < baseStart_299452 := by decide
  rcases family_descends (prefixWord ++ tailWord_299452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299482 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_299482 : Nat := 118140960795 + 299482 * 2 ^ 59
def prefixEnd_299482 : Nat := 4983230072969 + 3 ^ 40 * 299482 * 2
def baseEnd_299482 : Nat := 102518808913268339331809

theorem tailTrace_299482 : CollatzResearch.WordTrace tailWord_299482 prefixEnd_299482 102518808913268339331809 := by
  unfold tailWord_299482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730751475258834074663175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7282003934023557532435133 2730751475258834074663175)
  ·
    refine ⟨4096127212888251111994763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730751475258834074663175 4096127212888251111994763)
    ·
      refine ⟨6144190819332376667992145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096127212888251111994763 6144190819332376667992145)
      ·
        refine ⟨4608143114499282500994109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6144190819332376667992145 4608143114499282500994109)
        ·
          refine ⟨1728053667937230937872791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4608143114499282500994109 1728053667937230937872791)
          ·
            refine ⟨2592080501905846406809187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728053667937230937872791 2592080501905846406809187)
            ·
              refine ⟨3888120752858769610213781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592080501905846406809187 3888120752858769610213781)
              ·
                refine ⟨182255660290254825478771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3888120752858769610213781 182255660290254825478771)
                ·
                  refine ⟨273383490435382238218157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182255660290254825478771 273383490435382238218157)
                  ·
                    refine ⟨102518808913268339331809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273383490435382238218157 102518808913268339331809)
                    ·
                      rfl

theorem cell22_299482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_299482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299482 prefixEnd_299482 := by exact prefixLift 299482
  have htrace : WordTrace (prefixWord ++ tailWord_299482) baseStart_299482 baseEnd_299482 := by
    simpa [prefixWord, tailWord_299482, baseEnd_299482] using wordTrace_append hprefix tailTrace_299482
  have hstable : (prefixWord ++ tailWord_299482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299482).length < 2 ^ (prefixWord ++ tailWord_299482).sum := by decide
  have hdescent : baseEnd_299482 < baseStart_299482 := by decide
  rcases family_descends (prefixWord ++ tailWord_299482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299525 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_299525 : Nat := 118140960795 + 299525 * 2 ^ 59
def prefixEnd_299525 : Nat := 4983230072969 + 3 ^ 40 * 299525 * 2
def baseEnd_299525 : Nat := 102533528692030560506677

theorem tailTrace_299525 : CollatzResearch.WordTrace tailWord_299525 prefixEnd_299525 102533528692030560506677 := by
  unfold tailWord_299525
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924574239879554642468029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7283049493253036428312019 10924574239879554642468029)
  ·
    refine ⟨4096715339954832990925511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10924574239879554642468029 4096715339954832990925511)
    ·
      refine ⟨6145073009932249486388267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096715339954832990925511 6145073009932249486388267)
      ·
        refine ⟨9217609514898374229582401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145073009932249486388267 9217609514898374229582401)
        ·
          refine ⟨6913207136173780672186801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9217609514898374229582401 6913207136173780672186801)
          ·
            refine ⟨5184905352130335504140101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6913207136173780672186801 5184905352130335504140101)
            ·
              refine ⟨972169753524437907026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5184905352130335504140101 972169753524437907026269)
              ·
                refine ⟨364563657571664215134851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 972169753524437907026269 364563657571664215134851)
                ·
                  refine ⟨546845486357496322702277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364563657571664215134851 546845486357496322702277)
                  ·
                    refine ⟨102533528692030560506677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546845486357496322702277 102533528692030560506677)
                    ·
                      rfl

theorem cell22_299525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_299525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299525 prefixEnd_299525 := by exact prefixLift 299525
  have htrace : WordTrace (prefixWord ++ tailWord_299525) baseStart_299525 baseEnd_299525 := by
    simpa [prefixWord, tailWord_299525, baseEnd_299525] using wordTrace_append hprefix tailTrace_299525
  have hstable : (prefixWord ++ tailWord_299525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299525).length < 2 ^ (prefixWord ++ tailWord_299525).sum := by decide
  have hdescent : baseEnd_299525 < baseStart_299525 := by decide
  rcases family_descends (prefixWord ++ tailWord_299525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299559 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 3, 4]
def baseStart_299559 : Nat := 118140960795 + 299559 * 2 ^ 59
def prefixEnd_299559 : Nat := 4983230072969 + 3 ^ 40 * 299559 * 2
def baseEnd_299559 : Nat := 102545167586865805156573

theorem tailTrace_299559 : CollatzResearch.WordTrace tailWord_299559 prefixEnd_299559 102545167586865805156573 := by
  unfold tailWord_299559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925814321756378449205731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7283876214504252299470487 10925814321756378449205731)
  ·
    refine ⟨16388721482634567673808597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925814321756378449205731 16388721482634567673808597)
    ·
      refine ⟨384110659749247679854889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16388721482634567673808597 384110659749247679854889)
      ·
        refine ⟨288082994811935759891167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384110659749247679854889 288082994811935759891167)
        ·
          refine ⟨432124492217903639836751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288082994811935759891167 432124492217903639836751)
          ·
            refine ⟨648186738326855459755127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432124492217903639836751 648186738326855459755127)
            ·
              refine ⟨972280107490283189632691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648186738326855459755127 972280107490283189632691)
              ·
                refine ⟨1458420161235424784449037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972280107490283189632691 1458420161235424784449037)
                ·
                  refine ⟨546907560463284294168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1458420161235424784449037 546907560463284294168389)
                  ·
                    refine ⟨102545167586865805156573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546907560463284294168389 102545167586865805156573)
                    ·
                      rfl

theorem cell22_299559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_299559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299559 prefixEnd_299559 := by exact prefixLift 299559
  have htrace : WordTrace (prefixWord ++ tailWord_299559) baseStart_299559 baseEnd_299559 := by
    simpa [prefixWord, tailWord_299559, baseEnd_299559] using wordTrace_append hprefix tailTrace_299559
  have hstable : (prefixWord ++ tailWord_299559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299559).length < 2 ^ (prefixWord ++ tailWord_299559).sum := by decide
  have hdescent : baseEnd_299559 < baseStart_299559 := by decide
  rcases family_descends (prefixWord ++ tailWord_299559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299568 : List Nat := [2, 1, 1, 1, 2, 3, 4, 8]
def baseStart_299568 : Nat := 118140960795 + 299568 * 2 ^ 59
def prefixEnd_299568 : Nat := 4983230072969 + 3 ^ 40 * 299568 * 2
def baseEnd_299568 : Nat := 11394249830088086853505

theorem tailTrace_299568 : CollatzResearch.WordTrace tailWord_299568 prefixEnd_299568 11394249830088086853505 := by
  unfold tailWord_299568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463071289361886493141679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7284095052482515324188905 5463071289361886493141679)
  ·
    refine ⟨8194606934042829739712519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5463071289361886493141679 8194606934042829739712519)
    ·
      refine ⟨12291910401064244609568779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8194606934042829739712519 12291910401064244609568779)
      ·
        refine ⟨18437865601596366914353169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12291910401064244609568779 18437865601596366914353169)
        ·
          refine ⟨13828399201197275185764877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18437865601596366914353169 13828399201197275185764877)
          ·
            refine ⟨5185649700448978194661829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13828399201197275185764877 5185649700448978194661829)
            ·
              refine ⟨972309318834183411499093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5185649700448978194661829 972309318834183411499093)
              ·
                refine ⟨11394249830088086853505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 972309318834183411499093 11394249830088086853505)
                ·
                  rfl

theorem cell22_299568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_299568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299568 prefixEnd_299568 := by exact prefixLift 299568
  have htrace : WordTrace (prefixWord ++ tailWord_299568) baseStart_299568 baseEnd_299568 := by
    simpa [prefixWord, tailWord_299568, baseEnd_299568] using wordTrace_append hprefix tailTrace_299568
  have hstable : (prefixWord ++ tailWord_299568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299568).length < 2 ^ (prefixWord ++ tailWord_299568).sum := by decide
  have hdescent : baseEnd_299568 < baseStart_299568 := by decide
  rcases family_descends (prefixWord ++ tailWord_299568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299570 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_299570 : Nat := 118140960795 + 299570 * 2 ^ 59
def prefixEnd_299570 : Nat := 4983230072969 + 3 ^ 40 * 299570 * 2
def baseEnd_299570 : Nat := 102548933111665443131539

theorem tailTrace_299570 : CollatzResearch.WordTrace tailWord_299570 prefixEnd_299570 102548933111665443131539 := by
  unfold tailWord_299570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731553881179131831964041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7284143683144351551904109 2731553881179131831964041)
  ·
    refine ⟨2048665410884348873973031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731553881179131831964041 2048665410884348873973031)
    ·
      refine ⟨3072998116326523310959547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048665410884348873973031 3072998116326523310959547)
      ·
        refine ⟨4609497174489784966439321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072998116326523310959547 4609497174489784966439321)
        ·
          refine ⟨3457122880867338724829491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4609497174489784966439321 3457122880867338724829491)
          ·
            refine ⟨5185684321301008087244237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457122880867338724829491 5185684321301008087244237)
            ·
              refine ⟨1944631620487878032716589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5185684321301008087244237 1944631620487878032716589)
              ·
                refine ⟨729236857682954262268721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1944631620487878032716589 729236857682954262268721)
                ·
                  refine ⟨546927643262215696701541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729236857682954262268721 546927643262215696701541)
                  ·
                    refine ⟨102548933111665443131539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546927643262215696701541 102548933111665443131539)
                    ·
                      rfl

theorem cell22_299570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_299570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299570 prefixEnd_299570 := by exact prefixLift 299570
  have htrace : WordTrace (prefixWord ++ tailWord_299570) baseStart_299570 baseEnd_299570 := by
    simpa [prefixWord, tailWord_299570, baseEnd_299570] using wordTrace_append hprefix tailTrace_299570
  have hstable : (prefixWord ++ tailWord_299570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299570).length < 2 ^ (prefixWord ++ tailWord_299570).sum := by decide
  have hdescent : baseEnd_299570 < baseStart_299570 := by decide
  rcases family_descends (prefixWord ++ tailWord_299570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299617 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_299617 : Nat := 118140960795 + 299617 * 2 ^ 59
def prefixEnd_299617 : Nat := 4983230072969 + 3 ^ 40 * 299617 * 2
def baseEnd_299617 : Nat := 102565022172172987206395

theorem tailTrace_299617 : CollatzResearch.WordTrace tailWord_299617 prefixEnd_299617 102565022172172987206395 := by
  unfold tailWord_299617
  simp only [CollatzResearch.WordTrace]
  refine ⟨10927929755546254354817105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7285286503697502903211403 10927929755546254354817105)
  ·
    refine ⟨8195947316659690766112829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10927929755546254354817105 8195947316659690766112829)
    ·
      refine ⟨3073480243747384037292311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8195947316659690766112829 3073480243747384037292311)
      ·
        refine ⟨4610220365621076055938467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073480243747384037292311 4610220365621076055938467)
        ·
          refine ⟨6915330548431614083907701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610220365621076055938467 6915330548431614083907701)
          ·
            refine ⟨648312238915463820366347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6915330548431614083907701 648312238915463820366347)
            ·
              refine ⟨972468358373195730549521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648312238915463820366347 972468358373195730549521)
              ·
                refine ⟨729351268779896797912141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972468358373195730549521 729351268779896797912141)
                ·
                  refine ⟨273506725792461299217053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729351268779896797912141 273506725792461299217053)
                  ·
                    refine ⟨102565022172172987206395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273506725792461299217053 102565022172172987206395)
                    ·
                      rfl

theorem cell22_299617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_299617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299617 prefixEnd_299617 := by exact prefixLift 299617
  have htrace : WordTrace (prefixWord ++ tailWord_299617) baseStart_299617 baseEnd_299617 := by
    simpa [prefixWord, tailWord_299617, baseEnd_299617] using wordTrace_append hprefix tailTrace_299617
  have hstable : (prefixWord ++ tailWord_299617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299617).length < 2 ^ (prefixWord ++ tailWord_299617).sum := by decide
  have hdescent : baseEnd_299617 < baseStart_299617 := by decide
  rcases family_descends (prefixWord ++ tailWord_299617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299660 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_299660 : Nat := 118140960795 + 299660 * 2 ^ 59
def prefixEnd_299660 : Nat := 4983230072969 + 3 ^ 40 * 299660 * 2
def baseEnd_299660 : Nat := 102579741950935208381263

theorem tailTrace_299660 : CollatzResearch.WordTrace tailWord_299660 prefixEnd_299660 102579741950935208381263 := by
  unfold tailWord_299660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464749047195236349316217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7286332062926981799088289 5464749047195236349316217)
  ·
    refine ⟨4098561785396427261987163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5464749047195236349316217 4098561785396427261987163)
    ·
      refine ⟨6147842678094640892980745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098561785396427261987163 6147842678094640892980745)
      ·
        refine ⟨4610882008570980669735559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6147842678094640892980745 4610882008570980669735559)
        ·
          refine ⟨6916323012856471004603339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610882008570980669735559 6916323012856471004603339)
          ·
            refine ⟨10374484519284706506905009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916323012856471004603339 10374484519284706506905009)
            ·
              refine ⟨7780863389463529880178757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10374484519284706506905009 7780863389463529880178757)
              ·
                refine ⟨1458911885524411852533517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7780863389463529880178757 1458911885524411852533517)
                ·
                  refine ⟨547091957071654444700069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1458911885524411852533517 547091957071654444700069)
                  ·
                    refine ⟨102579741950935208381263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547091957071654444700069 102579741950935208381263)
                    ·
                      rfl

theorem cell22_299660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_299660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299660 prefixEnd_299660 := by exact prefixLift 299660
  have htrace : WordTrace (prefixWord ++ tailWord_299660) baseStart_299660 baseEnd_299660 := by
    simpa [prefixWord, tailWord_299660, baseEnd_299660] using wordTrace_append hprefix tailTrace_299660
  have hstable : (prefixWord ++ tailWord_299660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299660).length < 2 ^ (prefixWord ++ tailWord_299660).sum := by decide
  have hdescent : baseEnd_299660 < baseStart_299660 := by decide
  rcases family_descends (prefixWord ++ tailWord_299660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299677 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_299677 : Nat := 118140960795 + 299677 * 2 ^ 59
def prefixEnd_299677 : Nat := 4983230072969 + 3 ^ 40 * 299677 * 2
def baseEnd_299677 : Nat := 102585561398352830706211

theorem tailTrace_299677 : CollatzResearch.WordTrace tailWord_299677 prefixEnd_299677 102585561398352830706211 := by
  unfold tailWord_299677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10930118135328884602001285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7286745423552589734667523 10930118135328884602001285)
  ·
    refine ⟨2049397150374165862875241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10930118135328884602001285 2049397150374165862875241)
    ·
      refine ⟨1537047862780624397156431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049397150374165862875241 1537047862780624397156431)
      ·
        refine ⟨2305571794170936595734647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537047862780624397156431 2305571794170936595734647)
        ·
          refine ⟨3458357691256404893601971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305571794170936595734647 3458357691256404893601971)
          ·
            refine ⟨5187536536884607340402957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458357691256404893601971 5187536536884607340402957)
            ·
              refine ⟨1945326201331727752651109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5187536536884607340402957 1945326201331727752651109)
              ·
                refine ⟨364748662749698953622083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1945326201331727752651109 364748662749698953622083)
                ·
                  refine ⟨547122994124548430433125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364748662749698953622083 547122994124548430433125)
                  ·
                    refine ⟨102585561398352830706211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547122994124548430433125 102585561398352830706211)
                    ·
                      rfl

theorem cell22_299677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_299677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299677 prefixEnd_299677 := by exact prefixLift 299677
  have htrace : WordTrace (prefixWord ++ tailWord_299677) baseStart_299677 baseEnd_299677 := by
    simpa [prefixWord, tailWord_299677, baseEnd_299677] using wordTrace_append hprefix tailTrace_299677
  have hstable : (prefixWord ++ tailWord_299677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299677).length < 2 ^ (prefixWord ++ tailWord_299677).sum := by decide
  have hdescent : baseEnd_299677 < baseStart_299677 := by decide
  rcases family_descends (prefixWord ++ tailWord_299677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299720 : List Nat := [2, 1, 3, 1, 2, 3, 1, 9]
def baseStart_299720 : Nat := 118140960795 + 299720 * 2 ^ 59
def prefixEnd_299720 : Nat := 4983230072969 + 3 ^ 40 * 299720 * 2
def baseEnd_299720 : Nat := 11400031241901672431231

theorem tailTrace_299720 : CollatzResearch.WordTrace tailWord_299720 prefixEnd_299720 11400031241901672431231 := by
  unfold tailWord_299720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465843237086551472908307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7287790982782068630544409 5465843237086551472908307)
  ·
    refine ⟨8198764855629827209362461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5465843237086551472908307 8198764855629827209362461)
    ·
      refine ⟨3074536820861185203510923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8198764855629827209362461 3074536820861185203510923)
      ·
        refine ⟨4611805231291777805266385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074536820861185203510923 4611805231291777805266385)
        ·
          refine ⟨3458853923468833353949789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611805231291777805266385 3458853923468833353949789)
          ·
            refine ⟨1297070221300812507731171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3458853923468833353949789 1297070221300812507731171)
            ·
              refine ⟨1945605331951218761596757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297070221300812507731171 1945605331951218761596757)
              ·
                refine ⟨11400031241901672431231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1945605331951218761596757 11400031241901672431231)
                ·
                  rfl

theorem cell22_299720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_299720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299720 prefixEnd_299720 := by exact prefixLift 299720
  have htrace : WordTrace (prefixWord ++ tailWord_299720) baseStart_299720 baseEnd_299720 := by
    simpa [prefixWord, tailWord_299720, baseEnd_299720] using wordTrace_append hprefix tailTrace_299720
  have hstable : (prefixWord ++ tailWord_299720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299720).length < 2 ^ (prefixWord ++ tailWord_299720).sum := by decide
  have hdescent : baseEnd_299720 < baseStart_299720 := by decide
  rcases family_descends (prefixWord ++ tailWord_299720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299827 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 6]
def baseStart_299827 : Nat := 118140960795 + 299827 * 2 ^ 59
def prefixEnd_299827 : Nat := 4983230072969 + 3 ^ 40 * 299827 * 2
def baseEnd_299827 : Nat := 34212303154600813151917

theorem tailTrace_299827 : CollatzResearch.WordTrace tailWord_299827 prefixEnd_299827 34212303154600813151917 := by
  unfold tailWord_299827
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935589084785460219961735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7290392723190306813307823 10935589084785460219961735)
  ·
    refine ⟨16403383627178190329942603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10935589084785460219961735 16403383627178190329942603)
    ·
      refine ⟨24605075440767285494913905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16403383627178190329942603 24605075440767285494913905)
      ·
        refine ⟨18453806580575464121185429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24605075440767285494913905 18453806580575464121185429)
        ·
          refine ⟨865022183464474880680567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18453806580575464121185429 865022183464474880680567)
          ·
            refine ⟨1297533275196712321020851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865022183464474880680567 1297533275196712321020851)
            ·
              refine ⟨1946299912795068481531277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297533275196712321020851 1946299912795068481531277)
              ·
                refine ⟨729862467298150680574229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1946299912795068481531277 729862467298150680574229)
                ·
                  refine ⟨34212303154600813151917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 729862467298150680574229 34212303154600813151917)
                  ·
                    rfl

theorem cell22_299827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_299827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299827 prefixEnd_299827 := by exact prefixLift 299827
  have htrace : WordTrace (prefixWord ++ tailWord_299827) baseStart_299827 baseEnd_299827 := by
    simpa [prefixWord, tailWord_299827, baseEnd_299827] using wordTrace_append hprefix tailTrace_299827
  have hstable : (prefixWord ++ tailWord_299827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299827).length < 2 ^ (prefixWord ++ tailWord_299827).sum := by decide
  have hdescent : baseEnd_299827 < baseStart_299827 := by decide
  rcases family_descends (prefixWord ++ tailWord_299827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299893 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_299893 : Nat := 118140960795 + 299893 * 2 ^ 59
def prefixEnd_299893 : Nat := 4983230072969 + 3 ^ 40 * 299893 * 2
def baseEnd_299893 : Nat := 102659502612600267305549

theorem tailTrace_299893 : CollatzResearch.WordTrace tailWord_299893 prefixEnd_299893 102659502612600267305549 := by
  unfold tailWord_299893
  simp only [CollatzResearch.WordTrace]
  refine ⟨10937996302546353491864333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7291997535030902327909555 10937996302546353491864333)
  ·
    refine ⟨4101748613454882559449125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10937996302546353491864333 4101748613454882559449125)
    ·
      refine ⟨769077865022790479896711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4101748613454882559449125 769077865022790479896711)
      ·
        refine ⟨1153616797534185719845067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769077865022790479896711 1153616797534185719845067)
        ·
          refine ⟨1730425196301278579767601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153616797534185719845067 1730425196301278579767601)
          ·
            refine ⟨1297818897225958934825701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730425196301278579767601 1297818897225958934825701)
            ·
              refine ⟨243341043229867300279819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1297818897225958934825701 243341043229867300279819)
              ·
                refine ⟨365011564844800950419729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243341043229867300279819 365011564844800950419729)
                ·
                  refine ⟨273758673633600712814797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365011564844800950419729 273758673633600712814797)
                  ·
                    refine ⟨102659502612600267305549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273758673633600712814797 102659502612600267305549)
                    ·
                      rfl

theorem cell22_299893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_299893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299893 prefixEnd_299893 := by exact prefixLift 299893
  have htrace : WordTrace (prefixWord ++ tailWord_299893) baseStart_299893 baseEnd_299893 := by
    simpa [prefixWord, tailWord_299893, baseEnd_299893] using wordTrace_append hprefix tailTrace_299893
  have hstable : (prefixWord ++ tailWord_299893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299893).length < 2 ^ (prefixWord ++ tailWord_299893).sum := by decide
  have hdescent : baseEnd_299893 < baseStart_299893 := by decide
  rcases family_descends (prefixWord ++ tailWord_299893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299921 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_299921 : Nat := 118140960795 + 299921 * 2 ^ 59
def prefixEnd_299921 : Nat := 4983230072969 + 3 ^ 40 * 299921 * 2
def baseEnd_299921 : Nat := 102669087584817527605463

theorem tailTrace_299921 : CollatzResearch.WordTrace tailWord_299921 prefixEnd_299921 102669087584817527605463 := by
  unfold tailWord_299921
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939017546444914273883617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7292678364296609515922411 10939017546444914273883617)
  ·
    refine ⟨8204263159833685705412713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10939017546444914273883617 8204263159833685705412713)
    ·
      refine ⟨6153197369875264279059535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8204263159833685705412713 6153197369875264279059535)
      ·
        refine ⟨9229796054812896418589303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153197369875264279059535 9229796054812896418589303)
        ·
          refine ⟨13844694082219344627883955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9229796054812896418589303 13844694082219344627883955)
          ·
            refine ⟨20767041123329016941825933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13844694082219344627883955 20767041123329016941825933)
            ·
              refine ⟨7787640421248381353184725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20767041123329016941825933 7787640421248381353184725)
              ·
                refine ⟨182522822373008937965267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7787640421248381353184725 182522822373008937965267)
                ·
                  refine ⟨273784233559513406947901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182522822373008937965267 273784233559513406947901)
                  ·
                    refine ⟨102669087584817527605463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273784233559513406947901 102669087584817527605463)
                    ·
                      rfl

theorem cell22_299921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_299921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299921 prefixEnd_299921 := by exact prefixLift 299921
  have htrace : WordTrace (prefixWord ++ tailWord_299921) baseStart_299921 baseEnd_299921 := by
    simpa [prefixWord, tailWord_299921, baseEnd_299921] using wordTrace_append hprefix tailTrace_299921
  have hstable : (prefixWord ++ tailWord_299921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299921).length < 2 ^ (prefixWord ++ tailWord_299921).sum := by decide
  have hdescent : baseEnd_299921 < baseStart_299921 := by decide
  rcases family_descends (prefixWord ++ tailWord_299921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299972 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_299972 : Nat := 118140960795 + 299972 * 2 ^ 59
def prefixEnd_299972 : Nat := 4983230072969 + 3 ^ 40 * 299972 * 2
def baseEnd_299972 : Nat := 102686545927070394580307

theorem tailTrace_299972 : CollatzResearch.WordTrace tailWord_299972 prefixEnd_299972 102686545927070394580307 := by
  unfold tailWord_299972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470438834630074991995085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7293918446173433322660113 5470438834630074991995085)
  ·
    refine ⟨2051414562986278121998157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5470438834630074991995085 2051414562986278121998157)
    ·
      refine ⟨769280461119854295749309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2051414562986278121998157 769280461119854295749309)
      ·
        refine ⟨288480172919945360905991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 769280461119854295749309 288480172919945360905991)
        ·
          refine ⟨432720259379918041358987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288480172919945360905991 432720259379918041358987)
          ·
            refine ⟨649080389069877062038481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432720259379918041358987 649080389069877062038481)
            ·
              refine ⟨486810291802407796528861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649080389069877062038481 486810291802407796528861)
              ·
                refine ⟨182553859425902923698323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 486810291802407796528861 182553859425902923698323)
                ·
                  refine ⟨273830789138854385547485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182553859425902923698323 273830789138854385547485)
                  ·
                    refine ⟨102686545927070394580307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 273830789138854385547485 102686545927070394580307)
                    ·
                      rfl

theorem cell22_299972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_299972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_299972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_299972 prefixEnd_299972 := by exact prefixLift 299972
  have htrace : WordTrace (prefixWord ++ tailWord_299972) baseStart_299972 baseEnd_299972 := by
    simpa [prefixWord, tailWord_299972, baseEnd_299972] using wordTrace_append hprefix tailTrace_299972
  have hstable : (prefixWord ++ tailWord_299972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299972).length < 2 ^ (prefixWord ++ tailWord_299972).sum := by decide
  have hdescent : baseEnd_299972 < baseStart_299972 := by decide
  rcases family_descends (prefixWord ++ tailWord_299972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300116 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_300116 : Nat := 118140960795 + 300116 * 2 ^ 59
def prefixEnd_300116 : Nat := 4983230072969 + 3 ^ 40 * 300116 * 2
def baseEnd_300116 : Nat := 102735840069902018979865

theorem tailTrace_300116 : CollatzResearch.WordTrace tailWord_300116 prefixEnd_300116 102735840069902018979865 := by
  unfold tailWord_300116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473064890369231288616101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7297419853825641718154801 5473064890369231288616101)
  ·
    refine ⟨1026199666944230866615519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5473064890369231288616101 1026199666944230866615519)
    ·
      refine ⟨1539299500416346299923279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026199666944230866615519 1539299500416346299923279)
      ·
        refine ⟨2308949250624519449884919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539299500416346299923279 2308949250624519449884919)
        ·
          refine ⟨3463423875936779174827379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308949250624519449884919 3463423875936779174827379)
          ·
            refine ⟨5195135813905168762241069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463423875936779174827379 5195135813905168762241069)
            ·
              refine ⟨1948175930214438285840401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5195135813905168762241069 1948175930214438285840401)
              ·
                refine ⟨1461131947660828714380301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948175930214438285840401 1461131947660828714380301)
                ·
                  refine ⟨547924480372810767892613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1461131947660828714380301 547924480372810767892613)
                  ·
                    refine ⟨102735840069902018979865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547924480372810767892613 102735840069902018979865)
                    ·
                      rfl

theorem cell22_300116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_300116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300116 prefixEnd_300116 := by exact prefixLift 300116
  have htrace : WordTrace (prefixWord ++ tailWord_300116) baseStart_300116 baseEnd_300116 := by
    simpa [prefixWord, tailWord_300116, baseEnd_300116] using wordTrace_append hprefix tailTrace_300116
  have hstable : (prefixWord ++ tailWord_300116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300116).length < 2 ^ (prefixWord ++ tailWord_300116).sum := by decide
  have hdescent : baseEnd_300116 < baseStart_300116 := by decide
  rcases family_descends (prefixWord ++ tailWord_300116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300146 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_300146 : Nat := 118140960795 + 300146 * 2 ^ 59
def prefixEnd_300146 : Nat := 4983230072969 + 3 ^ 40 * 300146 * 2
def baseEnd_300146 : Nat := 102746109682991940729773

theorem tailTrace_300146 : CollatzResearch.WordTrace tailWord_300146 prefixEnd_300146 102746109682991940729773 := by
  unfold tailWord_300146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736805992657444425206073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7298149313753185133882861 2736805992657444425206073)
  ·
    refine ⟨2052604494493083318904555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2736805992657444425206073 2052604494493083318904555)
    ·
      refine ⟨3078906741739624978356833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052604494493083318904555 3078906741739624978356833)
      ·
        refine ⟨2309180056304718733767625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078906741739624978356833 2309180056304718733767625)
        ·
          refine ⟨1731885042228539050325719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2309180056304718733767625 1731885042228539050325719)
          ·
            refine ⟨2597827563342808575488579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731885042228539050325719 2597827563342808575488579)
            ·
              refine ⟨3896741345014212863232869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597827563342808575488579 3896741345014212863232869)
              ·
                refine ⟨730639002190164911856163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3896741345014212863232869 730639002190164911856163)
                ·
                  refine ⟨1095958503285247367784245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730639002190164911856163 1095958503285247367784245)
                  ·
                    refine ⟨102746109682991940729773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1095958503285247367784245 102746109682991940729773)
                    ·
                      rfl

theorem cell22_300146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_300146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300146 prefixEnd_300146 := by exact prefixLift 300146
  have htrace : WordTrace (prefixWord ++ tailWord_300146) baseStart_300146 baseEnd_300146 := by
    simpa [prefixWord, tailWord_300146, baseEnd_300146] using wordTrace_append hprefix tailTrace_300146
  have hstable : (prefixWord ++ tailWord_300146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300146).length < 2 ^ (prefixWord ++ tailWord_300146).sum := by decide
  have hdescent : baseEnd_300146 < baseStart_300146 := by decide
  rcases family_descends (prefixWord ++ tailWord_300146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300221 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 7]
def baseStart_300221 : Nat := 118140960795 + 300221 * 2 ^ 59
def prefixEnd_300221 : Nat := 4983230072969 + 3 ^ 40 * 300221 * 2
def baseEnd_300221 : Nat := 34257261238572248368181

theorem tailTrace_300221 : CollatzResearch.WordTrace tailWord_300221 prefixEnd_300221 34257261238572248368181 := by
  unfold tailWord_300221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10949959445358065509804517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7299972963572043673203011 10949959445358065509804517)
  ·
    refine ⟨2053117396004637283088347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10949959445358065509804517 2053117396004637283088347)
    ·
      refine ⟨3079676094006955924632521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053117396004637283088347 3079676094006955924632521)
      ·
        refine ⟨2309757070505216943474391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3079676094006955924632521 2309757070505216943474391)
        ·
          refine ⟨3464635605757825415211587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2309757070505216943474391 3464635605757825415211587)
          ·
            refine ⟨5196953408636738122817381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464635605757825415211587 5196953408636738122817381)
            ·
              refine ⟨974428764119388398028259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5196953408636738122817381 974428764119388398028259)
              ·
                refine ⟨1461643146179082597042389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974428764119388398028259 1461643146179082597042389)
                ·
                  refine ⟨34257261238572248368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1461643146179082597042389 34257261238572248368181)
                  ·
                    rfl

theorem cell22_300221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_300221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300221 prefixEnd_300221 := by exact prefixLift 300221
  have htrace : WordTrace (prefixWord ++ tailWord_300221) baseStart_300221 baseEnd_300221 := by
    simpa [prefixWord, tailWord_300221, baseEnd_300221] using wordTrace_append hprefix tailTrace_300221
  have hstable : (prefixWord ++ tailWord_300221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300221).length < 2 ^ (prefixWord ++ tailWord_300221).sum := by decide
  have hdescent : baseEnd_300221 < baseStart_300221 := by decide
  rcases family_descends (prefixWord ++ tailWord_300221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300281 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_300281 : Nat := 118140960795 + 300281 * 2 ^ 59
def prefixEnd_300281 : Nat := 4983230072969 + 3 ^ 40 * 300281 * 2
def baseEnd_300281 : Nat := 102792322941896588604359

theorem tailTrace_300281 : CollatzResearch.WordTrace tailWord_300281 prefixEnd_300281 102792322941896588604359 := by
  unfold tailWord_300281
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952147825140695756988697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7301431883427130504659131 10952147825140695756988697)
  ·
    refine ⟨8214110868855521817741523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10952147825140695756988697 8214110868855521817741523)
    ·
      refine ⟨12321166303283282726612285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8214110868855521817741523 12321166303283282726612285)
      ·
        refine ⟨4620437363731231022479607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12321166303283282726612285 4620437363731231022479607)
        ·
          refine ⟨6930656045596846533719411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620437363731231022479607 6930656045596846533719411)
          ·
            refine ⟨10395984068395269800579117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6930656045596846533719411 10395984068395269800579117)
            ·
              refine ⟨3898494025648226175217169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10395984068395269800579117 3898494025648226175217169)
              ·
                refine ⟨2923870519236169631412877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898494025648226175217169 2923870519236169631412877)
                ·
                  refine ⟨1096451444713563611779829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2923870519236169631412877 1096451444713563611779829)
                  ·
                    refine ⟨102792322941896588604359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1096451444713563611779829 102792322941896588604359)
                    ·
                      rfl

theorem cell22_300281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_300281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300281 prefixEnd_300281 := by exact prefixLift 300281
  have htrace : WordTrace (prefixWord ++ tailWord_300281) baseStart_300281 baseEnd_300281 := by
    simpa [prefixWord, tailWord_300281, baseEnd_300281] using wordTrace_append hprefix tailTrace_300281
  have hstable : (prefixWord ++ tailWord_300281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300281).length < 2 ^ (prefixWord ++ tailWord_300281).sum := by decide
  have hdescent : baseEnd_300281 < baseStart_300281 := by decide
  rcases family_descends (prefixWord ++ tailWord_300281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300298 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_300298 : Nat := 118140960795 + 300298 * 2 ^ 59
def prefixEnd_300298 : Nat := 4983230072969 + 3 ^ 40 * 300298 * 2
def baseEnd_300298 : Nat := 102798142389314210929307

theorem tailTrace_300298 : CollatzResearch.WordTrace tailWord_300298 prefixEnd_300298 102798142389314210929307 := by
  unfold tailWord_300298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738191966519776915089387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7301845244052738440238365 2738191966519776915089387)
  ·
    refine ⟨4107287949779665372634081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738191966519776915089387 4107287949779665372634081)
    ·
      refine ⟨3080465962334749029475561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4107287949779665372634081 3080465962334749029475561)
      ·
        refine ⟨2310349471751061772106671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3080465962334749029475561 2310349471751061772106671)
        ·
          refine ⟨3465524207626592658160007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310349471751061772106671 3465524207626592658160007)
          ·
            refine ⟨5198286311439888987240011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3465524207626592658160007 5198286311439888987240011)
            ·
              refine ⟨7797429467159833480860017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5198286311439888987240011 7797429467159833480860017)
              ·
                refine ⟨5848072100369875110645013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7797429467159833480860017 5848072100369875110645013)
                ·
                  refine ⟨274128379704837895811485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5848072100369875110645013 274128379704837895811485)
                  ·
                    refine ⟨102798142389314210929307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274128379704837895811485 102798142389314210929307)
                    ·
                      rfl

theorem cell22_300298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_300298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300298 prefixEnd_300298 := by exact prefixLift 300298
  have htrace : WordTrace (prefixWord ++ tailWord_300298) baseStart_300298 baseEnd_300298 := by
    simpa [prefixWord, tailWord_300298, baseEnd_300298] using wordTrace_append hprefix tailTrace_300298
  have hstable : (prefixWord ++ tailWord_300298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300298).length < 2 ^ (prefixWord ++ tailWord_300298).sum := by decide
  have hdescent : baseEnd_300298 < baseStart_300298 := by decide
  rcases family_descends (prefixWord ++ tailWord_300298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300317 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 4]
def baseStart_300317 : Nat := 118140960795 + 300317 * 2 ^ 59
def prefixEnd_300317 : Nat := 4983230072969 + 3 ^ 40 * 300317 * 2
def baseEnd_300317 : Nat := 34268215492534831568083

theorem tailTrace_300317 : CollatzResearch.WordTrace tailWord_300317 prefixEnd_300317 34268215492534831568083 := by
  unfold tailWord_300317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10953460853010273905299205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7302307235340182603532803 10953460853010273905299205)
  ·
    refine ⟨2053773909939426357243601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10953460853010273905299205 2053773909939426357243601)
    ·
      refine ⟨1540330432454569767932701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2053773909939426357243601 1540330432454569767932701)
      ·
        refine ⟨577623912170463662974763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1540330432454569767932701 577623912170463662974763)
        ·
          refine ⟨866435868255695494462145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577623912170463662974763 866435868255695494462145)
          ·
            refine ⟨649826901191771620846609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866435868255695494462145 649826901191771620846609)
            ·
              refine ⟨487370175893828715634957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649826901191771620846609 487370175893828715634957)
              ·
                refine ⟨182763815960185768363109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487370175893828715634957 182763815960185768363109)
                ·
                  refine ⟨34268215492534831568083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182763815960185768363109 34268215492534831568083)
                  ·
                    rfl

theorem cell22_300317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_300317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300317 prefixEnd_300317 := by exact prefixLift 300317
  have htrace : WordTrace (prefixWord ++ tailWord_300317) baseStart_300317 baseEnd_300317 := by
    simpa [prefixWord, tailWord_300317, baseEnd_300317] using wordTrace_append hprefix tailTrace_300317
  have hstable : (prefixWord ++ tailWord_300317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300317).length < 2 ^ (prefixWord ++ tailWord_300317).sum := by decide
  have hdescent : baseEnd_300317 < baseStart_300317 := by decide
  rcases family_descends (prefixWord ++ tailWord_300317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300319 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 1, 4]
def baseStart_300319 : Nat := 118140960795 + 300319 * 2 ^ 59
def prefixEnd_300319 : Nat := 4983230072969 + 3 ^ 40 * 300319 * 2
def baseEnd_300319 : Nat := 102805331118477156154243

theorem tailTrace_300319 : CollatzResearch.WordTrace tailWord_300319 prefixEnd_300319 102805331118477156154243 := by
  unfold tailWord_300319
  simp only [CollatzResearch.WordTrace]
  refine ⟨10953533799003028246872011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7302355866002018831248007 10953533799003028246872011)
  ·
    refine ⟨16430300698504542370308017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10953533799003028246872011 16430300698504542370308017)
    ·
      refine ⟨12322725523878406777731013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16430300698504542370308017 12322725523878406777731013)
      ·
        refine ⟨2310511035727201270824565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12322725523878406777731013 2310511035727201270824565)
        ·
          refine ⟨216610409599425119139803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2310511035727201270824565 216610409599425119139803)
          ·
            refine ⟨324915614399137678709705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216610409599425119139803 324915614399137678709705)
            ·
              refine ⟨243686710799353259032279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324915614399137678709705 243686710799353259032279)
              ·
                refine ⟨365530066199029888548419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243686710799353259032279 365530066199029888548419)
                ·
                  refine ⟨548295099298544832822629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365530066199029888548419 548295099298544832822629)
                  ·
                    refine ⟨102805331118477156154243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548295099298544832822629 102805331118477156154243)
                    ·
                      rfl

theorem cell22_300319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_300319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300319 prefixEnd_300319 := by exact prefixLift 300319
  have htrace : WordTrace (prefixWord ++ tailWord_300319) baseStart_300319 baseEnd_300319 := by
    simpa [prefixWord, tailWord_300319, baseEnd_300319] using wordTrace_append hprefix tailTrace_300319
  have hstable : (prefixWord ++ tailWord_300319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300319).length < 2 ^ (prefixWord ++ tailWord_300319).sum := by decide
  have hdescent : baseEnd_300319 < baseStart_300319 := by decide
  rcases family_descends (prefixWord ++ tailWord_300319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300328 : List Nat := [2, 1, 5, 1, 2, 2, 9]
def baseStart_300328 : Nat := 118140960795 + 300328 * 2 ^ 59
def prefixEnd_300328 : Nat := 4983230072969 + 3 ^ 40 * 300328 * 2
def baseEnd_300328 : Nat := 3807718963052004914045

theorem tailTrace_300328 : CollatzResearch.WordTrace tailWord_300328 prefixEnd_300328 3807718963052004914045 := by
  unfold tailWord_300328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476931027985211391974819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7302574703980281855966425 5476931027985211391974819)
  ·
    refine ⟨8215396541977817087962229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5476931027985211391974819 8215396541977817087962229)
    ·
      refine ⟨770193425810420351996459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8215396541977817087962229 770193425810420351996459)
      ·
        refine ⟨1155290138715630527994689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770193425810420351996459 1155290138715630527994689)
        ·
          refine ⟨866467604036722895996017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155290138715630527994689 866467604036722895996017)
          ·
            refine ⟨649850703027542171997013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866467604036722895996017 649850703027542171997013)
            ·
              refine ⟨3807718963052004914045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 649850703027542171997013 3807718963052004914045)
              ·
                rfl

theorem cell22_300328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 9].length) (baseStart_300328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300328 prefixEnd_300328 := by exact prefixLift 300328
  have htrace : WordTrace (prefixWord ++ tailWord_300328) baseStart_300328 baseEnd_300328 := by
    simpa [prefixWord, tailWord_300328, baseEnd_300328] using wordTrace_append hprefix tailTrace_300328
  have hstable : (prefixWord ++ tailWord_300328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300328).length < 2 ^ (prefixWord ++ tailWord_300328).sum := by decide
  have hdescent : baseEnd_300328 < baseStart_300328 := by decide
  rcases family_descends (prefixWord ++ tailWord_300328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300349 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_300349 : Nat := 118140960795 + 300349 * 2 ^ 59
def prefixEnd_300349 : Nat := 4983230072969 + 3 ^ 40 * 300349 * 2
def baseEnd_300349 : Nat := 102815600731567077904151

theorem tailTrace_300349 : CollatzResearch.WordTrace tailWord_300349 prefixEnd_300349 102815600731567077904151 := by
  unfold tailWord_300349
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954627988894343370464101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7303085325929562246976067 10954627988894343370464101)
  ·
    refine ⟨2053992747917689381962019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10954627988894343370464101 2053992747917689381962019)
    ·
      refine ⟨3080989121876534072943029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053992747917689381962019 3080989121876534072943029)
      ·
        refine ⟨288842730175925069338409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3080989121876534072943029 288842730175925069338409)
        ·
          refine ⟨216632047631943802003807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288842730175925069338409 216632047631943802003807)
          ·
            refine ⟨324948071447915703005711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216632047631943802003807 324948071447915703005711)
            ·
              refine ⟨487422107171873554508567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324948071447915703005711 487422107171873554508567)
              ·
                refine ⟨731133160757810331762851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487422107171873554508567 731133160757810331762851)
                ·
                  refine ⟨1096699741136715497644277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731133160757810331762851 1096699741136715497644277)
                  ·
                    refine ⟨102815600731567077904151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1096699741136715497644277 102815600731567077904151)
                    ·
                      rfl

theorem cell22_300349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_300349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300349 prefixEnd_300349 := by exact prefixLift 300349
  have htrace : WordTrace (prefixWord ++ tailWord_300349) baseStart_300349 baseEnd_300349 := by
    simpa [prefixWord, tailWord_300349, baseEnd_300349] using wordTrace_append hprefix tailTrace_300349
  have hstable : (prefixWord ++ tailWord_300349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300349).length < 2 ^ (prefixWord ++ tailWord_300349).sum := by decide
  have hdescent : baseEnd_300349 < baseStart_300349 := by decide
  rcases family_descends (prefixWord ++ tailWord_300349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300373 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 7]
def baseStart_300373 : Nat := 118140960795 + 300373 * 2 ^ 59
def prefixEnd_300373 : Nat := 4983230072969 + 3 ^ 40 * 300373 * 2
def baseEnd_300373 : Nat := 34274605474013005101359

theorem tailTrace_300373 : CollatzResearch.WordTrace tailWord_300373 prefixEnd_300373 34274605474013005101359 := by
  unfold tailWord_300373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955503340807395469337773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7303668893871596979558515 10955503340807395469337773)
  ·
    refine ⟨4108313752802773301001665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10955503340807395469337773 4108313752802773301001665)
    ·
      refine ⟨3081235314602079975751249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4108313752802773301001665 3081235314602079975751249)
      ·
        refine ⟨2310926485951559981813437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3081235314602079975751249 2310926485951559981813437)
        ·
          refine ⟨866597432231834993180039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2310926485951559981813437 866597432231834993180039)
          ·
            refine ⟨1299896148347752489770059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866597432231834993180039 1299896148347752489770059)
            ·
              refine ⟨1949844222521628734655089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299896148347752489770059 1949844222521628734655089)
              ·
                refine ⟨1462383166891221550991317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1949844222521628734655089 1462383166891221550991317)
                ·
                  refine ⟨34274605474013005101359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1462383166891221550991317 34274605474013005101359)
                  ·
                    rfl

theorem cell22_300373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_300373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300373 prefixEnd_300373 := by exact prefixLift 300373
  have htrace : WordTrace (prefixWord ++ tailWord_300373) baseStart_300373 baseEnd_300373 := by
    simpa [prefixWord, tailWord_300373, baseEnd_300373] using wordTrace_append hprefix tailTrace_300373
  have hstable : (prefixWord ++ tailWord_300373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300373).length < 2 ^ (prefixWord ++ tailWord_300373).sum := by decide
  have hdescent : baseEnd_300373 < baseStart_300373 := by decide
  rcases family_descends (prefixWord ++ tailWord_300373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300377 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_300377 : Nat := 118140960795 + 300377 * 2 ^ 59
def prefixEnd_300377 : Nat := 4983230072969 + 3 ^ 40 * 300377 * 2
def baseEnd_300377 : Nat := 102825185703784338204065

theorem tailTrace_300377 : CollatzResearch.WordTrace tailWord_300377 prefixEnd_300377 102825185703784338204065 := by
  unfold tailWord_300377
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955649232792904152483385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7303766155195269434988923 10955649232792904152483385)
  ·
    refine ⟨8216736924594678114362539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10955649232792904152483385 8216736924594678114362539)
    ·
      refine ⟨12325105386892017171543809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216736924594678114362539 12325105386892017171543809)
      ·
        refine ⟨9243829040169012878657857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12325105386892017171543809 9243829040169012878657857)
        ·
          refine ⟨6932871780126759658993393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9243829040169012878657857 6932871780126759658993393)
          ·
            refine ⟨5199653835095069744245045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6932871780126759658993393 5199653835095069744245045)
            ·
              refine ⟨487467547040162788522973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5199653835095069744245045 487467547040162788522973)
              ·
                refine ⟨182800330140061045696115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487467547040162788522973 182800330140061045696115)
                ·
                  refine ⟨274200495210091568544173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182800330140061045696115 274200495210091568544173)
                  ·
                    refine ⟨102825185703784338204065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274200495210091568544173 102825185703784338204065)
                    ·
                      rfl

theorem cell22_300377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_300377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300377 prefixEnd_300377 := by exact prefixLift 300377
  have htrace : WordTrace (prefixWord ++ tailWord_300377) baseStart_300377 baseEnd_300377 := by
    simpa [prefixWord, tailWord_300377, baseEnd_300377] using wordTrace_append hprefix tailTrace_300377
  have hstable : (prefixWord ++ tailWord_300377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300377).length < 2 ^ (prefixWord ++ tailWord_300377).sum := by decide
  have hdescent : baseEnd_300377 < baseStart_300377 := by decide
  rcases family_descends (prefixWord ++ tailWord_300377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300394 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_300394 : Nat := 118140960795 + 300394 * 2 ^ 59
def prefixEnd_300394 : Nat := 4983230072969 + 3 ^ 40 * 300394 * 2
def baseEnd_300394 : Nat := 102831005151201960529013

theorem tailTrace_300394 : CollatzResearch.WordTrace tailWord_300394 prefixEnd_300394 102831005151201960529013 := by
  unfold tailWord_300394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739067318432829013963059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7304179515820877370568157 2739067318432829013963059)
  ·
    refine ⟨4108600977649243520944589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739067318432829013963059 4108600977649243520944589)
    ·
      refine ⟨1540725366618466320354221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4108600977649243520944589 1540725366618466320354221)
      ·
        refine ⟨577772012481924870132833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1540725366618466320354221 577772012481924870132833)
        ·
          refine ⟨433329009361443652599625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577772012481924870132833 433329009361443652599625)
          ·
            refine ⟨324996757021082739449719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433329009361443652599625 324996757021082739449719)
            ·
              refine ⟨487495135531624109174579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324996757021082739449719 487495135531624109174579)
              ·
                refine ⟨731242703297436163761869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487495135531624109174579 731242703297436163761869)
                ·
                  refine ⟨274216013736538561410701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731242703297436163761869 274216013736538561410701)
                  ·
                    refine ⟨102831005151201960529013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274216013736538561410701 102831005151201960529013)
                    ·
                      rfl

theorem cell22_300394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_300394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300394 prefixEnd_300394 := by exact prefixLift 300394
  have htrace : WordTrace (prefixWord ++ tailWord_300394) baseStart_300394 baseEnd_300394 := by
    simpa [prefixWord, tailWord_300394, baseEnd_300394] using wordTrace_append hprefix tailTrace_300394
  have hstable : (prefixWord ++ tailWord_300394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300394).length < 2 ^ (prefixWord ++ tailWord_300394).sum := by decide
  have hdescent : baseEnd_300394 < baseStart_300394 := by decide
  rcases family_descends (prefixWord ++ tailWord_300394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300420 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_300420 : Nat := 118140960795 + 300420 * 2 ^ 59
def prefixEnd_300420 : Nat := 4983230072969 + 3 ^ 40 * 300420 * 2
def baseEnd_300420 : Nat := 102839905482546559378933

theorem tailTrace_300420 : CollatzResearch.WordTrace tailWord_300420 prefixEnd_300420 102839905482546559378933 := by
  unfold tailWord_300420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478608785818561248149357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7304811714424748330865809 5478608785818561248149357)
  ·
    refine ⟨2054478294681960468056009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5478608785818561248149357 2054478294681960468056009)
    ·
      refine ⟨1540858721011470351042007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2054478294681960468056009 1540858721011470351042007)
      ·
        refine ⟨2311288081517205526563011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540858721011470351042007 2311288081517205526563011)
        ·
          refine ⟨3466932122275808289844517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311288081517205526563011 3466932122275808289844517)
          ·
            refine ⟨650049772926714054345847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3466932122275808289844517 650049772926714054345847)
            ·
              refine ⟨975074659390071081518771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650049772926714054345847 975074659390071081518771)
              ·
                refine ⟨1462611989085106622278157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975074659390071081518771 1462611989085106622278157)
                ·
                  refine ⟨548479495906914983354309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1462611989085106622278157 548479495906914983354309)
                  ·
                    refine ⟨102839905482546559378933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548479495906914983354309 102839905482546559378933)
                    ·
                      rfl

theorem cell22_300420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_300420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300420 prefixEnd_300420 := by exact prefixLift 300420
  have htrace : WordTrace (prefixWord ++ tailWord_300420) baseStart_300420 baseEnd_300420 := by
    simpa [prefixWord, tailWord_300420, baseEnd_300420] using wordTrace_append hprefix tailTrace_300420
  have hstable : (prefixWord ++ tailWord_300420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300420).length < 2 ^ (prefixWord ++ tailWord_300420).sum := by decide
  have hdescent : baseEnd_300420 < baseStart_300420 := by decide
  rcases family_descends (prefixWord ++ tailWord_300420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300433 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_300433 : Nat := 118140960795 + 300433 * 2 ^ 59
def prefixEnd_300433 : Nat := 4983230072969 + 3 ^ 40 * 300433 * 2
def baseEnd_300433 : Nat := 102844355648218858803893

theorem tailTrace_300433 : CollatzResearch.WordTrace tailWord_300433 prefixEnd_300433 102844355648218858803893 := by
  unfold tailWord_300433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10957691720590025716521953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7305127813726683811014635 10957691720590025716521953)
  ·
    refine ⟨8218268790442519287391465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10957691720590025716521953 8218268790442519287391465)
    ·
      refine ⟨6163701592831889465543599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8218268790442519287391465 6163701592831889465543599)
      ·
        refine ⟨9245552389247834198315399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163701592831889465543599 9245552389247834198315399)
        ·
          refine ⟨13868328583871751297473099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245552389247834198315399 13868328583871751297473099)
          ·
            refine ⟨20802492875807626946209649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868328583871751297473099 20802492875807626946209649)
            ·
              refine ⟨15601869656855720209657237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20802492875807626946209649 15601869656855720209657237)
              ·
                refine ⟨731337640165111884827683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15601869656855720209657237 731337640165111884827683)
                ·
                  refine ⟨1097006460247667827241525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731337640165111884827683 1097006460247667827241525)
                  ·
                    refine ⟨102844355648218858803893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1097006460247667827241525 102844355648218858803893)
                    ·
                      rfl

theorem cell22_300433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_300433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300433 prefixEnd_300433 := by exact prefixLift 300433
  have htrace : WordTrace (prefixWord ++ tailWord_300433) baseStart_300433 baseEnd_300433 := by
    simpa [prefixWord, tailWord_300433, baseEnd_300433] using wordTrace_append hprefix tailTrace_300433
  have hstable : (prefixWord ++ tailWord_300433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300433).length < 2 ^ (prefixWord ++ tailWord_300433).sum := by decide
  have hdescent : baseEnd_300433 < baseStart_300433 := by decide
  rcases family_descends (prefixWord ++ tailWord_300433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_300523 : Nat := 118140960795 + 300523 * 2 ^ 59
def prefixEnd_300523 : Nat := 4983230072969 + 3 ^ 40 * 300523 * 2
def baseEnd_300523 : Nat := 102875164487488624053617

theorem tailTrace_300523 : CollatzResearch.WordTrace tailWord_300523 prefixEnd_300523 102875164487488624053617 := by
  unfold tailWord_300523
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960974290263971087298223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7307316193509314058198815 10960974290263971087298223)
  ·
    refine ⟨16441461435395956630947335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10960974290263971087298223 16441461435395956630947335)
    ·
      refine ⟨24662192153093934946421003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16441461435395956630947335 24662192153093934946421003)
      ·
        refine ⟨36993288229640902419631505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24662192153093934946421003 36993288229640902419631505)
        ·
          refine ⟨27744966172230676814723629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36993288229640902419631505 27744966172230676814723629)
          ·
            refine ⟨10404362314586503805521361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27744966172230676814723629 10404362314586503805521361)
            ·
              refine ⟨7803271735939877854141021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10404362314586503805521361 7803271735939877854141021)
              ·
                refine ⟨2926226900977454195302883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7803271735939877854141021 2926226900977454195302883)
                ·
                  refine ⟨4389340351466181292954325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926226900977454195302883 4389340351466181292954325)
                  ·
                    refine ⟨102875164487488624053617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4389340351466181292954325 102875164487488624053617)
                    ·
                      rfl

theorem cell22_300523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_300523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300523 prefixEnd_300523 := by exact prefixLift 300523
  have htrace : WordTrace (prefixWord ++ tailWord_300523) baseStart_300523 baseEnd_300523 := by
    simpa [prefixWord, tailWord_300523, baseEnd_300523] using wordTrace_append hprefix tailTrace_300523
  have hstable : (prefixWord ++ tailWord_300523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300523).length < 2 ^ (prefixWord ++ tailWord_300523).sum := by decide
  have hdescent : baseEnd_300523 < baseStart_300523 := by decide
  rcases family_descends (prefixWord ++ tailWord_300523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300615 : List Nat := [1, 1, 4, 1, 5, 10]
def baseStart_300615 : Nat := 118140960795 + 300615 * 2 ^ 59
def prefixEnd_300615 : Nat := 4983230072969 + 3 ^ 40 * 300615 * 2
def baseEnd_300615 : Nat := 1270452567501617910535

theorem tailTrace_300615 : CollatzResearch.WordTrace tailWord_300615 prefixEnd_300615 1270452567501617910535 := by
  unfold tailWord_300615
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964329805930670799647299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7309553203953780533098199 10964329805930670799647299)
  ·
    refine ⟨16446494708896006199470949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10964329805930670799647299 16446494708896006199470949)
    ·
      refine ⟨3083717757918001162400803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16446494708896006199470949 3083717757918001162400803)
      ·
        refine ⟨4625576636877001743601205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083717757918001162400803 4625576636877001743601205)
        ·
          refine ⟨433647809707218913462613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4625576636877001743601205 433647809707218913462613)
          ·
            refine ⟨1270452567501617910535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 433647809707218913462613 1270452567501617910535)
            ·
              rfl

theorem cell22_300615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 10].length) (baseStart_300615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300615 prefixEnd_300615 := by exact prefixLift 300615
  have htrace : WordTrace (prefixWord ++ tailWord_300615) baseStart_300615 baseEnd_300615 := by
    simpa [prefixWord, tailWord_300615, baseEnd_300615] using wordTrace_append hprefix tailTrace_300615
  have hstable : (prefixWord ++ tailWord_300615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300615).length < 2 ^ (prefixWord ++ tailWord_300615).sum := by decide
  have hdescent : baseEnd_300615 < baseStart_300615 := by decide
  rcases family_descends (prefixWord ++ tailWord_300615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300621 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 4]
def baseStart_300621 : Nat := 118140960795 + 300621 * 2 ^ 59
def prefixEnd_300621 : Nat := 4983230072969 + 3 ^ 40 * 300621 * 2
def baseEnd_300621 : Nat := 34302903963416345034439

theorem tailTrace_300621 : CollatzResearch.WordTrace tailWord_300621 prefixEnd_300621 34302903963416345034439 := by
  unfold tailWord_300621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964548643908933824365717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7309699095939289216243811 10964548643908933824365717)
  ·
    refine ⟨513963217683231273017143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10964548643908933824365717 513963217683231273017143)
    ·
      refine ⟨770944826524846909525715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513963217683231273017143 770944826524846909525715)
      ·
        refine ⟨1156417239787270364288573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770944826524846909525715 1156417239787270364288573)
        ·
          refine ⟨433656464920226386608215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1156417239787270364288573 433656464920226386608215)
          ·
            refine ⟨650484697380339579912323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433656464920226386608215 650484697380339579912323)
            ·
              refine ⟨975727046070509369868485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650484697380339579912323 975727046070509369868485)
              ·
                refine ⟨182948821138220506850341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 975727046070509369868485 182948821138220506850341)
                ·
                  refine ⟨34302903963416345034439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182948821138220506850341 34302903963416345034439)
                  ·
                    rfl

theorem cell22_300621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_300621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300621 prefixEnd_300621 := by exact prefixLift 300621
  have htrace : WordTrace (prefixWord ++ tailWord_300621) baseStart_300621 baseEnd_300621 := by
    simpa [prefixWord, tailWord_300621, baseEnd_300621] using wordTrace_append hprefix tailTrace_300621
  have hstable : (prefixWord ++ tailWord_300621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300621).length < 2 ^ (prefixWord ++ tailWord_300621).sum := by decide
  have hdescent : baseEnd_300621 < baseStart_300621 := by decide
  rcases family_descends (prefixWord ++ tailWord_300621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300647 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 5, 3]
def baseStart_300647 : Nat := 118140960795 + 300647 * 2 ^ 59
def prefixEnd_300647 : Nat := 4983230072969 + 3 ^ 40 * 300647 * 2
def baseEnd_300647 : Nat := 102917612221593633953237

theorem tailTrace_300647 : CollatzResearch.WordTrace tailWord_300647 prefixEnd_300647 102917612221593633953237 := by
  unfold tailWord_300647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965496941814740264812195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7310331294543160176541463 10965496941814740264812195)
  ·
    refine ⟨16448245412722110397218293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10965496941814740264812195 16448245412722110397218293)
    ·
      refine ⟨1542023007442697849739215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16448245412722110397218293 1542023007442697849739215)
      ·
        refine ⟨2313034511164046774608823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542023007442697849739215 2313034511164046774608823)
        ·
          refine ⟨3469551766746070161913235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313034511164046774608823 3469551766746070161913235)
          ·
            refine ⟨5204327650119105242869853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469551766746070161913235 5204327650119105242869853)
            ·
              refine ⟨1951622868794664466076195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5204327650119105242869853 1951622868794664466076195)
              ·
                refine ⟨2927434303191996699114293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951622868794664466076195 2927434303191996699114293)
                ·
                  refine ⟨274446965924249690541965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927434303191996699114293 274446965924249690541965)
                  ·
                    refine ⟨102917612221593633953237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274446965924249690541965 102917612221593633953237)
                    ·
                      rfl

theorem cell22_300647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_300647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300647 prefixEnd_300647 := by exact prefixLift 300647
  have htrace : WordTrace (prefixWord ++ tailWord_300647) baseStart_300647 baseEnd_300647 := by
    simpa [prefixWord, tailWord_300647, baseEnd_300647] using wordTrace_append hprefix tailTrace_300647
  have hstable : (prefixWord ++ tailWord_300647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300647).length < 2 ^ (prefixWord ++ tailWord_300647).sum := by decide
  have hdescent : baseEnd_300647 < baseStart_300647 := by decide
  rcases family_descends (prefixWord ++ tailWord_300647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300758 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_300758 : Nat := 118140960795 + 300758 * 2 ^ 59
def prefixEnd_300758 : Nat := 4983230072969 + 3 ^ 40 * 300758 * 2
def baseEnd_300758 : Nat := 102955609790026344427897

theorem tailTrace_300758 : CollatzResearch.WordTrace tailWord_300758 prefixEnd_300758 102955609790026344427897 := by
  unfold tailWord_300758
  simp only [CollatzResearch.WordTrace]
  refine ⟨685596590275787888881433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7313030296275070814735285 685596590275787888881433)
  ·
    refine ⟨514197442706840916661075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685596590275787888881433 514197442706840916661075)
    ·
      refine ⟨771296164060261374991613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514197442706840916661075 771296164060261374991613)
      ·
        refine ⟨289236061522598015621855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 771296164060261374991613 289236061522598015621855)
        ·
          refine ⟨433854092283897023432783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289236061522598015621855 433854092283897023432783)
          ·
            refine ⟨650781138425845535149175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433854092283897023432783 650781138425845535149175)
            ·
              refine ⟨976171707638768302723763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650781138425845535149175 976171707638768302723763)
              ·
                refine ⟨1464257561458152454085645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976171707638768302723763 1464257561458152454085645)
                ·
                  refine ⟨549096585546807170282117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1464257561458152454085645 549096585546807170282117)
                  ·
                    refine ⟨102955609790026344427897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 549096585546807170282117 102955609790026344427897)
                    ·
                      rfl

theorem cell22_300758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_300758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300758 prefixEnd_300758 := by exact prefixLift 300758
  have htrace : WordTrace (prefixWord ++ tailWord_300758) baseStart_300758 baseEnd_300758 := by
    simpa [prefixWord, tailWord_300758, baseEnd_300758] using wordTrace_append hprefix tailTrace_300758
  have hstable : (prefixWord ++ tailWord_300758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300758).length < 2 ^ (prefixWord ++ tailWord_300758).sum := by decide
  have hdescent : baseEnd_300758 < baseStart_300758 := by decide
  rcases family_descends (prefixWord ++ tailWord_300758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300833 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_300833 : Nat := 118140960795 + 300833 * 2 ^ 59
def prefixEnd_300833 : Nat := 4983230072969 + 3 ^ 40 * 300833 * 2
def baseEnd_300833 : Nat := 102981283822751148802667

theorem tailTrace_300833 : CollatzResearch.WordTrace tailWord_300833 prefixEnd_300833 102981283822751148802667 := by
  unfold tailWord_300833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10972280919140894031083153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7314853946093929354055435 10972280919140894031083153)
  ·
    refine ⟨8229210689355670523312365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10972280919140894031083153 8229210689355670523312365)
    ·
      refine ⟨3085954008508376446242137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8229210689355670523312365 3085954008508376446242137)
      ·
        refine ⟨2314465506381282334681603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085954008508376446242137 2314465506381282334681603)
        ·
          refine ⟨3471698259571923502022405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314465506381282334681603 3471698259571923502022405)
          ·
            refine ⟨650943423669735656629201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3471698259571923502022405 650943423669735656629201)
            ·
              refine ⟨488207567752301742471901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650943423669735656629201 488207567752301742471901)
              ·
                refine ⟨183077837907113153426963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488207567752301742471901 183077837907113153426963)
                ·
                  refine ⟨274616756860669730140445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183077837907113153426963 274616756860669730140445)
                  ·
                    refine ⟨102981283822751148802667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274616756860669730140445 102981283822751148802667)
                    ·
                      rfl

theorem cell22_300833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_300833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300833 prefixEnd_300833 := by exact prefixLift 300833
  have htrace : WordTrace (prefixWord ++ tailWord_300833) baseStart_300833 baseEnd_300833 := by
    simpa [prefixWord, tailWord_300833, baseEnd_300833] using wordTrace_append hprefix tailTrace_300833
  have hstable : (prefixWord ++ tailWord_300833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300833).length < 2 ^ (prefixWord ++ tailWord_300833).sum := by decide
  have hdescent : baseEnd_300833 < baseStart_300833 := by decide
  rcases family_descends (prefixWord ++ tailWord_300833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300846 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_300846 : Nat := 118140960795 + 300846 * 2 ^ 59
def prefixEnd_300846 : Nat := 4983230072969 + 3 ^ 40 * 300846 * 2
def baseEnd_300846 : Nat := 34328577996141149409209

theorem tailTrace_300846 : CollatzResearch.WordTrace tailWord_300846 prefixEnd_300846 34328577996141149409209 := by
  unfold tailWord_300846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371594383511724656413299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7315170045395864834204261 1371594383511724656413299)
  ·
    refine ⟨2057391575267586984619949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371594383511724656413299 2057391575267586984619949)
    ·
      refine ⟨771521840725345119232481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2057391575267586984619949 771521840725345119232481)
      ·
        refine ⟨578641380544008839424361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771521840725345119232481 578641380544008839424361)
        ·
          refine ⟨433981035408006629568271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578641380544008839424361 433981035408006629568271)
          ·
            refine ⟨650971553112009944352407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433981035408006629568271 650971553112009944352407)
            ·
              refine ⟨976457329668014916528611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650971553112009944352407 976457329668014916528611)
              ·
                refine ⟨1464685994502022374792917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976457329668014916528611 1464685994502022374792917)
                ·
                  refine ⟨34328577996141149409209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1464685994502022374792917 34328577996141149409209)
                  ·
                    rfl

theorem cell22_300846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_300846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300846 prefixEnd_300846 := by exact prefixLift 300846
  have htrace : WordTrace (prefixWord ++ tailWord_300846) baseStart_300846 baseEnd_300846 := by
    simpa [prefixWord, tailWord_300846, baseEnd_300846] using wordTrace_append hprefix tailTrace_300846
  have hstable : (prefixWord ++ tailWord_300846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300846).length < 2 ^ (prefixWord ++ tailWord_300846).sum := by decide
  have hdescent : baseEnd_300846 < baseStart_300846 := by decide
  rcases family_descends (prefixWord ++ tailWord_300846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300889 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_300889 : Nat := 118140960795 + 300889 * 2 ^ 59
def prefixEnd_300889 : Nat := 4983230072969 + 3 ^ 40 * 300889 * 2
def baseEnd_300889 : Nat := 103000453767185669402495

theorem tailTrace_300889 : CollatzResearch.WordTrace tailWord_300889 prefixEnd_300889 103000453767185669402495 := by
  unfold tailWord_300889
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974323406938015595121721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316215604625343730081147 10974323406938015595121721)
  ·
    refine ⟨8230742555203511696341291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10974323406938015595121721 8230742555203511696341291)
    ·
      refine ⟨12346113832805267544511937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8230742555203511696341291 12346113832805267544511937)
      ·
        refine ⟨9259585374603950658383953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12346113832805267544511937 9259585374603950658383953)
        ·
          refine ⟨6944689030952962993787965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9259585374603950658383953 6944689030952962993787965)
          ·
            refine ⟨2604258386607361122670487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6944689030952962993787965 2604258386607361122670487)
            ·
              refine ⟨3906387579911041684005731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604258386607361122670487 3906387579911041684005731)
              ·
                refine ⟨5859581369866562526008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906387579911041684005731 5859581369866562526008597)
                ·
                  refine ⟨274667876712495118406653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5859581369866562526008597 274667876712495118406653)
                  ·
                    refine ⟨103000453767185669402495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274667876712495118406653 103000453767185669402495)
                    ·
                      rfl

theorem cell22_300889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_300889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300889 prefixEnd_300889 := by exact prefixLift 300889
  have htrace : WordTrace (prefixWord ++ tailWord_300889) baseStart_300889 baseEnd_300889 := by
    simpa [prefixWord, tailWord_300889, baseEnd_300889] using wordTrace_append hprefix tailTrace_300889
  have hstable : (prefixWord ++ tailWord_300889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300889).length < 2 ^ (prefixWord ++ tailWord_300889).sum := by decide
  have hdescent : baseEnd_300889 < baseStart_300889 := by decide
  rcases family_descends (prefixWord ++ tailWord_300889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300908 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_300908 : Nat := 118140960795 + 300908 * 2 ^ 59
def prefixEnd_300908 : Nat := 4983230072969 + 3 ^ 40 * 300908 * 2
def baseEnd_300908 : Nat := 34335652618491984392479

theorem tailTrace_300908 : CollatzResearch.WordTrace tailWord_300908 prefixEnd_300908 34335652618491984392479 := by
  unfold tailWord_300908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487508196934590920031689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7316677595912787893375585 5487508196934590920031689)
  ·
    refine ⟨4115631147700943190023767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5487508196934590920031689 4115631147700943190023767)
    ·
      refine ⟨6173446721551414785035651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115631147700943190023767 6173446721551414785035651)
      ·
        refine ⟨9260170082327122177553477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173446721551414785035651 9260170082327122177553477)
        ·
          refine ⟨1736281890436335408291277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9260170082327122177553477 1736281890436335408291277)
          ·
            refine ⟨651105708913625778109229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1736281890436335408291277 651105708913625778109229)
            ·
              refine ⟨244164640842609666790961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 651105708913625778109229 244164640842609666790961)
              ·
                refine ⟨183123480631957250093221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244164640842609666790961 183123480631957250093221)
                ·
                  refine ⟨34335652618491984392479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183123480631957250093221 34335652618491984392479)
                  ·
                    rfl

theorem cell22_300908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_300908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300908 prefixEnd_300908 := by exact prefixLift 300908
  have htrace : WordTrace (prefixWord ++ tailWord_300908) baseStart_300908 baseEnd_300908 := by
    simpa [prefixWord, tailWord_300908, baseEnd_300908] using wordTrace_append hprefix tailTrace_300908
  have hstable : (prefixWord ++ tailWord_300908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300908).length < 2 ^ (prefixWord ++ tailWord_300908).sum := by decide
  have hdescent : baseEnd_300908 < baseStart_300908 := by decide
  rcases family_descends (prefixWord ++ tailWord_300908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300938 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_300938 : Nat := 118140960795 + 300938 * 2 ^ 59
def prefixEnd_300938 : Nat := 4983230072969 + 3 ^ 40 * 300938 * 2
def baseEnd_300938 : Nat := 103017227468565874927345

theorem tailTrace_300938 : CollatzResearch.WordTrace tailWord_300938 prefixEnd_300938 103017227468565874927345 := by
  unfold tailWord_300938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744027645940124240913867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7317407055840331309103645 2744027645940124240913867)
  ·
    refine ⟨4116041468910186361370801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744027645940124240913867 4116041468910186361370801)
    ·
      refine ⟨3087031101682639771028101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4116041468910186361370801 3087031101682639771028101)
      ·
        refine ⟨578818331565494957067769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3087031101682639771028101 578818331565494957067769)
        ·
          refine ⟨434113748674121217800827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578818331565494957067769 434113748674121217800827)
          ·
            refine ⟨651170623011181826701241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434113748674121217800827 651170623011181826701241)
            ·
              refine ⟨488377967258386370025931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651170623011181826701241 488377967258386370025931)
              ·
                refine ⟨732566950887579555038897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488377967258386370025931 732566950887579555038897)
                ·
                  refine ⟨549425213165684666279173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732566950887579555038897 549425213165684666279173)
                  ·
                    refine ⟨103017227468565874927345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 549425213165684666279173 103017227468565874927345)
                    ·
                      rfl

theorem cell22_300938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_300938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300938 prefixEnd_300938 := by exact prefixLift 300938
  have htrace : WordTrace (prefixWord ++ tailWord_300938) baseStart_300938 baseEnd_300938 := by
    simpa [prefixWord, tailWord_300938, baseEnd_300938] using wordTrace_append hprefix tailTrace_300938
  have hstable : (prefixWord ++ tailWord_300938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300938).length < 2 ^ (prefixWord ++ tailWord_300938).sum := by decide
  have hdescent : baseEnd_300938 < baseStart_300938 := by decide
  rcases family_descends (prefixWord ++ tailWord_300938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300979 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_300979 : Nat := 118140960795 + 300979 * 2 ^ 59
def prefixEnd_300979 : Nat := 4983230072969 + 3 ^ 40 * 300979 * 2
def baseEnd_300979 : Nat := 103031262606455434652219

theorem tailTrace_300979 : CollatzResearch.WordTrace tailWord_300979 prefixEnd_300979 103031262606455434652219 := by
  unfold tailWord_300979
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977605976611960965897991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7318403984407973977265327 10977605976611960965897991)
  ·
    refine ⟨16466408964917941448846987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977605976611960965897991 16466408964917941448846987)
    ·
      refine ⟨24699613447376912173270481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466408964917941448846987 24699613447376912173270481)
      ·
        refine ⟨18524710085532684129952861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24699613447376912173270481 18524710085532684129952861)
        ·
          refine ⟨6946766282074756548732323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18524710085532684129952861 6946766282074756548732323)
          ·
            refine ⟨10420149423112134823098485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946766282074756548732323 10420149423112134823098485)
            ·
              refine ⟨976889008416762639665483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10420149423112134823098485 976889008416762639665483)
              ·
                refine ⟨1465333512625143959498225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976889008416762639665483 1465333512625143959498225)
                ·
                  refine ⟨1099000134468857969623669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465333512625143959498225 1099000134468857969623669)
                  ·
                    refine ⟨103031262606455434652219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1099000134468857969623669 103031262606455434652219)
                    ·
                      rfl

theorem cell22_300979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_300979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300979 prefixEnd_300979 := by exact prefixLift 300979
  have htrace : WordTrace (prefixWord ++ tailWord_300979) baseStart_300979 baseEnd_300979 := by
    simpa [prefixWord, tailWord_300979, baseEnd_300979] using wordTrace_append hprefix tailTrace_300979
  have hstable : (prefixWord ++ tailWord_300979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300979).length < 2 ^ (prefixWord ++ tailWord_300979).sum := by decide
  have hdescent : baseEnd_300979 < baseStart_300979 := by decide
  rcases family_descends (prefixWord ++ tailWord_300979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300981 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 5]
def baseStart_300981 : Nat := 118140960795 + 300981 * 2 ^ 59
def prefixEnd_300981 : Nat := 4983230072969 + 3 ^ 40 * 300981 * 2
def baseEnd_300981 : Nat := 34343982415776032034071

theorem tailTrace_300981 : CollatzResearch.WordTrace tailWord_300981 prefixEnd_300981 34343982415776032034071 := by
  unfold tailWord_300981
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977678922604715307470797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7318452615069810204980531 10977678922604715307470797)
  ·
    refine ⟨4116629595976768240301549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10977678922604715307470797 4116629595976768240301549)
    ·
      refine ⟨1543736098491288090113081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4116629595976768240301549 1543736098491288090113081)
      ·
        refine ⟨1157802073868466067584811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1543736098491288090113081 1157802073868466067584811)
        ·
          refine ⟨1736703110802699101377217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157802073868466067584811 1736703110802699101377217)
          ·
            refine ⟨1302527333102024326032913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736703110802699101377217 1302527333102024326032913)
            ·
              refine ⟨976895499826518244524685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302527333102024326032913 976895499826518244524685)
              ·
                refine ⟨366335812434944341696757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976895499826518244524685 366335812434944341696757)
                ·
                  refine ⟨34343982415776032034071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 366335812434944341696757 34343982415776032034071)
                  ·
                    rfl

theorem cell22_300981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_300981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_300981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_300981 prefixEnd_300981 := by exact prefixLift 300981
  have htrace : WordTrace (prefixWord ++ tailWord_300981) baseStart_300981 baseEnd_300981 := by
    simpa [prefixWord, tailWord_300981, baseEnd_300981] using wordTrace_append hprefix tailTrace_300981
  have hstable : (prefixWord ++ tailWord_300981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300981).length < 2 ^ (prefixWord ++ tailWord_300981).sum := by decide
  have hdescent : baseEnd_300981 < baseStart_300981 := by decide
  rcases family_descends (prefixWord ++ tailWord_300981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301024 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_301024 : Nat := 118140960795 + 301024 * 2 ^ 59
def prefixEnd_301024 : Nat := 4983230072969 + 3 ^ 40 * 301024 * 2
def baseEnd_301024 : Nat := 103046667026090317277081

theorem tailTrace_301024 : CollatzResearch.WordTrace tailWord_301024 prefixEnd_301024 103046667026090317277081 := by
  unfold tailWord_301024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489623630724466825643063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7319498174299289100857417 5489623630724466825643063)
  ·
    refine ⟨8234435446086700238464595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5489623630724466825643063 8234435446086700238464595)
    ·
      refine ⟨12351653169130050357696893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8234435446086700238464595 12351653169130050357696893)
      ·
        refine ⟨4631869938423768884136335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12351653169130050357696893 4631869938423768884136335)
        ·
          refine ⟨6947804907635653326204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4631869938423768884136335 6947804907635653326204503)
          ·
            refine ⟨10421707361453479989306755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947804907635653326204503 10421707361453479989306755)
            ·
              refine ⟨15632561042180219983960133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10421707361453479989306755 15632561042180219983960133)
              ·
                refine ⟨2931105195408791246992525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15632561042180219983960133 2931105195408791246992525)
                ·
                  refine ⟨1099164448278296717622197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2931105195408791246992525 1099164448278296717622197)
                  ·
                    refine ⟨103046667026090317277081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1099164448278296717622197 103046667026090317277081)
                    ·
                      rfl

theorem cell22_301024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_301024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301024 prefixEnd_301024 := by exact prefixLift 301024
  have htrace : WordTrace (prefixWord ++ tailWord_301024) baseStart_301024 baseEnd_301024 := by
    simpa [prefixWord, tailWord_301024, baseEnd_301024] using wordTrace_append hprefix tailTrace_301024
  have hstable : (prefixWord ++ tailWord_301024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301024).length < 2 ^ (prefixWord ++ tailWord_301024).sum := by decide
  have hdescent : baseEnd_301024 < baseStart_301024 := by decide
  rcases family_descends (prefixWord ++ tailWord_301024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301039 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_301039 : Nat := 118140960795 + 301039 * 2 ^ 59
def prefixEnd_301039 : Nat := 4983230072969 + 3 ^ 40 * 301039 * 2
def baseEnd_301039 : Nat := 103051801832635278152035

theorem tailTrace_301039 : CollatzResearch.WordTrace tailWord_301039 prefixEnd_301039 103051801832635278152035 := by
  unfold tailWord_301039
  simp only [CollatzResearch.WordTrace]
  refine ⟨10979794356394591213082171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7319862904263060808721447 10979794356394591213082171)
  ·
    refine ⟨16469691534591886819623257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10979794356394591213082171 16469691534591886819623257)
    ·
      refine ⟨12352268650943915114717443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16469691534591886819623257 12352268650943915114717443)
      ·
        refine ⟨18528402976415872672076165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12352268650943915114717443 18528402976415872672076165)
        ·
          refine ⟨3474075558077976126014281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18528402976415872672076165 3474075558077976126014281)
          ·
            refine ⟨2605556668558482094510711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3474075558077976126014281 2605556668558482094510711)
            ·
              refine ⟨3908335002837723141766067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605556668558482094510711 3908335002837723141766067)
              ·
                refine ⟨5862502504256584712649101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908335002837723141766067 5862502504256584712649101)
                ·
                  refine ⟨2198438439096219267243413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5862502504256584712649101 2198438439096219267243413)
                  ·
                    refine ⟨103051801832635278152035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2198438439096219267243413 103051801832635278152035)
                    ·
                      rfl

theorem cell22_301039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_301039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301039 prefixEnd_301039 := by exact prefixLift 301039
  have htrace : WordTrace (prefixWord ++ tailWord_301039) baseStart_301039 baseEnd_301039 := by
    simpa [prefixWord, tailWord_301039, baseEnd_301039] using wordTrace_append hprefix tailTrace_301039
  have hstable : (prefixWord ++ tailWord_301039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301039).length < 2 ^ (prefixWord ++ tailWord_301039).sum := by decide
  have hdescent : baseEnd_301039 < baseStart_301039 := by decide
  rcases family_descends (prefixWord ++ tailWord_301039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301099 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 9]
def baseStart_301099 : Nat := 118140960795 + 301099 * 2 ^ 59
def prefixEnd_301099 : Nat := 4983230072969 + 3 ^ 40 * 301099 * 2
def baseEnd_301099 : Nat := 34357447019605040550617

theorem tailTrace_301099 : CollatzResearch.WordTrace tailWord_301099 prefixEnd_301099 34357447019605040550617 := by
  unfold tailWord_301099
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981982736177221460266351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321321824118147640177567 10981982736177221460266351)
  ·
    refine ⟨16472974104265832190399527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10981982736177221460266351 16472974104265832190399527)
    ·
      refine ⟨24709461156398748285599291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16472974104265832190399527 24709461156398748285599291)
      ·
        refine ⟨37064191734598122428398937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24709461156398748285599291 37064191734598122428398937)
        ·
          refine ⟨27798143800948591821299203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37064191734598122428398937 27798143800948591821299203)
          ·
            refine ⟨41697215701422887731948805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27798143800948591821299203 41697215701422887731948805)
            ·
              refine ⟨7818227944016791449740401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41697215701422887731948805 7818227944016791449740401)
              ·
                refine ⟨5863670958012593587305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7818227944016791449740401 5863670958012593587305301)
                ·
                  refine ⟨34357447019605040550617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5863670958012593587305301 34357447019605040550617)
                  ·
                    rfl

theorem cell22_301099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_301099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301099 prefixEnd_301099 := by exact prefixLift 301099
  have htrace : WordTrace (prefixWord ++ tailWord_301099) baseStart_301099 baseEnd_301099 := by
    simpa [prefixWord, tailWord_301099, baseEnd_301099] using wordTrace_append hprefix tailTrace_301099
  have hstable : (prefixWord ++ tailWord_301099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301099).length < 2 ^ (prefixWord ++ tailWord_301099).sum := by decide
  have hdescent : baseEnd_301099 < baseStart_301099 := by decide
  rcases family_descends (prefixWord ++ tailWord_301099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301146 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_301146 : Nat := 118140960795 + 301146 * 2 ^ 59
def prefixEnd_301146 : Nat := 4983230072969 + 3 ^ 40 * 301146 * 2
def baseEnd_301146 : Nat := 103088430119322665726707

theorem tailTrace_301146 : CollatzResearch.WordTrace tailWord_301146 prefixEnd_301146 103088430119322665726707 := by
  unfold tailWord_301146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745924241751737121806823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7322464644671298991484861 2745924241751737121806823)
  ·
    refine ⟨4118886362627605682710235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2745924241751737121806823 4118886362627605682710235)
    ·
      refine ⟨6178329543941408524065353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118886362627605682710235 6178329543941408524065353)
      ·
        refine ⟨4633747157956056393049015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6178329543941408524065353 4633747157956056393049015)
        ·
          refine ⟨6950620736934084589573523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633747157956056393049015 6950620736934084589573523)
          ·
            refine ⟨10425931105401126884360285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950620736934084589573523 10425931105401126884360285)
            ·
              refine ⟨3909724164525422581635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10425931105401126884360285 3909724164525422581635107)
              ·
                refine ⟨5864586246788133872452661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909724164525422581635107 5864586246788133872452661)
                ·
                  refine ⟨549804960636387550542437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5864586246788133872452661 549804960636387550542437)
                  ·
                    refine ⟨103088430119322665726707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 549804960636387550542437 103088430119322665726707)
                    ·
                      rfl

theorem cell22_301146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_301146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301146 prefixEnd_301146 := by exact prefixLift 301146
  have htrace : WordTrace (prefixWord ++ tailWord_301146) baseStart_301146 baseEnd_301146 := by
    simpa [prefixWord, tailWord_301146, baseEnd_301146] using wordTrace_append hprefix tailTrace_301146
  have hstable : (prefixWord ++ tailWord_301146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301146).length < 2 ^ (prefixWord ++ tailWord_301146).sum := by decide
  have hdescent : baseEnd_301146 < baseStart_301146 := by decide
  rcases family_descends (prefixWord ++ tailWord_301146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301148 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_301148 : Nat := 118140960795 + 301148 * 2 ^ 59
def prefixEnd_301148 : Nat := 4983230072969 + 3 ^ 40 * 301148 * 2
def baseEnd_301148 : Nat := 103089114760195327176701

theorem tailTrace_301148 : CollatzResearch.WordTrace tailWord_301148 prefixEnd_301148 103089114760195327176701 := by
  unfold tailWord_301148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491884956499851414400049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7322513275333135219200065 5491884956499851414400049)
  ·
    refine ⟨4118913717374888560800037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5491884956499851414400049 4118913717374888560800037)
    ·
      refine ⟨772296322007791605150007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4118913717374888560800037 772296322007791605150007)
      ·
        refine ⟨1158444483011687407725011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772296322007791605150007 1158444483011687407725011)
        ·
          refine ⟨1737666724517531111587517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158444483011687407725011 1737666724517531111587517)
          ·
            refine ⟨651625021694074166845319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1737666724517531111587517 651625021694074166845319)
            ·
              refine ⟨977437532541111250267979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651625021694074166845319 977437532541111250267979)
              ·
                refine ⟨1466156298811666875401969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977437532541111250267979 1466156298811666875401969)
                ·
                  refine ⟨1099617224108750156551477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466156298811666875401969 1099617224108750156551477)
                  ·
                    refine ⟨103089114760195327176701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1099617224108750156551477 103089114760195327176701)
                    ·
                      rfl

theorem cell22_301148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_301148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301148 prefixEnd_301148 := by exact prefixLift 301148
  have htrace : WordTrace (prefixWord ++ tailWord_301148) baseStart_301148 baseEnd_301148 := by
    simpa [prefixWord, tailWord_301148, baseEnd_301148] using wordTrace_append hprefix tailTrace_301148
  have hstable : (prefixWord ++ tailWord_301148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301148).length < 2 ^ (prefixWord ++ tailWord_301148).sum := by decide
  have hdescent : baseEnd_301148 < baseStart_301148 := by decide
  rcases family_descends (prefixWord ++ tailWord_301148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301161 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 6]
def baseStart_301161 : Nat := 118140960795 + 301161 * 2 ^ 59
def prefixEnd_301161 : Nat := 4983230072969 + 3 ^ 40 * 301161 * 2
def baseEnd_301161 : Nat := 34364521641955875533887

theorem tailTrace_301161 : CollatzResearch.WordTrace tailWord_301161 prefixEnd_301161 34364521641955875533887 := by
  unfold tailWord_301161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984244061952606049023337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7322829374635070699348891 10984244061952606049023337)
  ·
    refine ⟨8238183046464454536767503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10984244061952606049023337 8238183046464454536767503)
    ·
      refine ⟨12357274569696681805151255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238183046464454536767503 12357274569696681805151255)
      ·
        refine ⟨18535911854545022707726883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357274569696681805151255 18535911854545022707726883)
        ·
          refine ⟨27803867781817534061590325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18535911854545022707726883 27803867781817534061590325)
          ·
            refine ⟨2606612604545393818274093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27803867781817534061590325 2606612604545393818274093)
            ·
              refine ⟨977479726704522681852785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2606612604545393818274093 977479726704522681852785)
              ·
                refine ⟨733109795028392011389589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977479726704522681852785 733109795028392011389589)
                ·
                  refine ⟨34364521641955875533887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 733109795028392011389589 34364521641955875533887)
                  ·
                    rfl

theorem cell22_301161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_301161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301161 prefixEnd_301161 := by exact prefixLift 301161
  have htrace : WordTrace (prefixWord ++ tailWord_301161) baseStart_301161 baseEnd_301161 := by
    simpa [prefixWord, tailWord_301161, baseEnd_301161] using wordTrace_append hprefix tailTrace_301161
  have hstable : (prefixWord ++ tailWord_301161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301161).length < 2 ^ (prefixWord ++ tailWord_301161).sum := by decide
  have hdescent : baseEnd_301161 < baseStart_301161 := by decide
  rcases family_descends (prefixWord ++ tailWord_301161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301180 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_301180 : Nat := 118140960795 + 301180 * 2 ^ 59
def prefixEnd_301180 : Nat := 4983230072969 + 3 ^ 40 * 301180 * 2
def baseEnd_301180 : Nat := 103100069014157910376603

theorem tailTrace_301180 : CollatzResearch.WordTrace tailWord_301180 prefixEnd_301180 103100069014157910376603 := by
  unfold tailWord_301180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492468524441886146982497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7323291365922514862643329 5492468524441886146982497)
  ·
    refine ⟨4119351393331414610236873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5492468524441886146982497 4119351393331414610236873)
    ·
      refine ⟨3089513544998560957677655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119351393331414610236873 3089513544998560957677655)
      ·
        refine ⟨4634270317497841436516483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089513544998560957677655 4634270317497841436516483)
        ·
          refine ⟨6951405476246762154774725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634270317497841436516483 6951405476246762154774725)
          ·
            refine ⟨1303388526796267904020261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6951405476246762154774725 1303388526796267904020261)
            ·
              refine ⟨244385348774300232003799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1303388526796267904020261 244385348774300232003799)
              ·
                refine ⟨366578023161450348005699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244385348774300232003799 366578023161450348005699)
                ·
                  refine ⟨549867034742175522008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366578023161450348005699 549867034742175522008549)
                  ·
                    refine ⟨103100069014157910376603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 549867034742175522008549 103100069014157910376603)
                    ·
                      rfl

theorem cell22_301180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_301180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301180 prefixEnd_301180 := by exact prefixLift 301180
  have htrace : WordTrace (prefixWord ++ tailWord_301180) baseStart_301180 baseEnd_301180 := by
    simpa [prefixWord, tailWord_301180, baseEnd_301180] using wordTrace_append hprefix tailTrace_301180
  have hstable : (prefixWord ++ tailWord_301180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301180).length < 2 ^ (prefixWord ++ tailWord_301180).sum := by decide
  have hdescent : baseEnd_301180 < baseStart_301180 := by decide
  rcases family_descends (prefixWord ++ tailWord_301180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301193 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_301193 : Nat := 118140960795 + 301193 * 2 ^ 59
def prefixEnd_301193 : Nat := 4983230072969 + 3 ^ 40 * 301193 * 2
def baseEnd_301193 : Nat := 103104519179830209801563

theorem tailTrace_301193 : CollatzResearch.WordTrace tailWord_301193 prefixEnd_301193 103104519179830209801563 := by
  unfold tailWord_301193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985411197836675514188233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7323607465224450342792155 10985411197836675514188233)
  ·
    refine ⟨8239058398377506635641175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10985411197836675514188233 8239058398377506635641175)
    ·
      refine ⟨12358587597566259953461763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8239058398377506635641175 12358587597566259953461763)
      ·
        refine ⟨18537881396349389930192645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12358587597566259953461763 18537881396349389930192645)
        ·
          refine ⟨3475852761815510611911121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18537881396349389930192645 3475852761815510611911121)
          ·
            refine ⟨2606889571361632958933341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475852761815510611911121 2606889571361632958933341)
            ·
              refine ⟨977583589260612359600003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2606889571361632958933341 977583589260612359600003)
              ·
                refine ⟨1466375383890918539400005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977583589260612359600003 1466375383890918539400005)
                ·
                  refine ⟨274945384479547226137501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466375383890918539400005 274945384479547226137501)
                  ·
                    refine ⟨103104519179830209801563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274945384479547226137501 103104519179830209801563)
                    ·
                      rfl

theorem cell22_301193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_301193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301193 prefixEnd_301193 := by exact prefixLift 301193
  have htrace : WordTrace (prefixWord ++ tailWord_301193) baseStart_301193 baseEnd_301193 := by
    simpa [prefixWord, tailWord_301193, baseEnd_301193] using wordTrace_append hprefix tailTrace_301193
  have hstable : (prefixWord ++ tailWord_301193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301193).length < 2 ^ (prefixWord ++ tailWord_301193).sum := by decide
  have hdescent : baseEnd_301193 < baseStart_301193 := by decide
  rcases family_descends (prefixWord ++ tailWord_301193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301221 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_301221 : Nat := 118140960795 + 301221 * 2 ^ 59
def prefixEnd_301221 : Nat := 4983230072969 + 3 ^ 40 * 301221 * 2
def baseEnd_301221 : Nat := 103114104152047470101477

theorem tailTrace_301221 : CollatzResearch.WordTrace tailWord_301221 prefixEnd_301221 103114104152047470101477 := by
  unfold tailWord_301221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10986432441735236296207517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7324288294490157530805011 10986432441735236296207517)
  ·
    refine ⟨4119912165650713611077819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10986432441735236296207517 4119912165650713611077819)
    ·
      refine ⟨6179868248476070416616729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119912165650713611077819 6179868248476070416616729)
      ·
        refine ⟨4634901186357052812462547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6179868248476070416616729 4634901186357052812462547)
        ·
          refine ⟨6952351779535579218693821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634901186357052812462547 6952351779535579218693821)
          ·
            refine ⟨2607131917325842207010183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6952351779535579218693821 2607131917325842207010183)
            ·
              refine ⟨3910697875988763310515275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607131917325842207010183 3910697875988763310515275)
              ·
                refine ⟨5866046813983144965772913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910697875988763310515275 5866046813983144965772913)
                ·
                  refine ⟨4399535110487358724329685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5866046813983144965772913 4399535110487358724329685)
                  ·
                    refine ⟨103114104152047470101477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4399535110487358724329685 103114104152047470101477)
                    ·
                      rfl

theorem cell22_301221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_301221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301221 prefixEnd_301221 := by exact prefixLift 301221
  have htrace : WordTrace (prefixWord ++ tailWord_301221) baseStart_301221 baseEnd_301221 := by
    simpa [prefixWord, tailWord_301221, baseEnd_301221] using wordTrace_append hprefix tailTrace_301221
  have hstable : (prefixWord ++ tailWord_301221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301221).length < 2 ^ (prefixWord ++ tailWord_301221).sum := by decide
  have hdescent : baseEnd_301221 < baseStart_301221 := by decide
  rcases family_descends (prefixWord ++ tailWord_301221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301313 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 6]
def baseStart_301313 : Nat := 118140960795 + 301313 * 2 ^ 59
def prefixEnd_301313 : Nat := 4983230072969 + 3 ^ 40 * 301313 * 2
def baseEnd_301313 : Nat := 34381865877396632267065

theorem tailTrace_301313 : CollatzResearch.WordTrace tailWord_301313 prefixEnd_301313 34381865877396632267065 := by
  unfold tailWord_301313
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989787957401936008556593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7326525304934624005704395 10989787957401936008556593)
  ·
    refine ⟨8242340968051452006417445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10989787957401936008556593 8242340968051452006417445)
    ·
      refine ⟨1545438931509647251203271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8242340968051452006417445 1545438931509647251203271)
      ·
        refine ⟨2318158397264470876804907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545438931509647251203271 2318158397264470876804907)
        ·
          refine ⟨3477237595896706315207361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318158397264470876804907 3477237595896706315207361)
          ·
            refine ⟨2607928196922529736405521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477237595896706315207361 2607928196922529736405521)
            ·
              refine ⟨1955946147691897302304141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607928196922529736405521 1955946147691897302304141)
              ·
                refine ⟨733479805384461488364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955946147691897302304141 733479805384461488364053)
                ·
                  refine ⟨34381865877396632267065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 733479805384461488364053 34381865877396632267065)
                  ·
                    rfl

theorem cell22_301313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_301313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301313 prefixEnd_301313 := by exact prefixLift 301313
  have htrace : WordTrace (prefixWord ++ tailWord_301313) baseStart_301313 baseEnd_301313 := by
    simpa [prefixWord, tailWord_301313, baseEnd_301313] using wordTrace_append hprefix tailTrace_301313
  have hstable : (prefixWord ++ tailWord_301313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301313).length < 2 ^ (prefixWord ++ tailWord_301313).sum := by decide
  have hdescent : baseEnd_301313 < baseStart_301313 := by decide
  rcases family_descends (prefixWord ++ tailWord_301313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301349 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_301349 : Nat := 118140960795 + 301349 * 2 ^ 59
def prefixEnd_301349 : Nat := 4983230072969 + 3 ^ 40 * 301349 * 2
def baseEnd_301349 : Nat := 103157921167897802901085

theorem tailTrace_301349 : CollatzResearch.WordTrace tailWord_301349 prefixEnd_301349 103157921167897802901085 := by
  unfold tailWord_301349
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991100985271514156867101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7327400656847676104578067 10991100985271514156867101)
  ·
    refine ⟨4121662869476817808825163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10991100985271514156867101 4121662869476817808825163)
    ·
      refine ⟨6182494304215226713237745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121662869476817808825163 6182494304215226713237745)
      ·
        refine ⟨4636870728161420034928309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6182494304215226713237745 4636870728161420034928309)
        ·
          refine ⟨434706630765133128274529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4636870728161420034928309 434706630765133128274529)
          ·
            refine ⟨326029973073849846205897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434706630765133128274529 326029973073849846205897)
            ·
              refine ⟨244522479805387384654423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326029973073849846205897 244522479805387384654423)
              ·
                refine ⟨366783719708081076981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244522479805387384654423 366783719708081076981635)
                ·
                  refine ⟨550175579562121615472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366783719708081076981635 550175579562121615472453)
                  ·
                    refine ⟨103157921167897802901085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550175579562121615472453 103157921167897802901085)
                    ·
                      rfl

theorem cell22_301349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_301349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301349 prefixEnd_301349 := by exact prefixLift 301349
  have htrace : WordTrace (prefixWord ++ tailWord_301349) baseStart_301349 baseEnd_301349 := by
    simpa [prefixWord, tailWord_301349, baseEnd_301349] using wordTrace_append hprefix tailTrace_301349
  have hstable : (prefixWord ++ tailWord_301349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301349).length < 2 ^ (prefixWord ++ tailWord_301349).sum := by decide
  have hdescent : baseEnd_301349 < baseStart_301349 := by decide
  rcases family_descends (prefixWord ++ tailWord_301349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301362 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_301362 : Nat := 118140960795 + 301362 * 2 ^ 59
def prefixEnd_301362 : Nat := 4983230072969 + 3 ^ 40 * 301362 * 2
def baseEnd_301362 : Nat := 103162371333570102326045

theorem tailTrace_301362 : CollatzResearch.WordTrace tailWord_301362 prefixEnd_301362 103162371333570102326045 := by
  unfold tailWord_301362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747893783556104344272585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7327716756149611584726893 2747893783556104344272585)
  ·
    refine ⟨2060920337667078258204439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2747893783556104344272585 2060920337667078258204439)
    ·
      refine ⟨3091380506500617387306659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060920337667078258204439 3091380506500617387306659)
      ·
        refine ⟨4637070759750926080959989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091380506500617387306659 4637070759750926080959989)
        ·
          refine ⟨434725383726649320089999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4637070759750926080959989 434725383726649320089999)
          ·
            refine ⟨652088075589973980134999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434725383726649320089999 652088075589973980134999)
            ·
              refine ⟨978132113384960970202499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652088075589973980134999 978132113384960970202499)
              ·
                refine ⟨1467198170077441455303749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978132113384960970202499 1467198170077441455303749)
                ·
                  refine ⟨275099656889520272869453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467198170077441455303749 275099656889520272869453)
                  ·
                    refine ⟨103162371333570102326045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275099656889520272869453 103162371333570102326045)
                    ·
                      rfl

theorem cell22_301362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_301362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301362 prefixEnd_301362 := by exact prefixLift 301362
  have htrace : WordTrace (prefixWord ++ tailWord_301362) baseStart_301362 baseEnd_301362 := by
    simpa [prefixWord, tailWord_301362, baseEnd_301362] using wordTrace_append hprefix tailTrace_301362
  have hstable : (prefixWord ++ tailWord_301362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301362).length < 2 ^ (prefixWord ++ tailWord_301362).sum := by decide
  have hdescent : baseEnd_301362 < baseStart_301362 := by decide
  rcases family_descends (prefixWord ++ tailWord_301362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301390 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_301390 : Nat := 118140960795 + 301390 * 2 ^ 59
def prefixEnd_301390 : Nat := 4983230072969 + 3 ^ 40 * 301390 * 2
def baseEnd_301390 : Nat := 103171956305787362625959

theorem tailTrace_301390 : CollatzResearch.WordTrace tailWord_301390 prefixEnd_301390 103171956305787362625959 := by
  unfold tailWord_301390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374074547265372269888703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7328397585415318772739749 1374074547265372269888703)
  ·
    refine ⟨2061111820898058404833055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374074547265372269888703 2061111820898058404833055)
    ·
      refine ⟨3091667731347087607249583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061111820898058404833055 3091667731347087607249583)
      ·
        refine ⟨4637501597020631410874375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091667731347087607249583 4637501597020631410874375)
        ·
          refine ⟨6956252395530947116311563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637501597020631410874375 6956252395530947116311563)
          ·
            refine ⟨10434378593296420674467345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956252395530947116311563 10434378593296420674467345)
            ·
              refine ⟨7825783944972315505850509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10434378593296420674467345 7825783944972315505850509)
              ·
                refine ⟨2934668979364618314693941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825783944972315505850509 2934668979364618314693941)
                ·
                  refine ⟨275125216815432967002557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2934668979364618314693941 275125216815432967002557)
                  ·
                    refine ⟨103171956305787362625959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275125216815432967002557 103171956305787362625959)
                    ·
                      rfl

theorem cell22_301390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_301390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301390 prefixEnd_301390 := by exact prefixLift 301390
  have htrace : WordTrace (prefixWord ++ tailWord_301390) baseStart_301390 baseEnd_301390 := by
    simpa [prefixWord, tailWord_301390, baseEnd_301390] using wordTrace_append hprefix tailTrace_301390
  have hstable : (prefixWord ++ tailWord_301390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301390).length < 2 ^ (prefixWord ++ tailWord_301390).sum := by decide
  have hdescent : baseEnd_301390 < baseStart_301390 := by decide
  rcases family_descends (prefixWord ++ tailWord_301390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301430 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_301430 : Nat := 118140960795 + 301430 * 2 ^ 59
def prefixEnd_301430 : Nat := 4983230072969 + 3 ^ 40 * 301430 * 2
def baseEnd_301430 : Nat := 103185649123240591625837

theorem tailTrace_301430 : CollatzResearch.WordTrace tailWord_301430 prefixEnd_301430 103185649123240591625837 := by
  unfold tailWord_301430
  simp only [CollatzResearch.WordTrace]
  refine ⟨687128456123629061910359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7329370198652043327043829 687128456123629061910359)
  ·
    refine ⟨1030692684185443592865539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687128456123629061910359 1030692684185443592865539)
    ·
      refine ⟨1546039026278165389298309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030692684185443592865539 1546039026278165389298309)
      ·
        refine ⟨289882317427156010493433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1546039026278165389298309 289882317427156010493433)
        ·
          refine ⟨217411738070367007870075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289882317427156010493433 217411738070367007870075)
          ·
            refine ⟨326117607105550511805113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217411738070367007870075 326117607105550511805113)
            ·
              refine ⟨244588205329162883853835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326117607105550511805113 244588205329162883853835)
              ·
                refine ⟨366882307993744325780753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244588205329162883853835 366882307993744325780753)
                ·
                  refine ⟨275161730995308244335565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366882307993744325780753 275161730995308244335565)
                  ·
                    refine ⟨103185649123240591625837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275161730995308244335565 103185649123240591625837)
                    ·
                      rfl

theorem cell22_301430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_301430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301430 prefixEnd_301430 := by exact prefixLift 301430
  have htrace : WordTrace (prefixWord ++ tailWord_301430) baseStart_301430 baseEnd_301430 := by
    simpa [prefixWord, tailWord_301430, baseEnd_301430] using wordTrace_append hprefix tailTrace_301430
  have hstable : (prefixWord ++ tailWord_301430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301430).length < 2 ^ (prefixWord ++ tailWord_301430).sum := by decide
  have hdescent : baseEnd_301430 < baseStart_301430 := by decide
  rcases family_descends (prefixWord ++ tailWord_301430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301433 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_301433 : Nat := 118140960795 + 301433 * 2 ^ 59
def prefixEnd_301433 : Nat := 4983230072969 + 3 ^ 40 * 301433 * 2
def baseEnd_301433 : Nat := 103186676084549583800827

theorem tailTrace_301433 : CollatzResearch.WordTrace tailWord_301433 prefixEnd_301433 103186676084549583800827 := by
  unfold tailWord_301433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994164716967196502924953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7329443144644797668616635 10994164716967196502924953)
  ·
    refine ⟨8245623537725397377193715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10994164716967196502924953 8245623537725397377193715)
    ·
      refine ⟨12368435306588096065790573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8245623537725397377193715 12368435306588096065790573)
      ·
        refine ⟨4638163239970536024671465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12368435306588096065790573 4638163239970536024671465)
        ·
          refine ⟨3478622429977902018503599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4638163239970536024671465 3478622429977902018503599)
          ·
            refine ⟨5217933644966853027755399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478622429977902018503599 5217933644966853027755399)
            ·
              refine ⟨7826900467450279541633099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217933644966853027755399 7826900467450279541633099)
              ·
                refine ⟨11740350701175419312449649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7826900467450279541633099 11740350701175419312449649)
                ·
                  refine ⟨8805263025881564484337237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11740350701175419312449649 8805263025881564484337237)
                  ·
                    refine ⟨103186676084549583800827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8805263025881564484337237 103186676084549583800827)
                    ·
                      rfl

theorem cell22_301433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_301433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301433 prefixEnd_301433 := by exact prefixLift 301433
  have htrace : WordTrace (prefixWord ++ tailWord_301433) baseStart_301433 baseEnd_301433 := by
    simpa [prefixWord, tailWord_301433, baseEnd_301433] using wordTrace_append hprefix tailTrace_301433
  have hstable : (prefixWord ++ tailWord_301433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301433).length < 2 ^ (prefixWord ++ tailWord_301433).sum := by decide
  have hdescent : baseEnd_301433 < baseStart_301433 := by decide
  rcases family_descends (prefixWord ++ tailWord_301433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301437 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 5]
def baseStart_301437 : Nat := 118140960795 + 301437 * 2 ^ 59
def prefixEnd_301437 : Nat := 4983230072969 + 3 ^ 40 * 301437 * 2
def baseEnd_301437 : Nat := 34396015122098302233605

theorem tailTrace_301437 : CollatzResearch.WordTrace tailWord_301437 prefixEnd_301437 34396015122098302233605 := by
  unfold tailWord_301437
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994310608952705186070565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7329540405968470124047043 10994310608952705186070565)
  ·
    refine ⟨2061433239178632222388231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10994310608952705186070565 2061433239178632222388231)
    ·
      refine ⟨3092149858767948333582347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061433239178632222388231 3092149858767948333582347)
      ·
        refine ⟨4638224788151922500373521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3092149858767948333582347 4638224788151922500373521)
        ·
          refine ⟨3478668591113941875280141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4638224788151922500373521 3478668591113941875280141)
          ·
            refine ⟨1304500721667728203230053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3478668591113941875280141 1304500721667728203230053)
            ·
              refine ⟨244593885312699038105635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1304500721667728203230053 244593885312699038105635)
              ·
                refine ⟨366890827969048557158453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244593885312699038105635 366890827969048557158453)
                ·
                  refine ⟨34396015122098302233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 366890827969048557158453 34396015122098302233605)
                  ·
                    rfl

theorem cell22_301437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_301437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301437 prefixEnd_301437 := by exact prefixLift 301437
  have htrace : WordTrace (prefixWord ++ tailWord_301437) baseStart_301437 baseEnd_301437 := by
    simpa [prefixWord, tailWord_301437, baseEnd_301437] using wordTrace_append hprefix tailTrace_301437
  have hstable : (prefixWord ++ tailWord_301437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301437).length < 2 ^ (prefixWord ++ tailWord_301437).sum := by decide
  have hdescent : baseEnd_301437 < baseStart_301437 := by decide
  rcases family_descends (prefixWord ++ tailWord_301437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301497 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_301497 : Nat := 118140960795 + 301497 * 2 ^ 59
def prefixEnd_301497 : Nat := 4983230072969 + 3 ^ 40 * 301497 * 2
def baseEnd_301497 : Nat := 103208584592474750200631

theorem tailTrace_301497 : CollatzResearch.WordTrace tailWord_301497 prefixEnd_301497 103208584592474750200631 := by
  unfold tailWord_301497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996498988735335433254745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7330999325823556955503163 10996498988735335433254745)
  ·
    refine ⟨8247374241551501574941059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10996498988735335433254745 8247374241551501574941059)
    ·
      refine ⟨12371061362327252362411589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8247374241551501574941059 12371061362327252362411589)
      ·
        refine ⟨2319574005436359817952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12371061362327252362411589 2319574005436359817952173)
        ·
          refine ⟨869840252038634931732065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2319574005436359817952173 869840252038634931732065)
          ·
            refine ⟨652380189028976198799049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 869840252038634931732065 652380189028976198799049)
            ·
              refine ⟨489285141771732149099287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652380189028976198799049 489285141771732149099287)
              ·
                refine ⟨733927712657598223648931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489285141771732149099287 733927712657598223648931)
                ·
                  refine ⟨1100891568986397335473397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733927712657598223648931 1100891568986397335473397)
                  ·
                    refine ⟨103208584592474750200631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1100891568986397335473397 103208584592474750200631)
                    ·
                      rfl

theorem cell22_301497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_301497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301497 prefixEnd_301497 := by exact prefixLift 301497
  have htrace : WordTrace (prefixWord ++ tailWord_301497) baseStart_301497 baseEnd_301497 := by
    simpa [prefixWord, tailWord_301497, baseEnd_301497] using wordTrace_append hprefix tailTrace_301497
  have hstable : (prefixWord ++ tailWord_301497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301497).length < 2 ^ (prefixWord ++ tailWord_301497).sum := by decide
  have hdescent : baseEnd_301497 < baseStart_301497 := by decide
  rcases family_descends (prefixWord ++ tailWord_301497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301512 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_301512 : Nat := 118140960795 + 301512 * 2 ^ 59
def prefixEnd_301512 : Nat := 4983230072969 + 3 ^ 40 * 301512 * 2
def baseEnd_301512 : Nat := 103213719399019711075585

theorem tailTrace_301512 : CollatzResearch.WordTrace tailWord_301512 prefixEnd_301512 103213719399019711075585 := by
  unfold tailWord_301512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5498523041840496497525395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7331364055787328663367193 5498523041840496497525395)
  ·
    refine ⟨8247784562760744746288093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5498523041840496497525395 8247784562760744746288093)
    ·
      refine ⟨3092919211035279279858035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8247784562760744746288093 3092919211035279279858035)
      ·
        refine ⟨4639378816552918919787053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3092919211035279279858035 4639378816552918919787053)
        ·
          refine ⟨1739767056207344594920145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4639378816552918919787053 1739767056207344594920145)
          ·
            refine ⟨1304825292155508446190109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739767056207344594920145 1304825292155508446190109)
            ·
              refine ⟨489309484558315667321291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1304825292155508446190109 489309484558315667321291)
              ·
                refine ⟨733964226837473500981937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489309484558315667321291 733964226837473500981937)
                ·
                  refine ⟨550473170128105125736453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733964226837473500981937 550473170128105125736453)
                  ·
                    refine ⟨103213719399019711075585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550473170128105125736453 103213719399019711075585)
                    ·
                      rfl

theorem cell22_301512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_301512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301512 prefixEnd_301512 := by exact prefixLift 301512
  have htrace : WordTrace (prefixWord ++ tailWord_301512) baseStart_301512 baseEnd_301512 := by
    simpa [prefixWord, tailWord_301512, baseEnd_301512] using wordTrace_append hprefix tailTrace_301512
  have hstable : (prefixWord ++ tailWord_301512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301512).length < 2 ^ (prefixWord ++ tailWord_301512).sum := by decide
  have hdescent : baseEnd_301512 < baseStart_301512 := by decide
  rcases family_descends (prefixWord ++ tailWord_301512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301572 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_301572 : Nat := 118140960795 + 301572 * 2 ^ 59
def prefixEnd_301572 : Nat := 4983230072969 + 3 ^ 40 * 301572 * 2
def baseEnd_301572 : Nat := 34411419541733184858467

theorem tailTrace_301572 : CollatzResearch.WordTrace tailWord_301572 prefixEnd_301572 34411419541733184858467 := by
  unfold tailWord_301572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499617231731811621117485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7332822975642415494823313 5499617231731811621117485)
  ·
    refine ⟨2062356461899429357919057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5499617231731811621117485 2062356461899429357919057)
    ·
      refine ⟨1546767346424572018439293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062356461899429357919057 1546767346424572018439293)
      ·
        refine ⟨580037754909214506914735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1546767346424572018439293 580037754909214506914735)
        ·
          refine ⟨870056632363821760372103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580037754909214506914735 870056632363821760372103)
          ·
            refine ⟨1305084948545732640558155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870056632363821760372103 1305084948545732640558155)
            ·
              refine ⟨1957627422818598960837233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305084948545732640558155 1957627422818598960837233)
              ·
                refine ⟨1468220567113949220627925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957627422818598960837233 1468220567113949220627925)
                ·
                  refine ⟨34411419541733184858467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1468220567113949220627925 34411419541733184858467)
                  ·
                    rfl

theorem cell22_301572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_301572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301572 prefixEnd_301572 := by exact prefixLift 301572
  have htrace : WordTrace (prefixWord ++ tailWord_301572) baseStart_301572 baseEnd_301572 := by
    simpa [prefixWord, tailWord_301572, baseEnd_301572] using wordTrace_append hprefix tailTrace_301572
  have hstable : (prefixWord ++ tailWord_301572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301572).length < 2 ^ (prefixWord ++ tailWord_301572).sum := by decide
  have hdescent : baseEnd_301572 < baseStart_301572 := by decide
  rcases family_descends (prefixWord ++ tailWord_301572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301602 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_301602 : Nat := 118140960795 + 301602 * 2 ^ 59
def prefixEnd_301602 : Nat := 4983230072969 + 3 ^ 40 * 301602 * 2
def baseEnd_301602 : Nat := 103244528238289476325309

theorem tailTrace_301602 : CollatzResearch.WordTrace tailWord_301602 prefixEnd_301602 103244528238289476325309 := by
  unfold tailWord_301602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750082163338734591456765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7333552435569958910551373 2750082163338734591456765)
  ·
    refine ⟨1031280811252025471796287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2750082163338734591456765 1031280811252025471796287)
    ·
      refine ⟨1546921216878038207694431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031280811252025471796287 1546921216878038207694431)
      ·
        refine ⟨2320381825317057311541647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546921216878038207694431 2320381825317057311541647)
        ·
          refine ⟨3480572737975585967312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320381825317057311541647 3480572737975585967312471)
          ·
            refine ⟨5220859106963378950968707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480572737975585967312471 5220859106963378950968707)
            ·
              refine ⟨7831288660445068426453061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220859106963378950968707 7831288660445068426453061)
              ·
                refine ⟨1468366623833450329959949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7831288660445068426453061 1468366623833450329959949)
                ·
                  refine ⟨550637483937543873734981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1468366623833450329959949 550637483937543873734981)
                  ·
                    refine ⟨103244528238289476325309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550637483937543873734981 103244528238289476325309)
                    ·
                      rfl

theorem cell22_301602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_301602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301602 prefixEnd_301602 := by exact prefixLift 301602
  have htrace : WordTrace (prefixWord ++ tailWord_301602) baseStart_301602 baseEnd_301602 := by
    simpa [prefixWord, tailWord_301602, baseEnd_301602] using wordTrace_append hprefix tailTrace_301602
  have hstable : (prefixWord ++ tailWord_301602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301602).length < 2 ^ (prefixWord ++ tailWord_301602).sum := by decide
  have hdescent : baseEnd_301602 < baseStart_301602 := by decide
  rcases family_descends (prefixWord ++ tailWord_301602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301615 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_301615 : Nat := 118140960795 + 301615 * 2 ^ 59
def prefixEnd_301615 : Nat := 4983230072969 + 3 ^ 40 * 301615 * 2
def baseEnd_301615 : Nat := 103248978403961775750269

theorem tailTrace_301615 : CollatzResearch.WordTrace tailWord_301615 prefixEnd_301615 103248978403961775750269 := by
  unfold tailWord_301615
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000802802307841586050299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7333868534871894390700199 11000802802307841586050299)
  ·
    refine ⟨16501204203461762379075449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11000802802307841586050299 16501204203461762379075449)
    ·
      refine ⟨12375903152596321784306587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16501204203461762379075449 12375903152596321784306587)
      ·
        refine ⟨18563854728894482676459881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375903152596321784306587 18563854728894482676459881)
        ·
          refine ⟨13922891046670862007344911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18563854728894482676459881 13922891046670862007344911)
          ·
            refine ⟨20884336570006293011017367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13922891046670862007344911 20884336570006293011017367)
            ·
              refine ⟨31326504855009439516526051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20884336570006293011017367 31326504855009439516526051)
              ·
                refine ⟨46989757282514159274789077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31326504855009439516526051 46989757282514159274789077)
                ·
                  refine ⟨1101322436308925608002869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46989757282514159274789077 1101322436308925608002869)
                  ·
                    refine ⟨103248978403961775750269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1101322436308925608002869 103248978403961775750269)
                    ·
                      rfl

theorem cell22_301615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_301615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301615 prefixEnd_301615 := by exact prefixLift 301615
  have htrace : WordTrace (prefixWord ++ tailWord_301615) baseStart_301615 baseEnd_301615 := by
    simpa [prefixWord, tailWord_301615, baseEnd_301615] using wordTrace_append hprefix tailTrace_301615
  have hstable : (prefixWord ++ tailWord_301615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301615).length < 2 ^ (prefixWord ++ tailWord_301615).sum := by decide
  have hdescent : baseEnd_301615 < baseStart_301615 := by decide
  rcases family_descends (prefixWord ++ tailWord_301615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301632 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_301632 : Nat := 118140960795 + 301632 * 2 ^ 59
def prefixEnd_301632 : Nat := 4983230072969 + 3 ^ 40 * 301632 * 2
def baseEnd_301632 : Nat := 103254797851379398075217

theorem tailTrace_301632 : CollatzResearch.WordTrace tailWord_301632 prefixEnd_301632 103254797851379398075217 := by
  unfold tailWord_301632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500711421623126744709575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7334281895497502326279433 5500711421623126744709575)
  ·
    refine ⟨8251067132434690117064363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500711421623126744709575 8251067132434690117064363)
    ·
      refine ⟨12376600698652035175596545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8251067132434690117064363 12376600698652035175596545)
      ·
        refine ⟨9282450523989026381697409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12376600698652035175596545 9282450523989026381697409)
        ·
          refine ⟨6961837892991769786273057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9282450523989026381697409 6961837892991769786273057)
          ·
            refine ⟨5221378419743827339704793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6961837892991769786273057 5221378419743827339704793)
            ·
              refine ⟨3916033814807870504778595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5221378419743827339704793 3916033814807870504778595)
              ·
                refine ⟨5874050722211805757167893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916033814807870504778595 5874050722211805757167893)
                ·
                  refine ⟨275346127603678394867245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5874050722211805757167893 275346127603678394867245)
                  ·
                    refine ⟨103254797851379398075217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275346127603678394867245 103254797851379398075217)
                    ·
                      rfl

theorem cell22_301632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_301632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301632 prefixEnd_301632 := by exact prefixLift 301632
  have htrace : WordTrace (prefixWord ++ tailWord_301632) baseStart_301632 baseEnd_301632 := by
    simpa [prefixWord, tailWord_301632, baseEnd_301632] using wordTrace_append hprefix tailTrace_301632
  have hstable : (prefixWord ++ tailWord_301632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301632).length < 2 ^ (prefixWord ++ tailWord_301632).sum := by decide
  have hdescent : baseEnd_301632 < baseStart_301632 := by decide
  rcases family_descends (prefixWord ++ tailWord_301632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301647 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_301647 : Nat := 118140960795 + 301647 * 2 ^ 59
def prefixEnd_301647 : Nat := 4983230072969 + 3 ^ 40 * 301647 * 2
def baseEnd_301647 : Nat := 103259932657924358950171

theorem tailTrace_301647 : CollatzResearch.WordTrace tailWord_301647 prefixEnd_301647 103259932657924358950171 := by
  unfold tailWord_301647
  simp only [CollatzResearch.WordTrace]
  refine ⟨11001969938191911051215195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7334646625461274034143463 11001969938191911051215195)
  ·
    refine ⟨16502954907287866576822793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11001969938191911051215195 16502954907287866576822793)
    ·
      refine ⟨12377216180465899932617095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16502954907287866576822793 12377216180465899932617095)
      ·
        refine ⟨18565824270698849898925643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12377216180465899932617095 18565824270698849898925643)
        ·
          refine ⟨27848736406048274848388465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18565824270698849898925643 27848736406048274848388465)
          ·
            refine ⟨20886552304536206136291349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27848736406048274848388465 20886552304536206136291349)
            ·
              refine ⟨979057139275134662638657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20886552304536206136291349 979057139275134662638657)
              ·
                refine ⟨734292854456350996978993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979057139275134662638657 734292854456350996978993)
                ·
                  refine ⟨550719640842263247734245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734292854456350996978993 550719640842263247734245)
                  ·
                    refine ⟨103259932657924358950171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550719640842263247734245 103259932657924358950171)
                    ·
                      rfl

theorem cell22_301647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_301647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301647 prefixEnd_301647 := by exact prefixLift 301647
  have htrace : WordTrace (prefixWord ++ tailWord_301647) baseStart_301647 baseEnd_301647 := by
    simpa [prefixWord, tailWord_301647, baseEnd_301647] using wordTrace_append hprefix tailTrace_301647
  have hstable : (prefixWord ++ tailWord_301647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301647).length < 2 ^ (prefixWord ++ tailWord_301647).sum := by decide
  have hdescent : baseEnd_301647 < baseStart_301647 := by decide
  rcases family_descends (prefixWord ++ tailWord_301647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301649 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_301649 : Nat := 118140960795 + 301649 * 2 ^ 59
def prefixEnd_301649 : Nat := 4983230072969 + 3 ^ 40 * 301649 * 2
def baseEnd_301649 : Nat := 103260617298797020400165

theorem tailTrace_301649 : CollatzResearch.WordTrace tailWord_301649 prefixEnd_301649 103260617298797020400165 := by
  unfold tailWord_301649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11002042884184665392788001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7334695256123110261858667 11002042884184665392788001)
  ·
    refine ⟨8251532163138499044591001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11002042884184665392788001 8251532163138499044591001)
    ·
      refine ⟨6188649122353874283443251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8251532163138499044591001 6188649122353874283443251)
      ·
        refine ⟨9282973683530811425164877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188649122353874283443251 9282973683530811425164877)
        ·
          refine ⟨3481115131324054284436829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9282973683530811425164877 3481115131324054284436829)
          ·
            refine ⟨1305418174246520356663811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3481115131324054284436829 1305418174246520356663811)
            ·
              refine ⟨1958127261369780534995717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305418174246520356663811 1958127261369780534995717)
              ·
                refine ⟨367148861506833850311697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1958127261369780534995717 367148861506833850311697)
                ·
                  refine ⟨275361646130125387733773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367148861506833850311697 275361646130125387733773)
                  ·
                    refine ⟨103260617298797020400165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275361646130125387733773 103260617298797020400165)
                    ·
                      rfl

theorem cell22_301649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_301649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301649 prefixEnd_301649 := by exact prefixLift 301649
  have htrace : WordTrace (prefixWord ++ tailWord_301649) baseStart_301649 baseEnd_301649 := by
    simpa [prefixWord, tailWord_301649, baseEnd_301649] using wordTrace_append hprefix tailTrace_301649
  have hstable : (prefixWord ++ tailWord_301649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301649).length < 2 ^ (prefixWord ++ tailWord_301649).sum := by decide
  have hdescent : baseEnd_301649 < baseStart_301649 := by decide
  rcases family_descends (prefixWord ++ tailWord_301649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301707 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 5]
def baseStart_301707 : Nat := 118140960795 + 301707 * 2 ^ 59
def prefixEnd_301707 : Nat := 4983230072969 + 3 ^ 40 * 301707 * 2
def baseEnd_301707 : Nat := 34426823961368067483329

theorem tailTrace_301707 : CollatzResearch.WordTrace tailWord_301707 prefixEnd_301707 34426823961368067483329 := by
  unfold tailWord_301707
  simp only [CollatzResearch.WordTrace]
  refine ⟨11004158317974541298399375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7336105545316360865599583 11004158317974541298399375)
  ·
    refine ⟨16506237476961811947599063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11004158317974541298399375 16506237476961811947599063)
    ·
      refine ⟨24759356215442717921398595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16506237476961811947599063 24759356215442717921398595)
      ·
        refine ⟨37139034323164076882097893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24759356215442717921398595 37139034323164076882097893)
        ·
          refine ⟨6963568935593264415393355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37139034323164076882097893 6963568935593264415393355)
          ·
            refine ⟨10445353403389896623090033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963568935593264415393355 10445353403389896623090033)
            ·
              refine ⟨7834015052542422467317525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10445353403389896623090033 7834015052542422467317525)
              ·
                refine ⟨367219455587926053155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7834015052542422467317525 367219455587926053155509)
                ·
                  refine ⟨34426823961368067483329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367219455587926053155509 34426823961368067483329)
                  ·
                    rfl

theorem cell22_301707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 5].length) (baseStart_301707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301707 prefixEnd_301707 := by exact prefixLift 301707
  have htrace : WordTrace (prefixWord ++ tailWord_301707) baseStart_301707 baseEnd_301707 := by
    simpa [prefixWord, tailWord_301707, baseEnd_301707] using wordTrace_append hprefix tailTrace_301707
  have hstable : (prefixWord ++ tailWord_301707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301707).length < 2 ^ (prefixWord ++ tailWord_301707).sum := by decide
  have hdescent : baseEnd_301707 < baseStart_301707 := by decide
  rcases family_descends (prefixWord ++ tailWord_301707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301754 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_301754 : Nat := 118140960795 + 301754 * 2 ^ 59
def prefixEnd_301754 : Nat := 4983230072969 + 3 ^ 40 * 301754 * 2
def baseEnd_301754 : Nat := 103296560944611746524843

theorem tailTrace_301754 : CollatzResearch.WordTrace tailWord_301754 prefixEnd_301754 103296560944611746524843 := by
  unfold tailWord_301754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2751468137201067081340079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7337248365869512216906877 2751468137201067081340079)
  ·
    refine ⟨4127202205801600622010119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2751468137201067081340079 4127202205801600622010119)
    ·
      refine ⟨6190803308702400933015179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4127202205801600622010119 6190803308702400933015179)
      ·
        refine ⟨9286204963053601399522769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6190803308702400933015179 9286204963053601399522769)
        ·
          refine ⟨6964653722290201049642077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9286204963053601399522769 6964653722290201049642077)
          ·
            refine ⟨2611745145858825393615779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6964653722290201049642077 2611745145858825393615779)
            ·
              refine ⟨3917617718788238090423669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611745145858825393615779 3917617718788238090423669)
              ·
                refine ⟨367276661136397320977219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3917617718788238090423669 367276661136397320977219)
                ·
                  refine ⟨550914991704595981465829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367276661136397320977219 550914991704595981465829)
                  ·
                    refine ⟨103296560944611746524843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550914991704595981465829 103296560944611746524843)
                    ·
                      rfl

theorem cell22_301754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_301754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301754 prefixEnd_301754 := by exact prefixLift 301754
  have htrace : WordTrace (prefixWord ++ tailWord_301754) baseStart_301754 baseEnd_301754 := by
    simpa [prefixWord, tailWord_301754, baseEnd_301754] using wordTrace_append hprefix tailTrace_301754
  have hstable : (prefixWord ++ tailWord_301754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301754).length < 2 ^ (prefixWord ++ tailWord_301754).sum := by decide
  have hdescent : baseEnd_301754 < baseStart_301754 := by decide
  rcases family_descends (prefixWord ++ tailWord_301754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301767 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_301767 : Nat := 118140960795 + 301767 * 2 ^ 59
def prefixEnd_301767 : Nat := 4983230072969 + 3 ^ 40 * 301767 * 2
def baseEnd_301767 : Nat := 103301011110284045949803

theorem tailTrace_301767 : CollatzResearch.WordTrace tailWord_301767 prefixEnd_301767 103301011110284045949803 := by
  unfold tailWord_301767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006346697757171545583555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337564465171447697055703 11006346697757171545583555)
  ·
    refine ⟨16509520046635757318375333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006346697757171545583555 16509520046635757318375333)
    ·
      refine ⟨3095535008744204497195375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16509520046635757318375333 3095535008744204497195375)
      ·
        refine ⟨4643302513116306745793063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095535008744204497195375 4643302513116306745793063)
        ·
          refine ⟨6964953769674460118689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643302513116306745793063 6964953769674460118689595)
          ·
            refine ⟨10447430654511690178034393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964953769674460118689595 10447430654511690178034393)
            ·
              refine ⟨7835572990883767633525795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10447430654511690178034393 7835572990883767633525795)
              ·
                refine ⟨11753359486325651450288693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7835572990883767633525795 11753359486325651450288693)
                ·
                  refine ⟨1101877451843029823464565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11753359486325651450288693 1101877451843029823464565)
                  ·
                    refine ⟨103301011110284045949803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1101877451843029823464565 103301011110284045949803)
                    ·
                      rfl

theorem cell22_301767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_301767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301767 prefixEnd_301767 := by exact prefixLift 301767
  have htrace : WordTrace (prefixWord ++ tailWord_301767) baseStart_301767 baseEnd_301767 := by
    simpa [prefixWord, tailWord_301767, baseEnd_301767] using wordTrace_append hprefix tailTrace_301767
  have hstable : (prefixWord ++ tailWord_301767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301767).length < 2 ^ (prefixWord ++ tailWord_301767).sum := by decide
  have hdescent : baseEnd_301767 < baseStart_301767 := by decide
  rcases family_descends (prefixWord ++ tailWord_301767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301788 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_301788 : Nat := 118140960795 + 301788 * 2 ^ 59
def prefixEnd_301788 : Nat := 4983230072969 + 3 ^ 40 * 301788 * 2
def baseEnd_301788 : Nat := 103308199839446991174739

theorem tailTrace_301788 : CollatzResearch.WordTrace tailWord_301788 prefixEnd_301788 103308199839446991174739 := by
  unfold tailWord_301788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503556315340546066049009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7338075087120728088065345 5503556315340546066049009)
  ·
    refine ⟨4127667236505409549536757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5503556315340546066049009 4127667236505409549536757)
    ·
      refine ⟨386968803422382145269071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4127667236505409549536757 386968803422382145269071)
      ·
        refine ⟨580453205133573217903607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386968803422382145269071 580453205133573217903607)
        ·
          refine ⟨870679807700359826855411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580453205133573217903607 870679807700359826855411)
          ·
            refine ⟨1306019711550539740283117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870679807700359826855411 1306019711550539740283117)
            ·
              refine ⟨489757391831452402606169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1306019711550539740283117 489757391831452402606169)
              ·
                refine ⟨367318043873589301954627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489757391831452402606169 367318043873589301954627)
                ·
                  refine ⟨550977065810383952931941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367318043873589301954627 550977065810383952931941)
                  ·
                    refine ⟨103308199839446991174739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550977065810383952931941 103308199839446991174739)
                    ·
                      rfl

theorem cell22_301788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_301788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301788 prefixEnd_301788 := by exact prefixLift 301788
  have htrace : WordTrace (prefixWord ++ tailWord_301788) baseStart_301788 baseEnd_301788 := by
    simpa [prefixWord, tailWord_301788, baseEnd_301788] using wordTrace_append hprefix tailTrace_301788
  have hstable : (prefixWord ++ tailWord_301788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301788).length < 2 ^ (prefixWord ++ tailWord_301788).sum := by decide
  have hdescent : baseEnd_301788 < baseStart_301788 := by decide
  rcases family_descends (prefixWord ++ tailWord_301788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301829 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_301829 : Nat := 118140960795 + 301829 * 2 ^ 59
def prefixEnd_301829 : Nat := 4983230072969 + 3 ^ 40 * 301829 * 2
def baseEnd_301829 : Nat := 103322234977336550899613

theorem tailTrace_301829 : CollatzResearch.WordTrace tailWord_301829 prefixEnd_301829 103322234977336550899613 := by
  unfold tailWord_301829
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008608023532556134340541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7339072015688370756227027 11008608023532556134340541)
  ·
    refine ⟨4128228008824708550377703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11008608023532556134340541 4128228008824708550377703)
    ·
      refine ⟨6192342013237062825566555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4128228008824708550377703 6192342013237062825566555)
      ·
        refine ⟨9288513019855594238349833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192342013237062825566555 9288513019855594238349833)
        ·
          refine ⟨6966384764891695678762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288513019855594238349833 6966384764891695678762375)
          ·
            refine ⟨10449577147337543518143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966384764891695678762375 10449577147337543518143563)
            ·
              refine ⟨15674365721006315277215345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449577147337543518143563 15674365721006315277215345)
              ·
                refine ⟨11755774290754736457911509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15674365721006315277215345 11755774290754736457911509)
                ·
                  refine ⟨275525959939564135732301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11755774290754736457911509 275525959939564135732301)
                  ·
                    refine ⟨103322234977336550899613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275525959939564135732301 103322234977336550899613)
                    ·
                      rfl

theorem cell22_301829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_301829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301829 prefixEnd_301829 := by exact prefixLift 301829
  have htrace : WordTrace (prefixWord ++ tailWord_301829) baseStart_301829 baseEnd_301829 := by
    simpa [prefixWord, tailWord_301829, baseEnd_301829] using wordTrace_append hprefix tailTrace_301829
  have hstable : (prefixWord ++ tailWord_301829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301829).length < 2 ^ (prefixWord ++ tailWord_301829).sum := by decide
  have hdescent : baseEnd_301829 < baseStart_301829 := by decide
  rcases family_descends (prefixWord ++ tailWord_301829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301831 : List Nat := [1, 1, 4, 4, 1, 3, 1, 7]
def baseStart_301831 : Nat := 118140960795 + 301831 * 2 ^ 59
def prefixEnd_301831 : Nat := 4983230072969 + 3 ^ 40 * 301831 * 2
def baseEnd_301831 : Nat := 11480324402023245816623

theorem tailTrace_301831 : CollatzResearch.WordTrace tailWord_301831 prefixEnd_301831 11480324402023245816623 := by
  unfold tailWord_301831
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008680969525310475913347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7339120646350206983942231 11008680969525310475913347)
  ·
    refine ⟨16513021454287965713870021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11008680969525310475913347 16513021454287965713870021)
    ·
      refine ⟨3096191522678993571350629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16513021454287965713870021 3096191522678993571350629)
      ·
        refine ⟨580535910502311294628243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3096191522678993571350629 580535910502311294628243)
        ·
          refine ⟨870803865753466941942365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580535910502311294628243 870803865753466941942365)
          ·
            refine ⟨326551449657550103228387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 870803865753466941942365 326551449657550103228387)
            ·
              refine ⟨489827174486325154842581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326551449657550103228387 489827174486325154842581)
              ·
                refine ⟨11480324402023245816623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 489827174486325154842581 11480324402023245816623)
                ·
                  rfl

theorem cell22_301831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 7].length) (baseStart_301831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301831 prefixEnd_301831 := by exact prefixLift 301831
  have htrace : WordTrace (prefixWord ++ tailWord_301831) baseStart_301831 baseEnd_301831 := by
    simpa [prefixWord, tailWord_301831, baseEnd_301831] using wordTrace_append hprefix tailTrace_301831
  have hstable : (prefixWord ++ tailWord_301831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301831).length < 2 ^ (prefixWord ++ tailWord_301831).sum := by decide
  have hdescent : baseEnd_301831 < baseStart_301831 := by decide
  rcases family_descends (prefixWord ++ tailWord_301831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301869 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_301869 : Nat := 118140960795 + 301869 * 2 ^ 59
def prefixEnd_301869 : Nat := 4983230072969 + 3 ^ 40 * 301869 * 2
def baseEnd_301869 : Nat := 103335927794789779899491

theorem tailTrace_301869 : CollatzResearch.WordTrace tailWord_301869 prefixEnd_301869 103335927794789779899491 := by
  unfold tailWord_301869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010066943387642965796661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340044628925095310531107 11010066943387642965796661)
  ·
    refine ⟨1032193775942591528043437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11010066943387642965796661 1032193775942591528043437)
    ·
      refine ⟨387072665978471823016289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1032193775942591528043437 387072665978471823016289)
      ·
        refine ⟨290304499483853867262217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387072665978471823016289 290304499483853867262217)
        ·
          refine ⟨217728374612890400446663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290304499483853867262217 217728374612890400446663)
          ·
            refine ⟨326592561919335600669995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217728374612890400446663 326592561919335600669995)
            ·
              refine ⟨489888842879003401004993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326592561919335600669995 489888842879003401004993)
              ·
                refine ⟨367416632159252550753745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489888842879003401004993 367416632159252550753745)
                ·
                  refine ⟨275562474119439413065309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367416632159252550753745 275562474119439413065309)
                  ·
                    refine ⟨103335927794789779899491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275562474119439413065309 103335927794789779899491)
                    ·
                      rfl

theorem cell22_301869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_301869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301869 prefixEnd_301869 := by exact prefixLift 301869
  have htrace : WordTrace (prefixWord ++ tailWord_301869) baseStart_301869 baseEnd_301869 := by
    simpa [prefixWord, tailWord_301869, baseEnd_301869] using wordTrace_append hprefix tailTrace_301869
  have hstable : (prefixWord ++ tailWord_301869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301869).length < 2 ^ (prefixWord ++ tailWord_301869).sum := by decide
  have hdescent : baseEnd_301869 < baseStart_301869 := by decide
  rcases family_descends (prefixWord ++ tailWord_301869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301874 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_301874 : Nat := 118140960795 + 301874 * 2 ^ 59
def prefixEnd_301874 : Nat := 4983230072969 + 3 ^ 40 * 301874 * 2
def baseEnd_301874 : Nat := 103337639396971433524475

theorem tailTrace_301874 : CollatzResearch.WordTrace tailWord_301874 prefixEnd_301874 103337639396971433524475 := by
  unfold tailWord_301874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752562327092382204932169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7340166205579685879819117 2752562327092382204932169)
  ·
    refine ⟨2064421745319286653699127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2752562327092382204932169 2064421745319286653699127)
    ·
      refine ⟨3096632617978929980548691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064421745319286653699127 3096632617978929980548691)
      ·
        refine ⟨4644948926968394970823037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096632617978929980548691 4644948926968394970823037)
        ·
          refine ⟨1741855847613148114058639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4644948926968394970823037 1741855847613148114058639)
          ·
            refine ⟨2612783771419722171087959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741855847613148114058639 2612783771419722171087959)
            ·
              refine ⟨3919175657129583256631939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612783771419722171087959 3919175657129583256631939)
              ·
                refine ⟨5878763485694374884947909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919175657129583256631939 5878763485694374884947909)
                ·
                  refine ⟨1102268153567695290927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5878763485694374884947909 1102268153567695290927733)
                  ·
                    refine ⟨103337639396971433524475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1102268153567695290927733 103337639396971433524475)
                    ·
                      rfl

theorem cell22_301874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_301874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301874 prefixEnd_301874 := by exact prefixLift 301874
  have htrace : WordTrace (prefixWord ++ tailWord_301874) baseStart_301874 baseEnd_301874 := by
    simpa [prefixWord, tailWord_301874, baseEnd_301874] using wordTrace_append hprefix tailTrace_301874
  have hstable : (prefixWord ++ tailWord_301874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301874).length < 2 ^ (prefixWord ++ tailWord_301874).sum := by decide
  have hdescent : baseEnd_301874 < baseStart_301874 := by decide
  rcases family_descends (prefixWord ++ tailWord_301874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301904 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_301904 : Nat := 118140960795 + 301904 * 2 ^ 59
def prefixEnd_301904 : Nat := 4983230072969 + 3 ^ 40 * 301904 * 2
def baseEnd_301904 : Nat := 34449303003353785091461

theorem tailTrace_301904 : CollatzResearch.WordTrace tailWord_301904 prefixEnd_301904 34449303003353785091461 := by
  unfold tailWord_301904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505671749130421971660383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7340895665507229295547177 5505671749130421971660383)
  ·
    refine ⟨8258507623695632957490575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5505671749130421971660383 8258507623695632957490575)
    ·
      refine ⟨12387761435543449436235863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258507623695632957490575 12387761435543449436235863)
      ·
        refine ⟨18581642153315174154353795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387761435543449436235863 18581642153315174154353795)
        ·
          refine ⟨27872463229972761231530693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18581642153315174154353795 27872463229972761231530693)
          ·
            refine ⟨5226086855619892730912005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27872463229972761231530693 5226086855619892730912005)
            ·
              refine ⟨979891285428729887046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5226086855619892730912005 979891285428729887046001)
              ·
                refine ⟨734918464071547415284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979891285428729887046001 734918464071547415284501)
                ·
                  refine ⟨34449303003353785091461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 734918464071547415284501 34449303003353785091461)
                  ·
                    rfl

theorem cell22_301904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_301904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301904 prefixEnd_301904 := by exact prefixLift 301904
  have htrace : WordTrace (prefixWord ++ tailWord_301904) baseStart_301904 baseEnd_301904 := by
    simpa [prefixWord, tailWord_301904, baseEnd_301904] using wordTrace_append hprefix tailTrace_301904
  have hstable : (prefixWord ++ tailWord_301904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301904).length < 2 ^ (prefixWord ++ tailWord_301904).sum := by decide
  have hdescent : baseEnd_301904 < baseStart_301904 := by decide
  rcases family_descends (prefixWord ++ tailWord_301904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301919 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_301919 : Nat := 118140960795 + 301919 * 2 ^ 59
def prefixEnd_301919 : Nat := 4983230072969 + 3 ^ 40 * 301919 * 2
def baseEnd_301919 : Nat := 103353043816606316149337

theorem tailTrace_301919 : CollatzResearch.WordTrace tailWord_301919 prefixEnd_301919 103353043816606316149337 := by
  unfold tailWord_301919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011890593206501505116811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7341260395471001003411207 11011890593206501505116811)
  ·
    refine ⟨16517835889809752257675217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11011890593206501505116811 16517835889809752257675217)
    ·
      refine ⟨12388376917357314193256413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16517835889809752257675217 12388376917357314193256413)
      ·
        refine ⟨4645641344008992822471155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12388376917357314193256413 4645641344008992822471155)
        ·
          refine ⟨6968462016013489233706733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645641344008992822471155 6968462016013489233706733)
          ·
            refine ⟨2613173256005058462640025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6968462016013489233706733 2613173256005058462640025)
            ·
              refine ⟨1959879942003793846980019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613173256005058462640025 1959879942003793846980019)
              ·
                refine ⟨2939819913005690770470029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959879942003793846980019 2939819913005690770470029)
                ·
                  refine ⟨1102432467377134038926261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2939819913005690770470029 1102432467377134038926261)
                  ·
                    refine ⟨103353043816606316149337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1102432467377134038926261 103353043816606316149337)
                    ·
                      rfl

theorem cell22_301919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_301919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301919 prefixEnd_301919 := by exact prefixLift 301919
  have htrace : WordTrace (prefixWord ++ tailWord_301919) baseStart_301919 baseEnd_301919 := by
    simpa [prefixWord, tailWord_301919, baseEnd_301919] using wordTrace_append hprefix tailTrace_301919
  have hstable : (prefixWord ++ tailWord_301919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301919).length < 2 ^ (prefixWord ++ tailWord_301919).sum := by decide
  have hdescent : baseEnd_301919 < baseStart_301919 := by decide
  rcases family_descends (prefixWord ++ tailWord_301919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301921 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 4]
def baseStart_301921 : Nat := 118140960795 + 301921 * 2 ^ 59
def prefixEnd_301921 : Nat := 4983230072969 + 3 ^ 40 * 301921 * 2
def baseEnd_301921 : Nat := 34451242819159659199777

theorem tailTrace_301921 : CollatzResearch.WordTrace tailWord_301921 prefixEnd_301921 34451242819159659199777 := by
  unfold tailWord_301921
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011963539199255846689617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7341309026132837231126411 11011963539199255846689617)
  ·
    refine ⟨8258972654399441885017213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011963539199255846689617 8258972654399441885017213)
    ·
      refine ⟨3097114745399790706881455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8258972654399441885017213 3097114745399790706881455)
      ·
        refine ⟨4645672118099686060322183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097114745399790706881455 4645672118099686060322183)
        ·
          refine ⟨6968508177149529090483275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645672118099686060322183 6968508177149529090483275)
          ·
            refine ⟨10452762265724293635724913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968508177149529090483275 10452762265724293635724913)
            ·
              refine ⟨7839571699293220226793685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10452762265724293635724913 7839571699293220226793685)
              ·
                refine ⟨183739961702184849065477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7839571699293220226793685 183739961702184849065477)
                ·
                  refine ⟨34451242819159659199777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183739961702184849065477 34451242819159659199777)
                  ·
                    rfl

theorem cell22_301921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_301921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301921 prefixEnd_301921 := by exact prefixLift 301921
  have htrace : WordTrace (prefixWord ++ tailWord_301921) baseStart_301921 baseEnd_301921 := by
    simpa [prefixWord, tailWord_301921, baseEnd_301921] using wordTrace_append hprefix tailTrace_301921
  have hstable : (prefixWord ++ tailWord_301921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301921).length < 2 ^ (prefixWord ++ tailWord_301921).sum := by decide
  have hdescent : baseEnd_301921 < baseStart_301921 := by decide
  rcases family_descends (prefixWord ++ tailWord_301921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301936 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_301936 : Nat := 118140960795 + 301936 * 2 ^ 59
def prefixEnd_301936 : Nat := 4983230072969 + 3 ^ 40 * 301936 * 2
def baseEnd_301936 : Nat := 103358863264023938474285

theorem tailTrace_301936 : CollatzResearch.WordTrace tailWord_301936 prefixEnd_301936 103358863264023938474285 := by
  unfold tailWord_301936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506255317072456704242831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7341673756096608938990441 5506255317072456704242831)
  ·
    refine ⟨8259382975608685056364247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506255317072456704242831 8259382975608685056364247)
    ·
      refine ⟨12389074463413027584546371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8259382975608685056364247 12389074463413027584546371)
      ·
        refine ⟨18583611695119541376819557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12389074463413027584546371 18583611695119541376819557)
        ·
          refine ⟨3484427192834914008153667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18583611695119541376819557 3484427192834914008153667)
          ·
            refine ⟨5226640789252371012230501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484427192834914008153667 5226640789252371012230501)
            ·
              refine ⟨979995147984819564793219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5226640789252371012230501 979995147984819564793219)
              ·
                refine ⟨1469992721977229347189829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979995147984819564793219 1469992721977229347189829)
                ·
                  refine ⟨275623635370730502598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469992721977229347189829 275623635370730502598093)
                  ·
                    refine ⟨103358863264023938474285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275623635370730502598093 103358863264023938474285)
                    ·
                      rfl

theorem cell22_301936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_301936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301936 prefixEnd_301936 := by exact prefixLift 301936
  have htrace : WordTrace (prefixWord ++ tailWord_301936) baseStart_301936 baseEnd_301936 := by
    simpa [prefixWord, tailWord_301936, baseEnd_301936] using wordTrace_append hprefix tailTrace_301936
  have hstable : (prefixWord ++ tailWord_301936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301936).length < 2 ^ (prefixWord ++ tailWord_301936).sum := by decide
  have hdescent : baseEnd_301936 < baseStart_301936 := by decide
  rcases family_descends (prefixWord ++ tailWord_301936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301949 : List Nat := [1, 4, 1, 1, 2, 1, 3, 9]
def baseStart_301949 : Nat := 118140960795 + 301949 * 2 ^ 59
def prefixEnd_301949 : Nat := 4983230072969 + 3 ^ 40 * 301949 * 2
def baseEnd_301949 : Nat := 11484812603299581988805

theorem tailTrace_301949 : CollatzResearch.WordTrace tailWord_301949 prefixEnd_301949 11484812603299581988805 := by
  unfold tailWord_301949
  simp only [CollatzResearch.WordTrace]
  refine ⟨11012984783097816628708901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7341989855398544419139267 11012984783097816628708901)
  ·
    refine ⟨2064934646830840617882919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11012984783097816628708901 2064934646830840617882919)
    ·
      refine ⟨3097401970246260926824379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064934646830840617882919 3097401970246260926824379)
      ·
        refine ⟨4646102955369391390236569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097401970246260926824379 4646102955369391390236569)
        ·
          refine ⟨3484577216527043542677427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646102955369391390236569 3484577216527043542677427)
          ·
            refine ⟨5226865824790565314016141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484577216527043542677427 5226865824790565314016141)
            ·
              refine ⟨1960074684296461992756053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5226865824790565314016141 1960074684296461992756053)
              ·
                refine ⟨11484812603299581988805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1960074684296461992756053 11484812603299581988805)
                ·
                  rfl

theorem cell22_301949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 9].length) (baseStart_301949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301949 prefixEnd_301949 := by exact prefixLift 301949
  have htrace : WordTrace (prefixWord ++ tailWord_301949) baseStart_301949 baseEnd_301949 := by
    simpa [prefixWord, tailWord_301949, baseEnd_301949] using wordTrace_append hprefix tailTrace_301949
  have hstable : (prefixWord ++ tailWord_301949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301949).length < 2 ^ (prefixWord ++ tailWord_301949).sum := by decide
  have hdescent : baseEnd_301949 < baseStart_301949 := by decide
  rcases family_descends (prefixWord ++ tailWord_301949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301964 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_301964 : Nat := 118140960795 + 301964 * 2 ^ 59
def prefixEnd_301964 : Nat := 4983230072969 + 3 ^ 40 * 301964 * 2
def baseEnd_301964 : Nat := 103368448236241198774199

theorem tailTrace_301964 : CollatzResearch.WordTrace tailWord_301964 prefixEnd_301964 103368448236241198774199 := by
  unfold tailWord_301964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506765939021737095252473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7342354585362316127003297 5506765939021737095252473)
  ·
    refine ⟨4130074454266302821439355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5506765939021737095252473 4130074454266302821439355)
    ·
      refine ⟨6195111681399454232159033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130074454266302821439355 6195111681399454232159033)
      ·
        refine ⟨4646333761049590674119275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6195111681399454232159033 4646333761049590674119275)
        ·
          refine ⟨6969500641574386011178913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646333761049590674119275 6969500641574386011178913)
          ·
            refine ⟨5227125481180789508384185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969500641574386011178913 5227125481180789508384185)
            ·
              refine ⟨3920344110885592131288139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227125481180789508384185 3920344110885592131288139)
              ·
                refine ⟨5880516166328388196932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920344110885592131288139 5880516166328388196932209)
                ·
                  refine ⟨4410387124746291147699157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5880516166328388196932209 4410387124746291147699157)
                  ·
                    refine ⟨103368448236241198774199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4410387124746291147699157 103368448236241198774199)
                    ·
                      rfl

theorem cell22_301964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_301964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301964 prefixEnd_301964 := by exact prefixLift 301964
  have htrace : WordTrace (prefixWord ++ tailWord_301964) baseStart_301964 baseEnd_301964 := by
    simpa [prefixWord, tailWord_301964, baseEnd_301964] using wordTrace_append hprefix tailTrace_301964
  have hstable : (prefixWord ++ tailWord_301964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301964).length < 2 ^ (prefixWord ++ tailWord_301964).sum := by decide
  have hdescent : baseEnd_301964 < baseStart_301964 := by decide
  rcases family_descends (prefixWord ++ tailWord_301964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301974 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_301974 : Nat := 118140960795 + 301974 * 2 ^ 59
def prefixEnd_301974 : Nat := 4983230072969 + 3 ^ 40 * 301974 * 2
def baseEnd_301974 : Nat := 103371871440604506024169

theorem tailTrace_301974 : CollatzResearch.WordTrace tailWord_301974 prefixEnd_301974 103371871440604506024169 := by
  unfold tailWord_301974
  simp only [CollatzResearch.WordTrace]
  refine ⟨688368538000452868648061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7342597738671497265579317 688368538000452868648061)
  ·
    refine ⟨258138201750169825743023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 688368538000452868648061 258138201750169825743023)
    ·
      refine ⟨387207302625254738614535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258138201750169825743023 387207302625254738614535)
      ·
        refine ⟨580810953937882107921803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387207302625254738614535 580810953937882107921803)
        ·
          refine ⟨871216430906823161882705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580810953937882107921803 871216430906823161882705)
          ·
            refine ⟨653412323180117371412029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871216430906823161882705 653412323180117371412029)
            ·
              refine ⟨245029621192544014279511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653412323180117371412029 245029621192544014279511)
              ·
                refine ⟨367544431788816021419267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245029621192544014279511 367544431788816021419267)
                ·
                  refine ⟨551316647683224032128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367544431788816021419267 551316647683224032128901)
                  ·
                    refine ⟨103371871440604506024169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551316647683224032128901 103371871440604506024169)
                    ·
                      rfl

theorem cell22_301974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_301974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_301974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_301974 prefixEnd_301974 := by exact prefixLift 301974
  have htrace : WordTrace (prefixWord ++ tailWord_301974) baseStart_301974 baseEnd_301974 := by
    simpa [prefixWord, tailWord_301974, baseEnd_301974] using wordTrace_append hprefix tailTrace_301974
  have hstable : (prefixWord ++ tailWord_301974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301974).length < 2 ^ (prefixWord ++ tailWord_301974).sum := by decide
  have hdescent : baseEnd_301974 < baseStart_301974 := by decide
  rcases family_descends (prefixWord ++ tailWord_301974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302045 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 5]
def baseStart_302045 : Nat := 118140960795 + 302045 * 2 ^ 59
def prefixEnd_302045 : Nat := 4983230072969 + 3 ^ 40 * 302045 * 2
def baseEnd_302045 : Nat := 34465392063861329166317

theorem tailTrace_302045 : CollatzResearch.WordTrace tailWord_302045 prefixEnd_302045 34465392063861329166317 := by
  unfold tailWord_302045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016486190750025024203589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7344324127166683349469059 11016486190750025024203589)
  ·
    refine ⟨2065591160765629692038173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11016486190750025024203589 2065591160765629692038173)
    ·
      refine ⟨774596685287111134514315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2065591160765629692038173 774596685287111134514315)
      ·
        refine ⟨1161895027930666701771473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774596685287111134514315 1161895027930666701771473)
        ·
          refine ⟨871421270948000026328605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161895027930666701771473 871421270948000026328605)
          ·
            refine ⟨326782976605500009873227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 871421270948000026328605 326782976605500009873227)
            ·
              refine ⟨490174464908250014809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326782976605500009873227 490174464908250014809841)
              ·
                refine ⟨367630848681187511107381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490174464908250014809841 367630848681187511107381)
                ·
                  refine ⟨34465392063861329166317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367630848681187511107381 34465392063861329166317)
                  ·
                    rfl

theorem cell22_302045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_302045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302045 prefixEnd_302045 := by exact prefixLift 302045
  have htrace : WordTrace (prefixWord ++ tailWord_302045) baseStart_302045 baseEnd_302045 := by
    simpa [prefixWord, tailWord_302045, baseEnd_302045] using wordTrace_append hprefix tailTrace_302045
  have hstable : (prefixWord ++ tailWord_302045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302045).length < 2 ^ (prefixWord ++ tailWord_302045).sum := by decide
  have hdescent : baseEnd_302045 < baseStart_302045 := by decide
  rcases family_descends (prefixWord ++ tailWord_302045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302056 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_302056 : Nat := 118140960795 + 302056 * 2 ^ 59
def prefixEnd_302056 : Nat := 4983230072969 + 3 ^ 40 * 302056 * 2
def baseEnd_302056 : Nat := 34466647238794541824639

theorem tailTrace_302056 : CollatzResearch.WordTrace tailWord_302056 prefixEnd_302056 34466647238794541824639 := by
  unfold tailWord_302056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508443696855086951427011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7344591595806782601902681 5508443696855086951427011)
  ·
    refine ⟨8262665545282630427140517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508443696855086951427011 8262665545282630427140517)
    ·
      refine ⟨1549249789740493205088847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8262665545282630427140517 1549249789740493205088847)
      ·
        refine ⟨2323874684610739807633271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549249789740493205088847 2323874684610739807633271)
        ·
          refine ⟨3485812026916109711449907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323874684610739807633271 3485812026916109711449907)
          ·
            refine ⟨5228718040374164567174861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485812026916109711449907 5228718040374164567174861)
            ·
              refine ⟨1960769265140311712690573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5228718040374164567174861 1960769265140311712690573)
              ·
                refine ⟨735288474427616892258965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1960769265140311712690573 735288474427616892258965)
                ·
                  refine ⟨34466647238794541824639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 735288474427616892258965 34466647238794541824639)
                  ·
                    rfl

theorem cell22_302056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_302056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302056 prefixEnd_302056 := by exact prefixLift 302056
  have htrace : WordTrace (prefixWord ++ tailWord_302056) baseStart_302056 baseEnd_302056 := by
    simpa [prefixWord, tailWord_302056, baseEnd_302056] using wordTrace_append hprefix tailTrace_302056
  have hstable : (prefixWord ++ tailWord_302056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302056).length < 2 ^ (prefixWord ++ tailWord_302056).sum := by decide
  have hdescent : baseEnd_302056 < baseStart_302056 := by decide
  rcases family_descends (prefixWord ++ tailWord_302056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302088 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_302088 : Nat := 118140960795 + 302088 * 2 ^ 59
def prefixEnd_302088 : Nat := 4983230072969 + 3 ^ 40 * 302088 * 2
def baseEnd_302088 : Nat := 103410895970346208673819

theorem tailTrace_302088 : CollatzResearch.WordTrace tailWord_302088 prefixEnd_302088 103410895970346208673819 := by
  unfold tailWord_302088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509027264797121684009459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7345369686396162245345945 5509027264797121684009459)
  ·
    refine ⟨8263540897195682526014189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5509027264797121684009459 8263540897195682526014189)
    ·
      refine ⟨3098827836448380947255321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8263540897195682526014189 3098827836448380947255321)
      ·
        refine ⟨2324120877336285710441491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098827836448380947255321 2324120877336285710441491)
        ·
          refine ⟨3486181316004428565662237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324120877336285710441491 3486181316004428565662237)
          ·
            refine ⟨1307317993501660712123339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3486181316004428565662237 1307317993501660712123339)
            ·
              refine ⟨1960976990252491068185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307317993501660712123339 1960976990252491068185009)
              ·
                refine ⟨1470732742689368301138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960976990252491068185009 1470732742689368301138757)
                ·
                  refine ⟨275762389254256556463517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470732742689368301138757 275762389254256556463517)
                  ·
                    refine ⟨103410895970346208673819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275762389254256556463517 103410895970346208673819)
                    ·
                      rfl

theorem cell22_302088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_302088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302088 prefixEnd_302088 := by exact prefixLift 302088
  have htrace : WordTrace (prefixWord ++ tailWord_302088) baseStart_302088 baseEnd_302088 := by
    simpa [prefixWord, tailWord_302088, baseEnd_302088] using wordTrace_append hprefix tailTrace_302088
  have hstable : (prefixWord ++ tailWord_302088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302088).length < 2 ^ (prefixWord ++ tailWord_302088).sum := by decide
  have hdescent : baseEnd_302088 < baseStart_302088 := by decide
  rcases family_descends (prefixWord ++ tailWord_302088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302090 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_302090 : Nat := 118140960795 + 302090 * 2 ^ 59
def prefixEnd_302090 : Nat := 4983230072969 + 3 ^ 40 * 302090 * 2
def baseEnd_302090 : Nat := 34470526870406290041271

theorem tailTrace_302090 : CollatzResearch.WordTrace tailWord_302090 prefixEnd_302090 34470526870406290041271 := by
  unfold tailWord_302090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754531868896749427397931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7345418317057998473061149 2754531868896749427397931)
  ·
    refine ⟨4131797803345124141096897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754531868896749427397931 4131797803345124141096897)
    ·
      refine ⟨3098848352508843105822673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4131797803345124141096897 3098848352508843105822673)
      ·
        refine ⟨2324136264381632329367005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098848352508843105822673 2324136264381632329367005)
        ·
          refine ⟨871551099143112123512627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2324136264381632329367005 871551099143112123512627)
          ·
            refine ⟨1307326648714668185268941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871551099143112123512627 1307326648714668185268941)
            ·
              refine ⟨490247493268000569475853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307326648714668185268941 490247493268000569475853)
              ·
                refine ⟨183842809975500213553445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490247493268000569475853 183842809975500213553445)
                ·
                  refine ⟨34470526870406290041271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183842809975500213553445 34470526870406290041271)
                  ·
                    rfl

theorem cell22_302090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_302090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302090 prefixEnd_302090 := by exact prefixLift 302090
  have htrace : WordTrace (prefixWord ++ tailWord_302090) baseStart_302090 baseEnd_302090 := by
    simpa [prefixWord, tailWord_302090, baseEnd_302090] using wordTrace_append hprefix tailTrace_302090
  have hstable : (prefixWord ++ tailWord_302090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302090).length < 2 ^ (prefixWord ++ tailWord_302090).sum := by decide
  have hdescent : baseEnd_302090 < baseStart_302090 := by decide
  rcases family_descends (prefixWord ++ tailWord_302090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302101 : List Nat := [1, 3, 2, 1, 4, 1, 10]
def baseStart_302101 : Nat := 118140960795 + 302101 * 2 ^ 59
def prefixEnd_302101 : Nat := 4983230072969 + 3 ^ 40 * 302101 * 2
def baseEnd_302101 : Nat := 3830198005037722522177

theorem tailTrace_302101 : CollatzResearch.WordTrace tailWord_302101 prefixEnd_302101 3830198005037722522177 := by
  unfold tailWord_302101
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018528678547146588242157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345685785698097725494771 11018528678547146588242157)
  ·
    refine ⟨4131948254455179970590809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11018528678547146588242157 4131948254455179970590809)
    ·
      refine ⟨3098961190841384977943107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4131948254455179970590809 3098961190841384977943107)
      ·
        refine ⟨4648441786262077466914661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098961190841384977943107 4648441786262077466914661)
        ·
          refine ⟨871582834924139525046499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4648441786262077466914661 871582834924139525046499)
          ·
            refine ⟨1307374252386209287569749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871582834924139525046499 1307374252386209287569749)
            ·
              refine ⟨3830198005037722522177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1307374252386209287569749 3830198005037722522177)
              ·
                rfl

theorem cell22_302101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 10].length) (baseStart_302101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302101 prefixEnd_302101 := by exact prefixLift 302101
  have htrace : WordTrace (prefixWord ++ tailWord_302101) baseStart_302101 baseEnd_302101 := by
    simpa [prefixWord, tailWord_302101, baseEnd_302101] using wordTrace_append hprefix tailTrace_302101
  have hstable : (prefixWord ++ tailWord_302101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302101).length < 2 ^ (prefixWord ++ tailWord_302101).sum := by decide
  have hdescent : baseEnd_302101 < baseStart_302101 := by decide
  rcases family_descends (prefixWord ++ tailWord_302101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302103 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_302103 : Nat := 118140960795 + 302103 * 2 ^ 59
def prefixEnd_302103 : Nat := 4983230072969 + 3 ^ 40 * 302103 * 2
def baseEnd_302103 : Nat := 103416030776891169548773

theorem tailTrace_302103 : CollatzResearch.WordTrace tailWord_302103 prefixEnd_302103 103416030776891169548773 := by
  unfold tailWord_302103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018601624539900929814963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345734416359933953209975 11018601624539900929814963)
  ·
    refine ⟨16527902436809851394722445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11018601624539900929814963 16527902436809851394722445)
    ·
      refine ⟨6197963413803694273020917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16527902436809851394722445 6197963413803694273020917)
      ·
        refine ⟨581059070044096338095711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6197963413803694273020917 581059070044096338095711)
        ·
          refine ⟨871588605066144507143567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581059070044096338095711 871588605066144507143567)
          ·
            refine ⟨1307382907599216760715351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871588605066144507143567 1307382907599216760715351)
            ·
              refine ⟨1961074361398825141073027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307382907599216760715351 1961074361398825141073027)
              ·
                refine ⟨2941611542098237711609541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961074361398825141073027 2941611542098237711609541)
                ·
                  refine ⟨551552164143419570926789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2941611542098237711609541 551552164143419570926789)
                  ·
                    refine ⟨103416030776891169548773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551552164143419570926789 103416030776891169548773)
                    ·
                      rfl

theorem cell22_302103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_302103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302103 prefixEnd_302103 := by exact prefixLift 302103
  have htrace : WordTrace (prefixWord ++ tailWord_302103) baseStart_302103 baseEnd_302103 := by
    simpa [prefixWord, tailWord_302103, baseEnd_302103] using wordTrace_append hprefix tailTrace_302103
  have hstable : (prefixWord ++ tailWord_302103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302103).length < 2 ^ (prefixWord ++ tailWord_302103).sum := by decide
  have hdescent : baseEnd_302103 < baseStart_302103 := by decide
  rcases family_descends (prefixWord ++ tailWord_302103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302122 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_302122 : Nat := 118140960795 + 302122 * 2 ^ 59
def prefixEnd_302122 : Nat := 4983230072969 + 3 ^ 40 * 302122 * 2
def baseEnd_302122 : Nat := 103422534865181453323715

theorem tailTrace_302122 : CollatzResearch.WordTrace tailWord_302122 prefixEnd_302122 103422534865181453323715 := by
  unfold tailWord_302122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754823652867766793689155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7346196407647378116504413 2754823652867766793689155)
  ·
    refine ⟨4132235479301650190533733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754823652867766793689155 4132235479301650190533733)
    ·
      refine ⟨774794152369059410725075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4132235479301650190533733 774794152369059410725075)
      ·
        refine ⟨1162191228553589116087613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774794152369059410725075 1162191228553589116087613)
        ·
          refine ⟨435821710707595918532855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1162191228553589116087613 435821710707595918532855)
          ·
            refine ⟨653732566061393877799283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435821710707595918532855 653732566061393877799283)
            ·
              refine ⟨980598849092090816698925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653732566061393877799283 980598849092090816698925)
              ·
                refine ⟨367724568409534056262097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980598849092090816698925 367724568409534056262097)
                ·
                  refine ⟨275793426307150542196573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367724568409534056262097 275793426307150542196573)
                  ·
                    refine ⟨103422534865181453323715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275793426307150542196573 103422534865181453323715)
                    ·
                      rfl

theorem cell22_302122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_302122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302122 prefixEnd_302122 := by exact prefixLift 302122
  have htrace : WordTrace (prefixWord ++ tailWord_302122) baseStart_302122 baseEnd_302122 := by
    simpa [prefixWord, tailWord_302122, baseEnd_302122] using wordTrace_append hprefix tailTrace_302122
  have hstable : (prefixWord ++ tailWord_302122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302122).length < 2 ^ (prefixWord ++ tailWord_302122).sum := by decide
  have hdescent : baseEnd_302122 < baseStart_302122 := by decide
  rcases family_descends (prefixWord ++ tailWord_302122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302133 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_302133 : Nat := 118140960795 + 302133 * 2 ^ 59
def prefixEnd_302133 : Nat := 4983230072969 + 3 ^ 40 * 302133 * 2
def baseEnd_302133 : Nat := 103426300389981091298681

theorem tailTrace_302133 : CollatzResearch.WordTrace tailWord_302133 prefixEnd_302133 103426300389981091298681 := by
  unfold tailWord_302133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019695814431216053407053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346463876287477368938035 11019695814431216053407053)
  ·
    refine ⟨4132385930411706020027645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11019695814431216053407053 4132385930411706020027645)
    ·
      refine ⟨1549644723904389757510367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4132385930411706020027645 1549644723904389757510367)
      ·
        refine ⟨2324467085856584636265551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549644723904389757510367 2324467085856584636265551)
        ·
          refine ⟨3486700628784876954398327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324467085856584636265551 3486700628784876954398327)
          ·
            refine ⟨5230050943177315431597491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486700628784876954398327 5230050943177315431597491)
            ·
              refine ⟨7845076414765973147396237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230050943177315431597491 7845076414765973147396237)
              ·
                refine ⟨2941903655537239930273589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7845076414765973147396237 2941903655537239930273589)
                ·
                  refine ⟨275803467706616243463149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941903655537239930273589 275803467706616243463149)
                  ·
                    refine ⟨103426300389981091298681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275803467706616243463149 103426300389981091298681)
                    ·
                      rfl

theorem cell22_302133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_302133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302133 prefixEnd_302133 := by exact prefixLift 302133
  have htrace : WordTrace (prefixWord ++ tailWord_302133) baseStart_302133 baseEnd_302133 := by
    simpa [prefixWord, tailWord_302133, baseEnd_302133] using wordTrace_append hprefix tailTrace_302133
  have hstable : (prefixWord ++ tailWord_302133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302133).length < 2 ^ (prefixWord ++ tailWord_302133).sum := by decide
  have hdescent : baseEnd_302133 < baseStart_302133 := by decide
  rcases family_descends (prefixWord ++ tailWord_302133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302270 : List Nat := [4, 2, 1, 1, 3, 3, 8]
def baseStart_302270 : Nat := 118140960795 + 302270 * 2 ^ 59
def prefixEnd_302270 : Nat := 4983230072969 + 3 ^ 40 * 302270 * 2
def baseEnd_302270 : Nat := 3832340677398459282343

theorem tailTrace_302270 : CollatzResearch.WordTrace tailWord_302270 prefixEnd_302270 3832340677398459282343 := by
  unfold tailWord_302270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378086576866861056393033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7349795076623258967429509 1378086576866861056393033)
  ·
    refine ⟨1033564932650145792294775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1378086576866861056393033 1033564932650145792294775)
    ·
      refine ⟨1550347398975218688442163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033564932650145792294775 1550347398975218688442163)
      ·
        refine ⟨2325521098462828032663245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550347398975218688442163 2325521098462828032663245)
        ·
          refine ⟨872070411923560512248717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2325521098462828032663245 872070411923560512248717)
          ·
            refine ⟨327026404471335192093269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872070411923560512248717 327026404471335192093269)
            ·
              refine ⟨3832340677398459282343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 327026404471335192093269 3832340677398459282343)
              ·
                rfl

theorem cell22_302270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 8].length) (baseStart_302270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302270 prefixEnd_302270 := by exact prefixLift 302270
  have htrace : WordTrace (prefixWord ++ tailWord_302270) baseStart_302270 baseEnd_302270 := by
    simpa [prefixWord, tailWord_302270, baseEnd_302270] using wordTrace_append hprefix tailTrace_302270
  have hstable : (prefixWord ++ tailWord_302270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302270).length < 2 ^ (prefixWord ++ tailWord_302270).sum := by decide
  have hdescent : baseEnd_302270 < baseStart_302270 := by decide
  rcases family_descends (prefixWord ++ tailWord_302270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302332 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_302332 : Nat := 118140960795 + 302332 * 2 ^ 59
def prefixEnd_302332 : Nat := 4983230072969 + 3 ^ 40 * 302332 * 2
def baseEnd_302332 : Nat := 34498140718936968524357

theorem tailTrace_302332 : CollatzResearch.WordTrace tailWord_302332 prefixEnd_302332 34498140718936968524357 := by
  unfold tailWord_302332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513476970355136519950625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7351302627140182026600833 5513476970355136519950625)
  ·
    refine ⟨4135107727766352389962969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5513476970355136519950625 4135107727766352389962969)
    ·
      refine ⟨3101330795824764292472227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135107727766352389962969 3101330795824764292472227)
      ·
        refine ⟨4651996193737146438708341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101330795824764292472227 4651996193737146438708341)
        ·
          refine ⟨436124643162857478628907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4651996193737146438708341 436124643162857478628907)
          ·
            refine ⟨654186964744286217943361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436124643162857478628907 654186964744286217943361)
            ·
              refine ⟨490640223558214663457521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654186964744286217943361 490640223558214663457521)
              ·
                refine ⟨367980167668660997593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490640223558214663457521 367980167668660997593141)
                ·
                  refine ⟨34498140718936968524357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367980167668660997593141 34498140718936968524357)
                  ·
                    rfl

theorem cell22_302332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_302332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302332 prefixEnd_302332 := by exact prefixLift 302332
  have htrace : WordTrace (prefixWord ++ tailWord_302332) baseStart_302332 baseEnd_302332 := by
    simpa [prefixWord, tailWord_302332, baseEnd_302332] using wordTrace_append hprefix tailTrace_302332
  have hstable : (prefixWord ++ tailWord_302332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302332).length < 2 ^ (prefixWord ++ tailWord_302332).sum := by decide
  have hdescent : baseEnd_302332 < baseStart_302332 := by decide
  rcases family_descends (prefixWord ++ tailWord_302332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302360 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_302360 : Nat := 118140960795 + 302360 * 2 ^ 59
def prefixEnd_302360 : Nat := 4983230072969 + 3 ^ 40 * 302360 * 2
def baseEnd_302360 : Nat := 34501335709676055290995

theorem tailTrace_302360 : CollatzResearch.WordTrace tailWord_302360 prefixEnd_302360 34501335709676055290995 := by
  unfold tailWord_302360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513987592304416910960267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7351983456405889214613689 5513987592304416910960267)
  ·
    refine ⟨8270981388456625366440401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513987592304416910960267 8270981388456625366440401)
    ·
      refine ⟨6203236041342469024830301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8270981388456625366440401 6203236041342469024830301)
      ·
        refine ⟨2326213515503425884311363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6203236041342469024830301 2326213515503425884311363)
        ·
          refine ⟨3489320273255138826467045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326213515503425884311363 3489320273255138826467045)
          ·
            refine ⟨654247551235338529962571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3489320273255138826467045 654247551235338529962571)
            ·
              refine ⟨981371326853007794943857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654247551235338529962571 981371326853007794943857)
              ·
                refine ⟨736028495139755846207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981371326853007794943857 736028495139755846207893)
                ·
                  refine ⟨34501335709676055290995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 736028495139755846207893 34501335709676055290995)
                  ·
                    rfl

theorem cell22_302360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_302360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302360 prefixEnd_302360 := by exact prefixLift 302360
  have htrace : WordTrace (prefixWord ++ tailWord_302360) baseStart_302360 baseEnd_302360 := by
    simpa [prefixWord, tailWord_302360, baseEnd_302360] using wordTrace_append hprefix tailTrace_302360
  have hstable : (prefixWord ++ tailWord_302360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302360).length < 2 ^ (prefixWord ++ tailWord_302360).sum := by decide
  have hdescent : baseEnd_302360 < baseStart_302360 := by decide
  rcases family_descends (prefixWord ++ tailWord_302360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302420 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_302420 : Nat := 118140960795 + 302420 * 2 ^ 59
def prefixEnd_302420 : Nat := 4983230072969 + 3 ^ 40 * 302420 * 2
def baseEnd_302420 : Nat := 103524546355208009372801

theorem tailTrace_302420 : CollatzResearch.WordTrace tailWord_302420 prefixEnd_302420 103524546355208009372801 := by
  unfold tailWord_302420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515081782195732034552357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7353442376260976046069809 5515081782195732034552357)
  ·
    refine ⟨1034077834161699756478567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5515081782195732034552357 1034077834161699756478567)
    ·
      refine ⟨1551116751242549634717851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034077834161699756478567 1551116751242549634717851)
      ·
        refine ⟨2326675126863824452076777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551116751242549634717851 2326675126863824452076777)
        ·
          refine ⟨1745006345147868339057583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2326675126863824452076777 1745006345147868339057583)
          ·
            refine ⟨2617509517721802508586375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745006345147868339057583 2617509517721802508586375)
            ·
              refine ⟨3926264276582703762879563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617509517721802508586375 3926264276582703762879563)
              ·
                refine ⟨5889396414874055644319345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926264276582703762879563 5889396414874055644319345)
                ·
                  refine ⟨4417047311155541733239509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5889396414874055644319345 4417047311155541733239509)
                  ·
                    refine ⟨103524546355208009372801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4417047311155541733239509 103524546355208009372801)
                    ·
                      rfl

theorem cell22_302420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_302420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302420 prefixEnd_302420 := by exact prefixLift 302420
  have htrace : WordTrace (prefixWord ++ tailWord_302420) baseStart_302420 baseEnd_302420 := by
    simpa [prefixWord, tailWord_302420, baseEnd_302420] using wordTrace_append hprefix tailTrace_302420
  have hstable : (prefixWord ++ tailWord_302420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302420).length < 2 ^ (prefixWord ++ tailWord_302420).sum := by decide
  have hdescent : baseEnd_302420 < baseStart_302420 := by decide
  rcases family_descends (prefixWord ++ tailWord_302420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302450 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_302450 : Nat := 118140960795 + 302450 * 2 ^ 59
def prefixEnd_302450 : Nat := 4983230072969 + 3 ^ 40 * 302450 * 2
def baseEnd_302450 : Nat := 34511605322765977040903

theorem tailTrace_302450 : CollatzResearch.WordTrace tailWord_302450 prefixEnd_302450 34511605322765977040903 := by
  unfold tailWord_302450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757814438570694798174201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7354171836188519461797869 2757814438570694798174201)
  ·
    refine ⟨2068360828928021098630651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2757814438570694798174201 2068360828928021098630651)
    ·
      refine ⟨3102541243392031647945977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068360828928021098630651 3102541243392031647945977)
      ·
        refine ⟨2326905932544023735959483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3102541243392031647945977 2326905932544023735959483)
        ·
          refine ⟨3490358898816035603939225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326905932544023735959483 3490358898816035603939225)
          ·
            refine ⟨2617769174112026702954419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490358898816035603939225 2617769174112026702954419)
            ·
              refine ⟨3926653761168040054431629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617769174112026702954419 3926653761168040054431629)
              ·
                refine ⟨1472495160438015020411861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3926653761168040054431629 1472495160438015020411861)
                ·
                  refine ⟨34511605322765977040903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1472495160438015020411861 34511605322765977040903)
                  ·
                    rfl

theorem cell22_302450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_302450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302450 prefixEnd_302450 := by exact prefixLift 302450
  have htrace : WordTrace (prefixWord ++ tailWord_302450) baseStart_302450 baseEnd_302450 := by
    simpa [prefixWord, tailWord_302450, baseEnd_302450] using wordTrace_append hprefix tailTrace_302450
  have hstable : (prefixWord ++ tailWord_302450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302450).length < 2 ^ (prefixWord ++ tailWord_302450).sum := by decide
  have hdescent : baseEnd_302450 < baseStart_302450 := by decide
  rcases family_descends (prefixWord ++ tailWord_302450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302467 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 5]
def baseStart_302467 : Nat := 118140960795 + 302467 * 2 ^ 59
def prefixEnd_302467 : Nat := 4983230072969 + 3 ^ 40 * 302467 * 2
def baseEnd_302467 : Nat := 34513545138571851149219

theorem tailTrace_302467 : CollatzResearch.WordTrace tailWord_302467 prefixEnd_302467 34513545138571851149219 := by
  unfold tailWord_302467
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031877795221191096065655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7354585196814127397377103 11031877795221191096065655)
  ·
    refine ⟨16547816692831786644098483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11031877795221191096065655 16547816692831786644098483)
    ·
      refine ⟨24821725039247679966147725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16547816692831786644098483 24821725039247679966147725)
      ·
        refine ⟨9308146889717879987305397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24821725039247679966147725 9308146889717879987305397)
        ·
          refine ⟨872638770911051248809881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9308146889717879987305397 872638770911051248809881)
          ·
            refine ⟨654479078183288436607411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872638770911051248809881 654479078183288436607411)
            ·
              refine ⟨981718617274932654911117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654479078183288436607411 981718617274932654911117)
              ·
                refine ⟨368144481478099745591669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981718617274932654911117 368144481478099745591669)
                ·
                  refine ⟨34513545138571851149219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368144481478099745591669 34513545138571851149219)
                  ·
                    rfl

theorem cell22_302467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].length) (baseStart_302467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302467 prefixEnd_302467 := by exact prefixLift 302467
  have htrace : WordTrace (prefixWord ++ tailWord_302467) baseStart_302467 baseEnd_302467 := by
    simpa [prefixWord, tailWord_302467, baseEnd_302467] using wordTrace_append hprefix tailTrace_302467
  have hstable : (prefixWord ++ tailWord_302467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302467).length < 2 ^ (prefixWord ++ tailWord_302467).sum := by decide
  have hdescent : baseEnd_302467 < baseStart_302467 := by decide
  rcases family_descends (prefixWord ++ tailWord_302467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302548 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_302548 : Nat := 118140960795 + 302548 * 2 ^ 59
def prefixEnd_302548 : Nat := 4983230072969 + 3 ^ 40 * 302548 * 2
def baseEnd_302548 : Nat := 103568363371058342172409

theorem tailTrace_302548 : CollatzResearch.WordTrace tailWord_302548 prefixEnd_302548 103568363371058342172409 := by
  unfold tailWord_302548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5517416053963870964882149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7356554738618494619842865 5517416053963870964882149)
  ·
    refine ⟨1034515510118225805915403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5517416053963870964882149 1034515510118225805915403)
    ·
      refine ⟨1551773265177338708873105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034515510118225805915403 1551773265177338708873105)
      ·
        refine ⟨1163829948883004031654829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551773265177338708873105 1163829948883004031654829)
        ·
          refine ⟨436436230831126511870561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1163829948883004031654829 436436230831126511870561)
          ·
            refine ⟨327327173123344883902921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436436230831126511870561 327327173123344883902921)
            ·
              refine ⟨245495379842508662927191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327327173123344883902921 245495379842508662927191)
              ·
                refine ⟨368243069763762994390787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245495379842508662927191 368243069763762994390787)
                ·
                  refine ⟨552364604645644491586181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368243069763762994390787 552364604645644491586181)
                  ·
                    refine ⟨103568363371058342172409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552364604645644491586181 103568363371058342172409)
                    ·
                      rfl

theorem cell22_302548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_302548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302548 prefixEnd_302548 := by exact prefixLift 302548
  have htrace : WordTrace (prefixWord ++ tailWord_302548) baseStart_302548 baseEnd_302548 := by
    simpa [prefixWord, tailWord_302548, baseEnd_302548] using wordTrace_append hprefix tailTrace_302548
  have hstable : (prefixWord ++ tailWord_302548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302548).length < 2 ^ (prefixWord ++ tailWord_302548).sum := by decide
  have hdescent : baseEnd_302548 < baseStart_302548 := by decide
  rcases family_descends (prefixWord ++ tailWord_302548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302557 : List Nat := [1, 4, 3, 1, 1, 3, 9]
def baseStart_302557 : Nat := 118140960795 + 302557 * 2 ^ 59
def prefixEnd_302557 : Nat := 4983230072969 + 3 ^ 40 * 302557 * 2
def baseEnd_302557 : Nat := 3835979416851308099903

theorem tailTrace_302557 : CollatzResearch.WordTrace tailWord_302557 prefixEnd_302557 3835979416851308099903 := by
  unfold tailWord_302557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035160364895136466841925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7356773576596757644561283 11035160364895136466841925)
  ·
    refine ⟨2069092568417838087532861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11035160364895136466841925 2069092568417838087532861)
    ·
      refine ⟨775909713156689282824823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2069092568417838087532861 775909713156689282824823)
      ·
        refine ⟨1163864569735033924237235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775909713156689282824823 1163864569735033924237235)
        ·
          refine ⟨1745796854602550886355853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163864569735033924237235 1745796854602550886355853)
          ·
            refine ⟨654673820475956582383445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1745796854602550886355853 654673820475956582383445)
            ·
              refine ⟨3835979416851308099903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 654673820475956582383445 3835979416851308099903)
              ·
                rfl

theorem cell22_302557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 9].length) (baseStart_302557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302557 prefixEnd_302557 := by exact prefixLift 302557
  have htrace : WordTrace (prefixWord ++ tailWord_302557) baseStart_302557 baseEnd_302557 := by
    simpa [prefixWord, tailWord_302557, baseEnd_302557] using wordTrace_append hprefix tailTrace_302557
  have hstable : (prefixWord ++ tailWord_302557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302557).length < 2 ^ (prefixWord ++ tailWord_302557).sum := by decide
  have hdescent : baseEnd_302557 < baseStart_302557 := by decide
  rcases family_descends (prefixWord ++ tailWord_302557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302561 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_302561 : Nat := 118140960795 + 302561 * 2 ^ 59
def prefixEnd_302561 : Nat := 4983230072969 + 3 ^ 40 * 302561 * 2
def baseEnd_302561 : Nat := 103572813536730641597369

theorem tailTrace_302561 : CollatzResearch.WordTrace tailWord_302561 prefixEnd_302561 103572813536730641597369 := by
  unfold tailWord_302561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035306256880645149987537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7356870837920430099991691 11035306256880645149987537)
  ·
    refine ⟨8276479692660483862490653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11035306256880645149987537 8276479692660483862490653)
    ·
      refine ⟨3103679884747681448433995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8276479692660483862490653 3103679884747681448433995)
      ·
        refine ⟨4655519827121522172650993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103679884747681448433995 4655519827121522172650993)
        ·
          refine ⟨3491639870341141629488245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4655519827121522172650993 3491639870341141629488245)
          ·
            refine ⟨327341237844482027764523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3491639870341141629488245 327341237844482027764523)
            ·
              refine ⟨491011856766723041646785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327341237844482027764523 491011856766723041646785)
              ·
                refine ⟨368258892575042281235089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491011856766723041646785 368258892575042281235089)
                ·
                  refine ⟨276194169431281710926317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368258892575042281235089 276194169431281710926317)
                  ·
                    refine ⟨103572813536730641597369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276194169431281710926317 103572813536730641597369)
                    ·
                      rfl

theorem cell22_302561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_302561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302561 prefixEnd_302561 := by exact prefixLift 302561
  have htrace : WordTrace (prefixWord ++ tailWord_302561) baseStart_302561 baseEnd_302561 := by
    simpa [prefixWord, tailWord_302561, baseEnd_302561] using wordTrace_append hprefix tailTrace_302561
  have hstable : (prefixWord ++ tailWord_302561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302561).length < 2 ^ (prefixWord ++ tailWord_302561).sum := by decide
  have hdescent : baseEnd_302561 < baseStart_302561 := by decide
  rcases family_descends (prefixWord ++ tailWord_302561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302578 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_302578 : Nat := 118140960795 + 302578 * 2 ^ 59
def prefixEnd_302578 : Nat := 4983230072969 + 3 ^ 40 * 302578 * 2
def baseEnd_302578 : Nat := 103578632984148263922317

theorem tailTrace_302578 : CollatzResearch.WordTrace tailWord_302578 prefixEnd_302578 103578632984148263922317 := by
  unfold tailWord_302578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758981574454764263339097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7357284198546038035570925 2758981574454764263339097)
  ·
    refine ⟨2069236180841073197504323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2758981574454764263339097 2069236180841073197504323)
    ·
      refine ⟨3103854271261609796256485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069236180841073197504323 3103854271261609796256485)
      ·
        refine ⟨581972675861551836798091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3103854271261609796256485 581972675861551836798091)
        ·
          refine ⟨872959013792327755197137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581972675861551836798091 872959013792327755197137)
          ·
            refine ⟨654719260344245816397853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872959013792327755197137 654719260344245816397853)
            ·
              refine ⟨245519722629092181149195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 654719260344245816397853 245519722629092181149195)
              ·
                refine ⟨368279583943638271723793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245519722629092181149195 368279583943638271723793)
                ·
                  refine ⟨276209687957728703792845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368279583943638271723793 276209687957728703792845)
                  ·
                    refine ⟨103578632984148263922317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276209687957728703792845 103578632984148263922317)
                    ·
                      rfl

theorem cell22_302578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_302578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302578 prefixEnd_302578 := by exact prefixLift 302578
  have htrace : WordTrace (prefixWord ++ tailWord_302578) baseStart_302578 baseEnd_302578 := by
    simpa [prefixWord, tailWord_302578, baseEnd_302578] using wordTrace_append hprefix tailTrace_302578
  have hstable : (prefixWord ++ tailWord_302578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302578).length < 2 ^ (prefixWord ++ tailWord_302578).sum := by decide
  have hdescent : baseEnd_302578 < baseStart_302578 := by decide
  rcases family_descends (prefixWord ++ tailWord_302578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302589 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_302589 : Nat := 118140960795 + 302589 * 2 ^ 59
def prefixEnd_302589 : Nat := 4983230072969 + 3 ^ 40 * 302589 * 2
def baseEnd_302589 : Nat := 103582398508947901897283

theorem tailTrace_302589 : CollatzResearch.WordTrace tailWord_302589 prefixEnd_302589 103582398508947901897283 := by
  unfold tailWord_302589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036327500779205932006821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7357551667186137288004547 11036327500779205932006821)
  ·
    refine ⟨2069311406396101112251279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11036327500779205932006821 2069311406396101112251279)
    ·
      refine ⟨3103967109594151668376919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069311406396101112251279 3103967109594151668376919)
      ·
        refine ⟨4655950664391227502565379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103967109594151668376919 4655950664391227502565379)
        ·
          refine ⟨6983925996586841253848069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655950664391227502565379 6983925996586841253848069)
          ·
            refine ⟨1309486124360032735096513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6983925996586841253848069 1309486124360032735096513)
            ·
              refine ⟨982114593270024551322385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309486124360032735096513 982114593270024551322385)
              ·
                refine ⟨736585944952518413491789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982114593270024551322385 736585944952518413491789)
                ·
                  refine ⟨276219729357194405059421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736585944952518413491789 276219729357194405059421)
                  ·
                    refine ⟨103582398508947901897283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276219729357194405059421 103582398508947901897283)
                    ·
                      rfl

theorem cell22_302589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_302589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302589 prefixEnd_302589 := by exact prefixLift 302589
  have htrace : WordTrace (prefixWord ++ tailWord_302589) baseStart_302589 baseEnd_302589 := by
    simpa [prefixWord, tailWord_302589, baseEnd_302589] using wordTrace_append hprefix tailTrace_302589
  have hstable : (prefixWord ++ tailWord_302589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302589).length < 2 ^ (prefixWord ++ tailWord_302589).sum := by decide
  have hdescent : baseEnd_302589 < baseStart_302589 := by decide
  rcases family_descends (prefixWord ++ tailWord_302589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302602 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_302602 : Nat := 118140960795 + 302602 * 2 ^ 59
def prefixEnd_302602 : Nat := 4983230072969 + 3 ^ 40 * 302602 * 2
def baseEnd_302602 : Nat := 34528949558206733774081

theorem tailTrace_302602 : CollatzResearch.WordTrace tailWord_302602 prefixEnd_302602 34528949558206733774081 := by
  unfold tailWord_302602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759200412433027288057515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7357867766488072768153373 2759200412433027288057515)
  ·
    refine ⟨4138800618649540932086273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759200412433027288057515 4138800618649540932086273)
    ·
      refine ⟨3104100463987155699064705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4138800618649540932086273 3104100463987155699064705)
      ·
        refine ⟨2328075347990366774298529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104100463987155699064705 2328075347990366774298529)
        ·
          refine ⟨1746056510992775080723897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328075347990366774298529 1746056510992775080723897)
          ·
            refine ⟨1309542383244581310542923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746056510992775080723897 1309542383244581310542923)
            ·
              refine ⟨1964313574866871965814385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309542383244581310542923 1964313574866871965814385)
              ·
                refine ⟨1473235181150153974360789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964313574866871965814385 1473235181150153974360789)
                ·
                  refine ⟨34528949558206733774081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1473235181150153974360789 34528949558206733774081)
                  ·
                    rfl

theorem cell22_302602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_302602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302602 prefixEnd_302602 := by exact prefixLift 302602
  have htrace : WordTrace (prefixWord ++ tailWord_302602) baseStart_302602 baseEnd_302602 := by
    simpa [prefixWord, tailWord_302602, baseEnd_302602] using wordTrace_append hprefix tailTrace_302602
  have hstable : (prefixWord ++ tailWord_302602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302602).length < 2 ^ (prefixWord ++ tailWord_302602).sum := by decide
  have hdescent : baseEnd_302602 < baseStart_302602 := by decide
  rcases family_descends (prefixWord ++ tailWord_302602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302649 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_302649 : Nat := 118140960795 + 302649 * 2 ^ 59
def prefixEnd_302649 : Nat := 4983230072969 + 3 ^ 40 * 302649 * 2
def baseEnd_302649 : Nat := 103602937735127745397099

theorem tailTrace_302649 : CollatzResearch.WordTrace tailWord_302649 prefixEnd_302649 103602937735127745397099 := by
  unfold tailWord_302649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038515880561836179191001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359010587041224119460667 11038515880561836179191001)
  ·
    refine ⟨8278886910421377134393251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11038515880561836179191001 8278886910421377134393251)
    ·
      refine ⟨12418330365632065701589877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8278886910421377134393251 12418330365632065701589877)
      ·
        refine ⟨1164218471778006159524051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12418330365632065701589877 1164218471778006159524051)
        ·
          refine ⟨1746327707667009239286077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164218471778006159524051 1746327707667009239286077)
          ·
            refine ⟨654872890375128464732279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1746327707667009239286077 654872890375128464732279)
            ·
              refine ⟨982309335562692697098419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654872890375128464732279 982309335562692697098419)
              ·
                refine ⟨1473464003344039045647629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982309335562692697098419 1473464003344039045647629)
                ·
                  refine ⟨552549001254014642117861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1473464003344039045647629 552549001254014642117861)
                  ·
                    refine ⟨103602937735127745397099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552549001254014642117861 103602937735127745397099)
                    ·
                      rfl

theorem cell22_302649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_302649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302649 prefixEnd_302649 := by exact prefixLift 302649
  have htrace : WordTrace (prefixWord ++ tailWord_302649) baseStart_302649 baseEnd_302649 := by
    simpa [prefixWord, tailWord_302649, baseEnd_302649] using wordTrace_append hprefix tailTrace_302649
  have hstable : (prefixWord ++ tailWord_302649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302649).length < 2 ^ (prefixWord ++ tailWord_302649).sum := by decide
  have hdescent : baseEnd_302649 < baseStart_302649 := by decide
  rcases family_descends (prefixWord ++ tailWord_302649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302666 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_302666 : Nat := 118140960795 + 302666 * 2 ^ 59
def prefixEnd_302666 : Nat := 4983230072969 + 3 ^ 40 * 302666 * 2
def baseEnd_302666 : Nat := 103608757182545367722047

theorem tailTrace_302666 : CollatzResearch.WordTrace tailWord_302666 prefixEnd_302666 103608757182545367722047 := by
  unfold tailWord_302666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759783980375062020639963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7359423947666832055039901 2759783980375062020639963)
  ·
    refine ⟨4139675970562593030959945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759783980375062020639963 4139675970562593030959945)
    ·
      refine ⟨3104756977921944773219959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139675970562593030959945 3104756977921944773219959)
      ·
        refine ⟨4657135466882917159829939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104756977921944773219959 4657135466882917159829939)
        ·
          refine ⟨6985703200324375739744909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657135466882917159829939 6985703200324375739744909)
          ·
            refine ⟨2619638700121640902404341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6985703200324375739744909 2619638700121640902404341)
            ·
              refine ⟨245591128136403834600407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2619638700121640902404341 245591128136403834600407)
              ·
                refine ⟨368386692204605751900611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245591128136403834600407 368386692204605751900611)
                ·
                  refine ⟨552580038306908627850917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368386692204605751900611 552580038306908627850917)
                  ·
                    refine ⟨103608757182545367722047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 552580038306908627850917 103608757182545367722047)
                    ·
                      rfl

theorem cell22_302666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_302666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302666 prefixEnd_302666 := by exact prefixLift 302666
  have htrace : WordTrace (prefixWord ++ tailWord_302666) baseStart_302666 baseEnd_302666 := by
    simpa [prefixWord, tailWord_302666, baseEnd_302666] using wordTrace_append hprefix tailTrace_302666
  have hstable : (prefixWord ++ tailWord_302666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302666).length < 2 ^ (prefixWord ++ tailWord_302666).sum := by decide
  have hdescent : baseEnd_302666 < baseStart_302666 := by decide
  rcases family_descends (prefixWord ++ tailWord_302666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302677 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_302677 : Nat := 118140960795 + 302677 * 2 ^ 59
def prefixEnd_302677 : Nat := 4983230072969 + 3 ^ 40 * 302677 * 2
def baseEnd_302677 : Nat := 103612522707345005697013

theorem tailTrace_302677 : CollatzResearch.WordTrace tailWord_302677 prefixEnd_302677 103612522707345005697013 := by
  unfold tailWord_302677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039537124460396961210285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359691416306931307473523 11039537124460396961210285)
  ·
    refine ⟨4139826421672648860453857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11039537124460396961210285 4139826421672648860453857)
    ·
      refine ⟨3104869816254486645340393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139826421672648860453857 3104869816254486645340393)
      ·
        refine ⟨2328652362190864984005295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104869816254486645340393 2328652362190864984005295)
        ·
          refine ⟨3492978543286297476007943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328652362190864984005295 3492978543286297476007943)
          ·
            refine ⟨5239467814929446214011915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492978543286297476007943 5239467814929446214011915)
            ·
              refine ⟨7859201722394169321017873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239467814929446214011915 7859201722394169321017873)
              ·
                refine ⟨5894401291795626990763405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7859201722394169321017873 5894401291795626990763405)
                ·
                  refine ⟨2210400484423360121536277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5894401291795626990763405 2210400484423360121536277)
                  ·
                    refine ⟨103612522707345005697013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2210400484423360121536277 103612522707345005697013)
                    ·
                      rfl

theorem cell22_302677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_302677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302677 prefixEnd_302677 := by exact prefixLift 302677
  have htrace : WordTrace (prefixWord ++ tailWord_302677) baseStart_302677 baseEnd_302677 := by
    simpa [prefixWord, tailWord_302677, baseEnd_302677] using wordTrace_append hprefix tailTrace_302677
  have hstable : (prefixWord ++ tailWord_302677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302677).length < 2 ^ (prefixWord ++ tailWord_302677).sum := by decide
  have hdescent : baseEnd_302677 < baseStart_302677 := by decide
  rcases family_descends (prefixWord ++ tailWord_302677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302696 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_302696 : Nat := 118140960795 + 302696 * 2 ^ 59
def prefixEnd_302696 : Nat := 4983230072969 + 3 ^ 40 * 302696 * 2
def baseEnd_302696 : Nat := 103619026795635289471955

theorem tailTrace_302696 : CollatzResearch.WordTrace tailWord_302696 prefixEnd_302696 103619026795635289471955 := by
  unfold tailWord_302696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520115055695781603075971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7360153407594375470767961 5520115055695781603075971)
  ·
    refine ⟨8280172583543672404613957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520115055695781603075971 8280172583543672404613957)
    ·
      refine ⟨1552532359414438575865117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8280172583543672404613957 1552532359414438575865117)
      ·
        refine ⟨582199634780414465949419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1552532359414438575865117 582199634780414465949419)
        ·
          refine ⟨873299452170621698924129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582199634780414465949419 873299452170621698924129)
          ·
            refine ⟨654974589127966274193097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873299452170621698924129 654974589127966274193097)
            ·
              refine ⟨491230941845974705644823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654974589127966274193097 491230941845974705644823)
              ·
                refine ⟨736846412768962058467235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491230941845974705644823 736846412768962058467235)
                ·
                  refine ⟨1105269619153443087700853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736846412768962058467235 1105269619153443087700853)
                  ·
                    refine ⟨103619026795635289471955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1105269619153443087700853 103619026795635289471955)
                    ·
                      rfl

theorem cell22_302696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_302696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302696 prefixEnd_302696 := by exact prefixLift 302696
  have htrace : WordTrace (prefixWord ++ tailWord_302696) baseStart_302696 baseEnd_302696 := by
    simpa [prefixWord, tailWord_302696, baseEnd_302696] using wordTrace_append hprefix tailTrace_302696
  have hstable : (prefixWord ++ tailWord_302696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302696).length < 2 ^ (prefixWord ++ tailWord_302696).sum := by decide
  have hdescent : baseEnd_302696 < baseStart_302696 := by decide
  rcases family_descends (prefixWord ++ tailWord_302696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302775 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 1, 3]
def baseStart_302775 : Nat := 118140960795 + 302775 * 2 ^ 59
def prefixEnd_302775 : Nat := 4983230072969 + 3 ^ 40 * 302775 * 2
def baseEnd_302775 : Nat := 103646070110105416746713

theorem tailTrace_302775 : CollatzResearch.WordTrace tailWord_302775 prefixEnd_302775 103646070110105416746713 := by
  unfold tailWord_302775
  simp only [CollatzResearch.WordTrace]
  refine ⟨11043111478105359698277779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7362074318736906465518519 11043111478105359698277779)
  ·
    refine ⟨16564667217158039547416669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11043111478105359698277779 16564667217158039547416669)
    ·
      refine ⟨6211750206434264830281251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16564667217158039547416669 6211750206434264830281251)
      ·
        refine ⟨9317625309651397245421877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211750206434264830281251 9317625309651397245421877)
        ·
          refine ⟨873527372779818491758301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9317625309651397245421877 873527372779818491758301)
          ·
            refine ⟨327572764792431934409363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 873527372779818491758301 327572764792431934409363)
            ·
              refine ⟨491359147188647901614045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327572764792431934409363 491359147188647901614045)
              ·
                refine ⟨184259680195742963105267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491359147188647901614045 184259680195742963105267)
                ·
                  refine ⟨276389520293614444657901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184259680195742963105267 276389520293614444657901)
                  ·
                    refine ⟨103646070110105416746713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276389520293614444657901 103646070110105416746713)
                    ·
                      rfl

theorem cell22_302775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_302775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302775 prefixEnd_302775 := by exact prefixLift 302775
  have htrace : WordTrace (prefixWord ++ tailWord_302775) baseStart_302775 baseEnd_302775 := by
    simpa [prefixWord, tailWord_302775, baseEnd_302775] using wordTrace_append hprefix tailTrace_302775
  have hstable : (prefixWord ++ tailWord_302775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302775).length < 2 ^ (prefixWord ++ tailWord_302775).sum := by decide
  have hdescent : baseEnd_302775 < baseStart_302775 := by decide
  rcases family_descends (prefixWord ++ tailWord_302775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302854 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_302854 : Nat := 118140960795 + 302854 * 2 ^ 59
def prefixEnd_302854 : Nat := 4983230072969 + 3 ^ 40 * 302854 * 2
def baseEnd_302854 : Nat := 103673113424575544021471

theorem tailTrace_302854 : CollatzResearch.WordTrace tailWord_302854 prefixEnd_302854 103673113424575544021471 := by
  unfold tailWord_302854
  simp only [CollatzResearch.WordTrace]
  refine ⟨345187276400598630950113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7363995229879437460269077 345187276400598630950113)
  ·
    refine ⟨258890457300448973212585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345187276400598630950113 258890457300448973212585)
    ·
      refine ⟨194167842975336729909439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258890457300448973212585 194167842975336729909439)
      ·
        refine ⟨291251764463005094864159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194167842975336729909439 291251764463005094864159)
        ·
          refine ⟨436877646694507642296239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291251764463005094864159 436877646694507642296239)
          ·
            refine ⟨655316470041761463444359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436877646694507642296239 655316470041761463444359)
            ·
              refine ⟨982974705062642195166539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655316470041761463444359 982974705062642195166539)
              ·
                refine ⟨1474462057593963292749809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982974705062642195166539 1474462057593963292749809)
                ·
                  refine ⟨1105846543195472469562357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474462057593963292749809 1105846543195472469562357)
                  ·
                    refine ⟨103673113424575544021471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1105846543195472469562357 103673113424575544021471)
                    ·
                      rfl

theorem cell22_302854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_302854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302854 prefixEnd_302854 := by exact prefixLift 302854
  have htrace : WordTrace (prefixWord ++ tailWord_302854) baseStart_302854 baseEnd_302854 := by
    simpa [prefixWord, tailWord_302854, baseEnd_302854] using wordTrace_append hprefix tailTrace_302854
  have hstable : (prefixWord ++ tailWord_302854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302854).length < 2 ^ (prefixWord ++ tailWord_302854).sum := by decide
  have hdescent : baseEnd_302854 < baseStart_302854 := by decide
  rcases family_descends (prefixWord ++ tailWord_302854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302906 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_302906 : Nat := 118140960795 + 302906 * 2 ^ 59
def prefixEnd_302906 : Nat := 4983230072969 + 3 ^ 40 * 302906 * 2
def baseEnd_302906 : Nat := 34563638029088247240437

theorem tailTrace_302906 : CollatzResearch.WordTrace tailWord_302906 prefixEnd_302906 34563638029088247240437 := by
  unfold tailWord_302906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761972360157692267824143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7365259627087179380864381 2761972360157692267824143)
  ·
    refine ⟨4142958540236538401736215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761972360157692267824143 4142958540236538401736215)
    ·
      refine ⟨6214437810354807602604323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142958540236538401736215 6214437810354807602604323)
      ·
        refine ⟨9321656715532211403906485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214437810354807602604323 9321656715532211403906485)
        ·
          refine ⟨873905317081144819116233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9321656715532211403906485 873905317081144819116233)
          ·
            refine ⟨655428987810858614337175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873905317081144819116233 655428987810858614337175)
            ·
              refine ⟨983143481716287921505763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655428987810858614337175 983143481716287921505763)
              ·
                refine ⟨1474715222574431882258645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983143481716287921505763 1474715222574431882258645)
                ·
                  refine ⟨34563638029088247240437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1474715222574431882258645 34563638029088247240437)
                  ·
                    rfl

theorem cell22_302906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_302906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302906 prefixEnd_302906 := by exact prefixLift 302906
  have htrace : WordTrace (prefixWord ++ tailWord_302906) baseStart_302906 baseEnd_302906 := by
    simpa [prefixWord, tailWord_302906, baseEnd_302906] using wordTrace_append hprefix tailTrace_302906
  have hstable : (prefixWord ++ tailWord_302906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302906).length < 2 ^ (prefixWord ++ tailWord_302906).sum := by decide
  have hdescent : baseEnd_302906 < baseStart_302906 := by decide
  rcases family_descends (prefixWord ++ tailWord_302906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302910 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_302910 : Nat := 118140960795 + 302910 * 2 ^ 59
def prefixEnd_302910 : Nat := 4983230072969 + 3 ^ 40 * 302910 * 2
def baseEnd_302910 : Nat := 103692283369010064621299

theorem tailTrace_302910 : CollatzResearch.WordTrace tailWord_302910 prefixEnd_302910 103692283369010064621299 := by
  unfold tailWord_302910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381004416577034719305273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7365356888410851836294789 1381004416577034719305273)
  ·
    refine ⟨1035753312432776039478955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1381004416577034719305273 1035753312432776039478955)
    ·
      refine ⟨1553629968649164059218433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035753312432776039478955 1553629968649164059218433)
      ·
        refine ⟨1165222476486873044413825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1553629968649164059218433 1165222476486873044413825)
        ·
          refine ⟨873916857365154783310369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165222476486873044413825 873916857365154783310369)
          ·
            refine ⟨655437643023866087482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873916857365154783310369 655437643023866087482777)
            ·
              refine ⟨491578232267899565612083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655437643023866087482777 491578232267899565612083)
              ·
                refine ⟨737367348401849348418125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491578232267899565612083 737367348401849348418125)
                ·
                  refine ⟨276512755650693505656797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737367348401849348418125 276512755650693505656797)
                  ·
                    refine ⟨103692283369010064621299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276512755650693505656797 103692283369010064621299)
                    ·
                      rfl

theorem cell22_302910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_302910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302910 prefixEnd_302910 := by exact prefixLift 302910
  have htrace : WordTrace (prefixWord ++ tailWord_302910) baseStart_302910 baseEnd_302910 := by
    simpa [prefixWord, tailWord_302910, baseEnd_302910] using wordTrace_append hprefix tailTrace_302910
  have hstable : (prefixWord ++ tailWord_302910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302910).length < 2 ^ (prefixWord ++ tailWord_302910).sum := by decide
  have hdescent : baseEnd_302910 < baseStart_302910 := by decide
  rcases family_descends (prefixWord ++ tailWord_302910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302981 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_302981 : Nat := 118140960795 + 302981 * 2 ^ 59
def prefixEnd_302981 : Nat := 4983230072969 + 3 ^ 40 * 302981 * 2
def baseEnd_302981 : Nat := 103716588119989546096081

theorem tailTrace_302981 : CollatzResearch.WordTrace tailWord_302981 prefixEnd_302981 103716588119989546096081 := by
  unfold tailWord_302981
  simp only [CollatzResearch.WordTrace]
  refine ⟨11050624915359056880276797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7367083276906037920184531 11050624915359056880276797)
  ·
    refine ⟨4143984343259646330103799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11050624915359056880276797 4143984343259646330103799)
    ·
      refine ⟨6215976514889469495155699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143984343259646330103799 6215976514889469495155699)
      ·
        refine ⟨9323964772334204242733549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215976514889469495155699 9323964772334204242733549)
        ·
          refine ⟨3496486789625326591025081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9323964772334204242733549 3496486789625326591025081)
          ·
            refine ⟨2622365092218994943268811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3496486789625326591025081 2622365092218994943268811)
            ·
              refine ⟨3933547638328492414903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622365092218994943268811 3933547638328492414903217)
              ·
                refine ⟨2950160728746369311177413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933547638328492414903217 2950160728746369311177413)
                ·
                  refine ⟨553155136639944245845765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2950160728746369311177413 553155136639944245845765)
                  ·
                    refine ⟨103716588119989546096081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553155136639944245845765 103716588119989546096081)
                    ·
                      rfl

theorem cell22_302981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_302981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_302981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_302981 prefixEnd_302981 := by exact prefixLift 302981
  have htrace : WordTrace (prefixWord ++ tailWord_302981) baseStart_302981 baseEnd_302981 := by
    simpa [prefixWord, tailWord_302981, baseEnd_302981] using wordTrace_append hprefix tailTrace_302981
  have hstable : (prefixWord ++ tailWord_302981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302981).length < 2 ^ (prefixWord ++ tailWord_302981).sum := by decide
  have hdescent : baseEnd_302981 < baseStart_302981 := by decide
  rcases family_descends (prefixWord ++ tailWord_302981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303000 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_303000 : Nat := 118140960795 + 303000 * 2 ^ 59
def prefixEnd_303000 : Nat := 4983230072969 + 3 ^ 40 * 303000 * 2
def baseEnd_303000 : Nat := 103723092208279829871023

theorem tailTrace_303000 : CollatzResearch.WordTrace tailWord_303000 prefixEnd_303000 103723092208279829871023 := by
  unfold tailWord_303000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525658951145111562609227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7367545268193482083478969 5525658951145111562609227)
  ·
    refine ⟨8288488426717667343913841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5525658951145111562609227 8288488426717667343913841)
    ·
      refine ⟨6216366320038250507935381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288488426717667343913841 6216366320038250507935381)
      ·
        refine ⟨291392171251792992559471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6216366320038250507935381 291392171251792992559471)
        ·
          refine ⟨437088256877689488839207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291392171251792992559471 437088256877689488839207)
          ·
            refine ⟨655632385316534233258811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437088256877689488839207 655632385316534233258811)
            ·
              refine ⟨983448577974801349888217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655632385316534233258811 983448577974801349888217)
              ·
                refine ⟨737586433481101012416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983448577974801349888217 737586433481101012416163)
                ·
                  refine ⟨1106379650221651518624245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737586433481101012416163 1106379650221651518624245)
                  ·
                    refine ⟨103723092208279829871023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1106379650221651518624245 103723092208279829871023)
                    ·
                      rfl

theorem cell22_303000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_303000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303000 prefixEnd_303000 := by exact prefixLift 303000
  have htrace : WordTrace (prefixWord ++ tailWord_303000) baseStart_303000 baseEnd_303000 := by
    simpa [prefixWord, tailWord_303000, baseEnd_303000] using wordTrace_append hprefix tailTrace_303000
  have hstable : (prefixWord ++ tailWord_303000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303000).length < 2 ^ (prefixWord ++ tailWord_303000).sum := by decide
  have hdescent : baseEnd_303000 < baseStart_303000 := by decide
  rcases family_descends (prefixWord ++ tailWord_303000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303068 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_303068 : Nat := 118140960795 + 303068 * 2 ^ 59
def prefixEnd_303068 : Nat := 4983230072969 + 3 ^ 40 * 303068 * 2
def baseEnd_303068 : Nat := 103746369997950319170815

theorem tailTrace_303068 : CollatzResearch.WordTrace tailWord_303068 prefixEnd_303068 103746369997950319170815 := by
  unfold tailWord_303068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526899033021935369346929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7369198710695913825795905 5526899033021935369346929)
  ·
    refine ⟨4145174274766451527010197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5526899033021935369346929 4145174274766451527010197)
    ·
      refine ⟨194305044129677415328603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4145174274766451527010197 194305044129677415328603)
      ·
        refine ⟨291457566194516122992905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194305044129677415328603 291457566194516122992905)
        ·
          refine ⟨218593174645887092244679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291457566194516122992905 218593174645887092244679)
          ·
            refine ⟨327889761968830638367019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218593174645887092244679 327889761968830638367019)
            ·
              refine ⟨491834642953245957550529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327889761968830638367019 491834642953245957550529)
              ·
                refine ⟨368875982214934468162897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491834642953245957550529 368875982214934468162897)
                ·
                  refine ⟨276656986661200851122173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368875982214934468162897 276656986661200851122173)
                  ·
                    refine ⟨103746369997950319170815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276656986661200851122173 103746369997950319170815)
                    ·
                      rfl

theorem cell22_303068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_303068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303068 prefixEnd_303068 := by exact prefixLift 303068
  have htrace : WordTrace (prefixWord ++ tailWord_303068) baseStart_303068 baseEnd_303068 := by
    simpa [prefixWord, tailWord_303068, baseEnd_303068] using wordTrace_append hprefix tailTrace_303068
  have hstable : (prefixWord ++ tailWord_303068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303068).length < 2 ^ (prefixWord ++ tailWord_303068).sum := by decide
  have hdescent : baseEnd_303068 < baseStart_303068 := by decide
  rcases family_descends (prefixWord ++ tailWord_303068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303075 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 5]
def baseStart_303075 : Nat := 118140960795 + 303075 * 2 ^ 59
def prefixEnd_303075 : Nat := 4983230072969 + 3 ^ 40 * 303075 * 2
def baseEnd_303075 : Nat := 34582922080334878081931

theorem tailTrace_303075 : CollatzResearch.WordTrace tailWord_303075 prefixEnd_303075 34582922080334878081931 := by
  unfold tailWord_303075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054053377018510934198679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7369368918012340622799119 11054053377018510934198679)
  ·
    refine ⟨16581080065527766401298019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11054053377018510934198679 16581080065527766401298019)
    ·
      refine ⟨24871620098291649601947029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16581080065527766401298019 24871620098291649601947029)
      ·
        refine ⟨1165857192107421075091267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24871620098291649601947029 1165857192107421075091267)
        ·
          refine ⟨1748785788161131612636901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165857192107421075091267 1748785788161131612636901)
          ·
            refine ⟨327897335280212177369419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1748785788161131612636901 327897335280212177369419)
            ·
              refine ⟨491846002920318266054129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327897335280212177369419 491846002920318266054129)
              ·
                refine ⟨368884502190238699540597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491846002920318266054129 368884502190238699540597)
                ·
                  refine ⟨34582922080334878081931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368884502190238699540597 34582922080334878081931)
                  ·
                    rfl

theorem cell22_303075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].length) (baseStart_303075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303075 prefixEnd_303075 := by exact prefixLift 303075
  have htrace : WordTrace (prefixWord ++ tailWord_303075) baseStart_303075 baseEnd_303075 := by
    simpa [prefixWord, tailWord_303075, baseEnd_303075] using wordTrace_append hprefix tailTrace_303075
  have hstable : (prefixWord ++ tailWord_303075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303075).length < 2 ^ (prefixWord ++ tailWord_303075).sum := by decide
  have hdescent : baseEnd_303075 < baseStart_303075 := by decide
  rcases family_descends (prefixWord ++ tailWord_303075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303105 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_303105 : Nat := 118140960795 + 303105 * 2 ^ 59
def prefixEnd_303105 : Nat := 4983230072969 + 3 ^ 40 * 303105 * 2
def baseEnd_303105 : Nat := 103759035854094555995701

theorem tailTrace_303105 : CollatzResearch.WordTrace tailWord_303105 prefixEnd_303105 103759035854094555995701 := by
  unfold tailWord_303105
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055147566909826057790769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370098377939884038527179 11055147566909826057790769)
  ·
    refine ⟨8291360675182369543343077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11055147566909826057790769 8291360675182369543343077)
    ·
      refine ⟨1554630126596694289376827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8291360675182369543343077 1554630126596694289376827)
      ·
        refine ⟨2331945189895041434065241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554630126596694289376827 2331945189895041434065241)
        ·
          refine ⟨1748958892421281075548931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2331945189895041434065241 1748958892421281075548931)
          ·
            refine ⟨2623438338631921613323397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748958892421281075548931 2623438338631921613323397)
            ·
              refine ⟨491894688493485302498137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2623438338631921613323397 491894688493485302498137)
              ·
                refine ⟨368921016370113976873603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491894688493485302498137 368921016370113976873603)
                ·
                  refine ⟨553381524555170965310405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368921016370113976873603 553381524555170965310405)
                  ·
                    refine ⟨103759035854094555995701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553381524555170965310405 103759035854094555995701)
                    ·
                      rfl

theorem cell22_303105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_303105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303105 prefixEnd_303105 := by exact prefixLift 303105
  have htrace : WordTrace (prefixWord ++ tailWord_303105) baseStart_303105 baseEnd_303105 := by
    simpa [prefixWord, tailWord_303105, baseEnd_303105] using wordTrace_append hprefix tailTrace_303105
  have hstable : (prefixWord ++ tailWord_303105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303105).length < 2 ^ (prefixWord ++ tailWord_303105).sum := by decide
  have hdescent : baseEnd_303105 < baseStart_303105 := by decide
  rcases family_descends (prefixWord ++ tailWord_303105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303118 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_303118 : Nat := 118140960795 + 303118 * 2 ^ 59
def prefixEnd_303118 : Nat := 4983230072969 + 3 ^ 40 * 303118 * 2
def baseEnd_303118 : Nat := 103763486019766855420661

theorem tailTrace_303118 : CollatzResearch.WordTrace tailWord_303118 prefixEnd_303118 103763486019766855420661 := by
  unfold tailWord_303118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381952714482841159751751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7370414477241819518676005 1381952714482841159751751)
  ·
    refine ⟨2072929071724261739627627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1381952714482841159751751 2072929071724261739627627)
    ·
      refine ⟨3109393607586392609441441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072929071724261739627627 3109393607586392609441441)
      ·
        refine ⟨2332045205689794457081081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109393607586392609441441 2332045205689794457081081)
        ·
          refine ⟨1749033904267345842810811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332045205689794457081081 1749033904267345842810811)
          ·
            refine ⟨2623550856401018764216217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749033904267345842810811 2623550856401018764216217)
            ·
              refine ⟨1967663142300764073162163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623550856401018764216217 1967663142300764073162163)
              ·
                refine ⟨2951494713451146109743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967663142300764073162163 2951494713451146109743245)
                ·
                  refine ⟨1106810517544179791153717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2951494713451146109743245 1106810517544179791153717)
                  ·
                    refine ⟨103763486019766855420661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1106810517544179791153717 103763486019766855420661)
                    ·
                      rfl

theorem cell22_303118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_303118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303118 prefixEnd_303118 := by exact prefixLift 303118
  have htrace : WordTrace (prefixWord ++ tailWord_303118) baseStart_303118 baseEnd_303118 := by
    simpa [prefixWord, tailWord_303118, baseEnd_303118] using wordTrace_append hprefix tailTrace_303118
  have hstable : (prefixWord ++ tailWord_303118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303118).length < 2 ^ (prefixWord ++ tailWord_303118).sum := by decide
  have hdescent : baseEnd_303118 < baseStart_303118 := by decide
  rcases family_descends (prefixWord ++ tailWord_303118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303135 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 2, 3]
def baseStart_303135 : Nat := 118140960795 + 303135 * 2 ^ 59
def prefixEnd_303135 : Nat := 4983230072969 + 3 ^ 40 * 303135 * 2
def baseEnd_303135 : Nat := 103769305467184477745609

theorem tailTrace_303135 : CollatzResearch.WordTrace tailWord_303135 prefixEnd_303135 103769305467184477745609 := by
  unfold tailWord_303135
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056241756801141181382859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370827837867427454255239 11056241756801141181382859)
  ·
    refine ⟨16584362635201711772074289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11056241756801141181382859 16584362635201711772074289)
    ·
      refine ⟨12438271976401283829055717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16584362635201711772074289 12438271976401283829055717)
      ·
        refine ⟨2332175995575240717947947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12438271976401283829055717 2332175995575240717947947)
        ·
          refine ⟨3498263993362861076921921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332175995575240717947947 3498263993362861076921921)
          ·
            refine ⟨2623697995022145807691441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3498263993362861076921921 2623697995022145807691441)
            ·
              refine ⟨1967773496266609355768581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623697995022145807691441 1967773496266609355768581)
              ·
                refine ⟨368957530549989254206609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1967773496266609355768581 368957530549989254206609)
                ·
                  refine ⟨276718147912491940654957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368957530549989254206609 276718147912491940654957)
                  ·
                    refine ⟨103769305467184477745609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276718147912491940654957 103769305467184477745609)
                    ·
                      rfl

theorem cell22_303135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_303135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303135 prefixEnd_303135 := by exact prefixLift 303135
  have htrace : WordTrace (prefixWord ++ tailWord_303135) baseStart_303135 baseEnd_303135 := by
    simpa [prefixWord, tailWord_303135, baseEnd_303135] using wordTrace_append hprefix tailTrace_303135
  have hstable : (prefixWord ++ tailWord_303135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303135).length < 2 ^ (prefixWord ++ tailWord_303135).sum := by decide
  have hdescent : baseEnd_303135 < baseStart_303135 := by decide
  rcases family_descends (prefixWord ++ tailWord_303135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303137 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 6]
def baseStart_303137 : Nat := 118140960795 + 303137 * 2 ^ 59
def prefixEnd_303137 : Nat := 4983230072969 + 3 ^ 40 * 303137 * 2
def baseEnd_303137 : Nat := 34589996702685713065201

theorem tailTrace_303137 : CollatzResearch.WordTrace tailWord_303137 prefixEnd_303137 34589996702685713065201 := by
  unfold tailWord_303137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056314702793895522955665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370876468529263681970443 11056314702793895522955665)
  ·
    refine ⟨8292236027095421642216749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11056314702793895522955665 8292236027095421642216749)
    ·
      refine ⟨3109588510160783115831281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8292236027095421642216749 3109588510160783115831281)
      ·
        refine ⟨2332191382620587336873461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3109588510160783115831281 2332191382620587336873461)
        ·
          refine ⟨218642942120680062831887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2332191382620587336873461 218642942120680062831887)
          ·
            refine ⟨327964413181020094247831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218642942120680062831887 327964413181020094247831)
            ·
              refine ⟨491946619771530141371747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327964413181020094247831 491946619771530141371747)
              ·
                refine ⟨737919929657295212057621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491946619771530141371747 737919929657295212057621)
                ·
                  refine ⟨34589996702685713065201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 737919929657295212057621 34589996702685713065201)
                  ·
                    rfl

theorem cell22_303137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_303137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303137 prefixEnd_303137 := by exact prefixLift 303137
  have htrace : WordTrace (prefixWord ++ tailWord_303137) baseStart_303137 baseEnd_303137 := by
    simpa [prefixWord, tailWord_303137, baseEnd_303137] using wordTrace_append hprefix tailTrace_303137
  have hstable : (prefixWord ++ tailWord_303137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303137).length < 2 ^ (prefixWord ++ tailWord_303137).sum := by decide
  have hdescent : baseEnd_303137 < baseStart_303137 := by decide
  rcases family_descends (prefixWord ++ tailWord_303137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303152 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_303152 : Nat := 118140960795 + 303152 * 2 ^ 59
def prefixEnd_303152 : Nat := 4983230072969 + 3 ^ 40 * 303152 * 2
def baseEnd_303152 : Nat := 103775124914602100070557

theorem tailTrace_303152 : CollatzResearch.WordTrace tailWord_303152 prefixEnd_303152 103775124914602100070557 := by
  unfold tailWord_303152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528430898869776542375855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7371241198493035389834473 5528430898869776542375855)
  ·
    refine ⟨8292646348304664813563783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528430898869776542375855 8292646348304664813563783)
    ·
      refine ⟨12438969522456997220345675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292646348304664813563783 12438969522456997220345675)
      ·
        refine ⟨18658454283685495830518513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12438969522456997220345675 18658454283685495830518513)
        ·
          refine ⟨13993840712764121872888885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18658454283685495830518513 13993840712764121872888885)
          ·
            refine ⟨1311922566821636425583333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13993840712764121872888885 1311922566821636425583333)
            ·
              refine ⟨245985481279056829796875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1311922566821636425583333 245985481279056829796875)
              ·
                refine ⟨368978221918585244695313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245985481279056829796875 368978221918585244695313)
                ·
                  refine ⟨276733666438938933521485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368978221918585244695313 276733666438938933521485)
                  ·
                    refine ⟨103775124914602100070557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276733666438938933521485 103775124914602100070557)
                    ·
                      rfl

theorem cell22_303152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_303152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303152 prefixEnd_303152 := by exact prefixLift 303152
  have htrace : WordTrace (prefixWord ++ tailWord_303152) baseStart_303152 baseEnd_303152 := by
    simpa [prefixWord, tailWord_303152, baseEnd_303152] using wordTrace_append hprefix tailTrace_303152
  have hstable : (prefixWord ++ tailWord_303152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303152).length < 2 ^ (prefixWord ++ tailWord_303152).sum := by decide
  have hdescent : baseEnd_303152 < baseStart_303152 := by decide
  rcases family_descends (prefixWord ++ tailWord_303152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303156 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_303156 : Nat := 118140960795 + 303156 * 2 ^ 59
def prefixEnd_303156 : Nat := 4983230072969 + 3 ^ 40 * 303156 * 2
def baseEnd_303156 : Nat := 103776494196347422970545

theorem tailTrace_303156 : CollatzResearch.WordTrace tailWord_303156 prefixEnd_303156 103776494196347422970545 := by
  unfold tailWord_303156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528503844862530883948661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7371338459816707845264881 5528503844862530883948661)
  ·
    refine ⟨518297235455862270370187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5528503844862530883948661 518297235455862270370187)
    ·
      refine ⟨777445853183793405555281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 518297235455862270370187 777445853183793405555281)
      ·
        refine ⟨583084389887845054166461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777445853183793405555281 583084389887845054166461)
        ·
          refine ⟨218656646207941895312423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 583084389887845054166461 218656646207941895312423)
          ·
            refine ⟨327984969311912842968635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218656646207941895312423 327984969311912842968635)
            ·
              refine ⟨491977453967869264452953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327984969311912842968635 491977453967869264452953)
              ·
                refine ⟨368983090475901948339715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491977453967869264452953 368983090475901948339715)
                ·
                  refine ⟨553474635713852922509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368983090475901948339715 553474635713852922509573)
                  ·
                    refine ⟨103776494196347422970545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553474635713852922509573 103776494196347422970545)
                    ·
                      rfl

theorem cell22_303156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_303156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303156 prefixEnd_303156 := by exact prefixLift 303156
  have htrace : WordTrace (prefixWord ++ tailWord_303156) baseStart_303156 baseEnd_303156 := by
    simpa [prefixWord, tailWord_303156, baseEnd_303156] using wordTrace_append hprefix tailTrace_303156
  have hstable : (prefixWord ++ tailWord_303156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303156).length < 2 ^ (prefixWord ++ tailWord_303156).sum := by decide
  have hdescent : baseEnd_303156 < baseStart_303156 := by decide
  rcases family_descends (prefixWord ++ tailWord_303156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303300 : List Nat := [2, 3, 3, 1, 2, 1, 10]
def baseStart_303300 : Nat := 118140960795 + 303300 * 2 ^ 59
def prefixEnd_303300 : Nat := 4983230072969 + 3 ^ 40 * 303300 * 2
def baseEnd_303300 : Nat := 3845399568117742495189

theorem tailTrace_303300 : CollatzResearch.WordTrace tailWord_303300 prefixEnd_303300 3845399568117742495189 := by
  unfold tailWord_303300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531129900601687180569677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7374839867468916240759569 5531129900601687180569677)
  ·
    refine ⟨2074173712725632692713629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5531129900601687180569677 2074173712725632692713629)
    ·
      refine ⟨777815142272112259767611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2074173712725632692713629 777815142272112259767611)
      ·
        refine ⟨1166722713408168389651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777815142272112259767611 1166722713408168389651417)
        ·
          refine ⟨875042035056126292238563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166722713408168389651417 875042035056126292238563)
          ·
            refine ⟨1312563052584189438357845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875042035056126292238563 1312563052584189438357845)
            ·
              refine ⟨3845399568117742495189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1312563052584189438357845 3845399568117742495189)
              ·
                rfl

theorem cell22_303300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 10].length) (baseStart_303300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303300 prefixEnd_303300 := by exact prefixLift 303300
  have htrace : WordTrace (prefixWord ++ tailWord_303300) baseStart_303300 baseEnd_303300 := by
    simpa [prefixWord, tailWord_303300, baseEnd_303300] using wordTrace_append hprefix tailTrace_303300
  have hstable : (prefixWord ++ tailWord_303300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303300).length < 2 ^ (prefixWord ++ tailWord_303300).sum := by decide
  have hdescent : baseEnd_303300 < baseStart_303300 := by decide
  rcases family_descends (prefixWord ++ tailWord_303300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303317 : List Nat := [1, 3, 2, 4, 2, 1, 2, 7]
def baseStart_303317 : Nat := 118140960795 + 303317 * 2 ^ 59
def prefixEnd_303317 : Nat := 4983230072969 + 3 ^ 40 * 303317 * 2
def baseEnd_303317 : Nat := 11536845309621852188339

theorem tailTrace_303317 : CollatzResearch.WordTrace tailWord_303317 prefixEnd_303317 11536845309621852188339 := by
  unfold tailWord_303317
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062879842141786264508205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375253228094524176338803 11062879842141786264508205)
  ·
    refine ⟨4148579940803169849190577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11062879842141786264508205 4148579940803169849190577)
    ·
      refine ⟨3111434955602377386892933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4148579940803169849190577 3111434955602377386892933)
      ·
        refine ⟨583394054175445760042425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3111434955602377386892933 583394054175445760042425)
        ·
          refine ⟨437545540631584320031819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583394054175445760042425 437545540631584320031819)
          ·
            refine ⟨656318310947376480047729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437545540631584320031819 656318310947376480047729)
            ·
              refine ⟨492238733210532360035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 656318310947376480047729 492238733210532360035797)
              ·
                refine ⟨11536845309621852188339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 492238733210532360035797 11536845309621852188339)
                ·
                  rfl

theorem cell22_303317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 7].length) (baseStart_303317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303317 prefixEnd_303317 := by exact prefixLift 303317
  have htrace : WordTrace (prefixWord ++ tailWord_303317) baseStart_303317 baseEnd_303317 := by
    simpa [prefixWord, tailWord_303317, baseEnd_303317] using wordTrace_append hprefix tailTrace_303317
  have hstable : (prefixWord ++ tailWord_303317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303317).length < 2 ^ (prefixWord ++ tailWord_303317).sum := by decide
  have hdescent : baseEnd_303317 < baseStart_303317 := by decide
  rcases family_descends (prefixWord ++ tailWord_303317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303392 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_303392 : Nat := 118140960795 + 303392 * 2 ^ 59
def prefixEnd_303392 : Nat := 4983230072969 + 3 ^ 40 * 303392 * 2
def baseEnd_303392 : Nat := 103857281819321474069821

theorem tailTrace_303392 : CollatzResearch.WordTrace tailWord_303392 prefixEnd_303392 103857281819321474069821 := by
  unfold tailWord_303392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532807658435037036744215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7377076877913382715658953 5532807658435037036744215)
  ·
    refine ⟨8299211487652555555116323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532807658435037036744215 8299211487652555555116323)
    ·
      refine ⟨12448817231478833332674485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299211487652555555116323 12448817231478833332674485)
      ·
        refine ⟨1167076615451140624938233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12448817231478833332674485 1167076615451140624938233)
        ·
          refine ⟨875307461588355468703675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167076615451140624938233 875307461588355468703675)
          ·
            refine ⟨1312961192382533203055513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875307461588355468703675 1312961192382533203055513)
            ·
              refine ⟨984720894286899902291635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312961192382533203055513 984720894286899902291635)
              ·
                refine ⟨1477081341430349853437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984720894286899902291635 1477081341430349853437453)
                ·
                  refine ⟨553905503036381195039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1477081341430349853437453 553905503036381195039045)
                  ·
                    refine ⟨103857281819321474069821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553905503036381195039045 103857281819321474069821)
                    ·
                      rfl

theorem cell22_303392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_303392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303392 prefixEnd_303392 := by exact prefixLift 303392
  have htrace : WordTrace (prefixWord ++ tailWord_303392) baseStart_303392 baseEnd_303392 := by
    simpa [prefixWord, tailWord_303392, baseEnd_303392] using wordTrace_append hprefix tailTrace_303392
  have hstable : (prefixWord ++ tailWord_303392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303392).length < 2 ^ (prefixWord ++ tailWord_303392).sum := by decide
  have hdescent : baseEnd_303392 < baseStart_303392 := by decide
  rcases family_descends (prefixWord ++ tailWord_303392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303407 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 4]
def baseStart_303407 : Nat := 118140960795 + 303407 * 2 ^ 59
def prefixEnd_303407 : Nat := 4983230072969 + 3 ^ 40 * 303407 * 2
def baseEnd_303407 : Nat := 34620805541955478314925

theorem tailTrace_303407 : CollatzResearch.WordTrace tailWord_303407 prefixEnd_303407 34620805541955478314925 := by
  unfold tailWord_303407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066162411815731635284475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7377441607877154423522983 11066162411815731635284475)
  ·
    refine ⟨16599243617723597452926713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11066162411815731635284475 16599243617723597452926713)
    ·
      refine ⟨12449432713292698089695035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16599243617723597452926713 12449432713292698089695035)
      ·
        refine ⟨18674149069939047134542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12449432713292698089695035 18674149069939047134542553)
        ·
          refine ⟨14005611802454285350906915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18674149069939047134542553 14005611802454285350906915)
          ·
            refine ⟨21008417703681428026360373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14005611802454285350906915 21008417703681428026360373)
            ·
              refine ⟨1969539159720133877471285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21008417703681428026360373 1969539159720133877471285)
              ·
                refine ⟨184644296223762551012933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1969539159720133877471285 184644296223762551012933)
                ·
                  refine ⟨34620805541955478314925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184644296223762551012933 34620805541955478314925)
                  ·
                    rfl

theorem cell22_303407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 4].length) (baseStart_303407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303407 prefixEnd_303407 := by exact prefixLift 303407
  have htrace : WordTrace (prefixWord ++ tailWord_303407) baseStart_303407 baseEnd_303407 := by
    simpa [prefixWord, tailWord_303407, baseEnd_303407] using wordTrace_append hprefix tailTrace_303407
  have hstable : (prefixWord ++ tailWord_303407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303407).length < 2 ^ (prefixWord ++ tailWord_303407).sum := by decide
  have hdescent : baseEnd_303407 < baseStart_303407 := by decide
  rcases family_descends (prefixWord ++ tailWord_303407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303409 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_303409 : Nat := 118140960795 + 303409 * 2 ^ 59
def prefixEnd_303409 : Nat := 4983230072969 + 3 ^ 40 * 303409 * 2
def baseEnd_303409 : Nat := 103863101266739096394769

theorem tailTrace_303409 : CollatzResearch.WordTrace tailWord_303409 prefixEnd_303409 103863101266739096394769 := by
  unfold tailWord_303409
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066235357808485976857281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7377490238538990651238187 11066235357808485976857281)
  ·
    refine ⟨8299676518356364482642961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11066235357808485976857281 8299676518356364482642961)
    ·
      refine ⟨6224757388767273361982221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8299676518356364482642961 6224757388767273361982221)
      ·
        refine ⟨2334284020787727510743333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6224757388767273361982221 2334284020787727510743333)
        ·
          refine ⟨437678253897698908264375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2334284020787727510743333 437678253897698908264375)
          ·
            refine ⟨656517380846548362396563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437678253897698908264375 656517380846548362396563)
            ·
              refine ⟨984776071269822543594845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656517380846548362396563 984776071269822543594845)
              ·
                refine ⟨369291026726183453848067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 984776071269822543594845 369291026726183453848067)
                ·
                  refine ⟨553936540089275180772101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369291026726183453848067 553936540089275180772101)
                  ·
                    refine ⟨103863101266739096394769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553936540089275180772101 103863101266739096394769)
                    ·
                      rfl

theorem cell22_303409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_303409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303409 prefixEnd_303409 := by exact prefixLift 303409
  have htrace : WordTrace (prefixWord ++ tailWord_303409) baseStart_303409 baseEnd_303409 := by
    simpa [prefixWord, tailWord_303409, baseEnd_303409] using wordTrace_append hprefix tailTrace_303409
  have hstable : (prefixWord ++ tailWord_303409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303409).length < 2 ^ (prefixWord ++ tailWord_303409).sum := by decide
  have hdescent : baseEnd_303409 < baseStart_303409 := by decide
  rcases family_descends (prefixWord ++ tailWord_303409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303450 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_303450 : Nat := 118140960795 + 303450 * 2 ^ 59
def prefixEnd_303450 : Nat := 4983230072969 + 3 ^ 40 * 303450 * 2
def baseEnd_303450 : Nat := 103877136404628656119643

theorem tailTrace_303450 : CollatzResearch.WordTrace tailWord_303450 prefixEnd_303450 103877136404628656119643 := by
  unfold tailWord_303450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766932687664987494774951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7378487167106633319399869 2766932687664987494774951)
  ·
    refine ⟨4150399031497481242162427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766932687664987494774951 4150399031497481242162427)
    ·
      refine ⟨6225598547246221863243641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4150399031497481242162427 6225598547246221863243641)
      ·
        refine ⟨4669198910434666397432731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6225598547246221863243641 4669198910434666397432731)
        ·
          refine ⟨7003798365651999596149097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669198910434666397432731 7003798365651999596149097)
          ·
            refine ⟨5252848774238999697111823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7003798365651999596149097 5252848774238999697111823)
            ·
              refine ⟨7879273161358499545667735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5252848774238999697111823 7879273161358499545667735)
              ·
                refine ⟨11818909742037749318501603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7879273161358499545667735 11818909742037749318501603)
                ·
                  refine ⟨17728364613056623977752405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11818909742037749318501603 17728364613056623977752405)
                  ·
                    refine ⟨103877136404628656119643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17728364613056623977752405 103877136404628656119643)
                    ·
                      rfl

theorem cell22_303450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_303450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303450 prefixEnd_303450 := by exact prefixLift 303450
  have htrace : WordTrace (prefixWord ++ tailWord_303450) baseStart_303450 baseEnd_303450 := by
    simpa [prefixWord, tailWord_303450, baseEnd_303450] using wordTrace_append hprefix tailTrace_303450
  have hstable : (prefixWord ++ tailWord_303450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303450).length < 2 ^ (prefixWord ++ tailWord_303450).sum := by decide
  have hdescent : baseEnd_303450 < baseStart_303450 := by decide
  rcases family_descends (prefixWord ++ tailWord_303450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303619 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 3, 3]
def baseStart_303619 : Nat := 118140960795 + 303619 * 2 ^ 59
def prefixEnd_303619 : Nat := 4983230072969 + 3 ^ 40 * 303619 * 2
def baseEnd_303619 : Nat := 103934988558368548644125

theorem tailTrace_303619 : CollatzResearch.WordTrace tailWord_303619 prefixEnd_303619 103934988558368548644125 := by
  unfold tailWord_303619
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073894687047691842001911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382596458031794561334607 11073894687047691842001911)
  ·
    refine ⟨16610842030571537763002867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11073894687047691842001911 16610842030571537763002867)
    ·
      refine ⟨24916263045857306644504301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16610842030571537763002867 24916263045857306644504301)
      ·
        refine ⟨9343598642196489991689113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24916263045857306644504301 9343598642196489991689113)
        ·
          refine ⟨7007698981647367493766835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9343598642196489991689113 7007698981647367493766835)
          ·
            refine ⟨10511548472471051240650253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007698981647367493766835 10511548472471051240650253)
            ·
              refine ⟨3941830677176644215243845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10511548472471051240650253 3941830677176644215243845)
              ·
                refine ⟨739093251970620790358221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3941830677176644215243845 739093251970620790358221)
                ·
                  refine ⟨277159969488982796384333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739093251970620790358221 277159969488982796384333)
                  ·
                    refine ⟨103934988558368548644125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277159969488982796384333 103934988558368548644125)
                    ·
                      rfl

theorem cell22_303619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].length) (baseStart_303619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303619 prefixEnd_303619 := by exact prefixLift 303619
  have htrace : WordTrace (prefixWord ++ tailWord_303619) baseStart_303619 baseEnd_303619 := by
    simpa [prefixWord, tailWord_303619, baseEnd_303619] using wordTrace_append hprefix tailTrace_303619
  have hstable : (prefixWord ++ tailWord_303619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303619).length < 2 ^ (prefixWord ++ tailWord_303619).sum := by decide
  have hdescent : baseEnd_303619 < baseStart_303619 := by decide
  rcases family_descends (prefixWord ++ tailWord_303619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303649 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 5]
def baseStart_303649 : Nat := 118140960795 + 303649 * 2 ^ 59
def prefixEnd_303649 : Nat := 4983230072969 + 3 ^ 40 * 303649 * 2
def baseEnd_303649 : Nat := 34648419390486156798011

theorem tailTrace_303649 : CollatzResearch.WordTrace tailWord_303649 prefixEnd_303649 34648419390486156798011 := by
  unfold tailWord_303649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074988876939006965594001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7383325917959337977062667 11074988876939006965594001)
  ·
    refine ⟨8306241657704255224195501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11074988876939006965594001 8306241657704255224195501)
    ·
      refine ⟨3114840621639095709073313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8306241657704255224195501 3114840621639095709073313)
      ·
        refine ⟨2336130466229321781804985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3114840621639095709073313 2336130466229321781804985)
        ·
          refine ⟨1752097849671991336353739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336130466229321781804985 1752097849671991336353739)
          ·
            refine ⟨2628146774507987004530609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752097849671991336353739 2628146774507987004530609)
            ·
              refine ⟨1971110080880990253397957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628146774507987004530609 1971110080880990253397957)
              ·
                refine ⟨369583140165185672512117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1971110080880990253397957 369583140165185672512117)
                ·
                  refine ⟨34648419390486156798011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 369583140165185672512117 34648419390486156798011)
                  ·
                    rfl

theorem cell22_303649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_303649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303649 prefixEnd_303649 := by exact prefixLift 303649
  have htrace : WordTrace (prefixWord ++ tailWord_303649) baseStart_303649 baseEnd_303649 := by
    simpa [prefixWord, tailWord_303649, baseEnd_303649] using wordTrace_append hprefix tailTrace_303649
  have hstable : (prefixWord ++ tailWord_303649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303649).length < 2 ^ (prefixWord ++ tailWord_303649).sum := by decide
  have hdescent : baseEnd_303649 < baseStart_303649 := by decide
  rcases family_descends (prefixWord ++ tailWord_303649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303666 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_303666 : Nat := 118140960795 + 303666 * 2 ^ 59
def prefixEnd_303666 : Nat := 4983230072969 + 3 ^ 40 * 303666 * 2
def baseEnd_303666 : Nat := 34650359206292030906327

theorem tailTrace_303666 : CollatzResearch.WordTrace tailWord_303666 prefixEnd_303666 34650359206292030906327 := by
  unfold tailWord_303666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768902229469354717240713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7383739278584945912641901 2768902229469354717240713)
  ·
    refine ⟨2076676672102016037930535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2768902229469354717240713 2076676672102016037930535)
    ·
      refine ⟨3115015008153024056895803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076676672102016037930535 3115015008153024056895803)
      ·
        refine ⟨4672522512229536085343705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115015008153024056895803 4672522512229536085343705)
        ·
          refine ⟨3504391884172152064007779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4672522512229536085343705 3504391884172152064007779)
          ·
            refine ⟨5256587826258228096011669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504391884172152064007779 5256587826258228096011669)
            ·
              refine ⟨246402554355854442000547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5256587826258228096011669 246402554355854442000547)
              ·
                refine ⟨369603831533781663000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246402554355854442000547 369603831533781663000821)
                ·
                  refine ⟨34650359206292030906327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 369603831533781663000821 34650359206292030906327)
                  ·
                    rfl

theorem cell22_303666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_303666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303666 prefixEnd_303666 := by exact prefixLift 303666
  have htrace : WordTrace (prefixWord ++ tailWord_303666) baseStart_303666 baseEnd_303666 := by
    simpa [prefixWord, tailWord_303666, baseEnd_303666] using wordTrace_append hprefix tailTrace_303666
  have hstable : (prefixWord ++ tailWord_303666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303666).length < 2 ^ (prefixWord ++ tailWord_303666).sum := by decide
  have hdescent : baseEnd_303666 < baseStart_303666 := by decide
  rcases family_descends (prefixWord ++ tailWord_303666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303679 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_303679 : Nat := 118140960795 + 303679 * 2 ^ 59
def prefixEnd_303679 : Nat := 4983230072969 + 3 ^ 40 * 303679 * 2
def baseEnd_303679 : Nat := 103955527784548392143941

theorem tailTrace_303679 : CollatzResearch.WordTrace tailWord_303679 prefixEnd_303679 103955527784548392143941 := by
  unfold tailWord_303679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076083066830322089186091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7384055377886881392790727 11076083066830322089186091)
  ·
    refine ⟨16614124600245483133779137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11076083066830322089186091 16614124600245483133779137)
    ·
      refine ⟨12460593450184112350334353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16614124600245483133779137 12460593450184112350334353)
      ·
        refine ⟨9345445087638084262750765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12460593450184112350334353 9345445087638084262750765)
        ·
          refine ⟨3504541907864281598531537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9345445087638084262750765 3504541907864281598531537)
          ·
            refine ⟨2628406430898211198898653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504541907864281598531537 2628406430898211198898653)
            ·
              refine ⟨985652411586829199586995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628406430898211198898653 985652411586829199586995)
              ·
                refine ⟨1478478617380243799380493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985652411586829199586995 1478478617380243799380493)
                ·
                  refine ⟨554429481517591424767685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1478478617380243799380493 554429481517591424767685)
                  ·
                    refine ⟨103955527784548392143941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554429481517591424767685 103955527784548392143941)
                    ·
                      rfl

theorem cell22_303679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_303679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303679 prefixEnd_303679 := by exact prefixLift 303679
  have htrace : WordTrace (prefixWord ++ tailWord_303679) baseStart_303679 baseEnd_303679 := by
    simpa [prefixWord, tailWord_303679, baseEnd_303679] using wordTrace_append hprefix tailTrace_303679
  have hstable : (prefixWord ++ tailWord_303679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303679).length < 2 ^ (prefixWord ++ tailWord_303679).sum := by decide
  have hdescent : baseEnd_303679 < baseStart_303679 := by decide
  rcases family_descends (prefixWord ++ tailWord_303679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303724 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_303724 : Nat := 118140960795 + 303724 * 2 ^ 59
def prefixEnd_303724 : Nat := 4983230072969 + 3 ^ 40 * 303724 * 2
def baseEnd_303724 : Nat := 103970932204183274768803

theorem tailTrace_303724 : CollatzResearch.WordTrace tailWord_303724 prefixEnd_303724 103970932204183274768803 := by
  unfold tailWord_303724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538862175833647387287113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7385149567778196516382817 5538862175833647387287113)
  ·
    refine ⟨4154146631875235540465335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5538862175833647387287113 4154146631875235540465335)
    ·
      refine ⟨6231219947812853310698003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154146631875235540465335 6231219947812853310698003)
      ·
        refine ⟨9346829921719279966047005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231219947812853310698003 9346829921719279966047005)
        ·
          refine ⟨3505061220644729987267627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9346829921719279966047005 3505061220644729987267627)
          ·
            refine ⟨5257591830967094980901441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505061220644729987267627 5257591830967094980901441)
            ·
              refine ⟨3943193873225321235676081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257591830967094980901441 3943193873225321235676081)
              ·
                refine ⟨2957395404918990926757061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943193873225321235676081 2957395404918990926757061)
                ·
                  refine ⟨554511638422310798766949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2957395404918990926757061 554511638422310798766949)
                  ·
                    refine ⟨103970932204183274768803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554511638422310798766949 103970932204183274768803)
                    ·
                      rfl

theorem cell22_303724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_303724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303724 prefixEnd_303724 := by exact prefixLift 303724
  have htrace : WordTrace (prefixWord ++ tailWord_303724) baseStart_303724 baseEnd_303724 := by
    simpa [prefixWord, tailWord_303724, baseEnd_303724] using wordTrace_append hprefix tailTrace_303724
  have hstable : (prefixWord ++ tailWord_303724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303724).length < 2 ^ (prefixWord ++ tailWord_303724).sum := by decide
  have hdescent : baseEnd_303724 < baseStart_303724 := by decide
  rcases family_descends (prefixWord ++ tailWord_303724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303726 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_303726 : Nat := 118140960795 + 303726 * 2 ^ 59
def prefixEnd_303726 : Nat := 4983230072969 + 3 ^ 40 * 303726 * 2
def baseEnd_303726 : Nat := 103971616845055936218797

theorem tailTrace_303726 : CollatzResearch.WordTrace tailWord_303726 prefixEnd_303726 103971616845055936218797 := by
  unfold tailWord_303726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384724662207506139518379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7385198198440032744098021 1384724662207506139518379)
  ·
    refine ⟨2077086993311259209277569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384724662207506139518379 2077086993311259209277569)
    ·
      refine ⟨1557815244983444406958177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2077086993311259209277569 1557815244983444406958177)
      ·
        refine ⟨1168361433737583305218633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1557815244983444406958177 1168361433737583305218633)
        ·
          refine ⟨876271075303187478913975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168361433737583305218633 876271075303187478913975)
          ·
            refine ⟨1314406612954781218370963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876271075303187478913975 1314406612954781218370963)
            ·
              refine ⟨1971609919432171827556445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314406612954781218370963 1971609919432171827556445)
              ·
                refine ⟨739353719787064435333667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1971609919432171827556445 739353719787064435333667)
                ·
                  refine ⟨1109030579680596653000501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739353719787064435333667 1109030579680596653000501)
                  ·
                    refine ⟨103971616845055936218797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1109030579680596653000501 103971616845055936218797)
                    ·
                      rfl

theorem cell22_303726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_303726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303726 prefixEnd_303726 := by exact prefixLift 303726
  have htrace : WordTrace (prefixWord ++ tailWord_303726) baseStart_303726 baseEnd_303726 := by
    simpa [prefixWord, tailWord_303726, baseEnd_303726] using wordTrace_append hprefix tailTrace_303726
  have hstable : (prefixWord ++ tailWord_303726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303726).length < 2 ^ (prefixWord ++ tailWord_303726).sum := by decide
  have hdescent : baseEnd_303726 < baseStart_303726 := by decide
  rcases family_descends (prefixWord ++ tailWord_303726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303741 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_303741 : Nat := 118140960795 + 303741 * 2 ^ 59
def prefixEnd_303741 : Nat := 4983230072969 + 3 ^ 40 * 303741 * 2
def baseEnd_303741 : Nat := 103976751651600897093751

theorem tailTrace_303741 : CollatzResearch.WordTrace tailWord_303741 prefixEnd_303741 103976751651600897093751 := by
  unfold tailWord_303741
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078344392605706677943077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7385562928403804451962051 11078344392605706677943077)
  ·
    refine ⟨2077189573613570002114327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11078344392605706677943077 2077189573613570002114327)
    ·
      refine ⟨3115784360420355003171491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077189573613570002114327 3115784360420355003171491)
      ·
        refine ⟨4673676540630532504757237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115784360420355003171491 4673676540630532504757237)
        ·
          refine ⟨438157175684112422320991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4673676540630532504757237 438157175684112422320991)
          ·
            refine ⟨657235763526168633481487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438157175684112422320991 657235763526168633481487)
            ·
              refine ⟨985853645289252950222231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657235763526168633481487 985853645289252950222231)
              ·
                refine ⟨1478780467933879425333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985853645289252950222231 1478780467933879425333347)
                ·
                  refine ⟨2218170701900819138000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478780467933879425333347 2218170701900819138000021)
                  ·
                    refine ⟨103976751651600897093751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2218170701900819138000021 103976751651600897093751)
                    ·
                      rfl

theorem cell22_303741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_303741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303741 prefixEnd_303741 := by exact prefixLift 303741
  have htrace : WordTrace (prefixWord ++ tailWord_303741) baseStart_303741 baseEnd_303741 := by
    simpa [prefixWord, tailWord_303741, baseEnd_303741] using wordTrace_append hprefix tailTrace_303741
  have hstable : (prefixWord ++ tailWord_303741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303741).length < 2 ^ (prefixWord ++ tailWord_303741).sum := by decide
  have hdescent : baseEnd_303741 < baseStart_303741 := by decide
  rcases family_descends (prefixWord ++ tailWord_303741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303790 : List Nat := [4, 1, 4, 1, 1, 3, 2, 6]
def baseStart_303790 : Nat := 118140960795 + 303790 * 2 ^ 59
def prefixEnd_303790 : Nat := 4983230072969 + 3 ^ 40 * 303790 * 2
def baseEnd_303790 : Nat := 11554836150331233624289

theorem tailTrace_303790 : CollatzResearch.WordTrace tailWord_303790 prefixEnd_303790 11554836150331233624289 := by
  unfold tailWord_303790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385016446178523505809603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7386754379618792030984549 1385016446178523505809603)
  ·
    refine ⟨2077524669267785258714405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385016446178523505809603 2077524669267785258714405)
    ·
      refine ⟨389535875487709736008951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2077524669267785258714405 389535875487709736008951)
      ·
        refine ⟨584303813231564604013427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389535875487709736008951 584303813231564604013427)
        ·
          refine ⟨876455719847346906020141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584303813231564604013427 876455719847346906020141)
          ·
            refine ⟨328670894942755089757553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 876455719847346906020141 328670894942755089757553)
            ·
              refine ⟨246503171207066317318165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328670894942755089757553 246503171207066317318165)
              ·
                refine ⟨11554836150331233624289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246503171207066317318165 11554836150331233624289)
                ·
                  rfl

theorem cell22_303790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_303790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303790 prefixEnd_303790 := by exact prefixLift 303790
  have htrace : WordTrace (prefixWord ++ tailWord_303790) baseStart_303790 baseEnd_303790 := by
    simpa [prefixWord, tailWord_303790, baseEnd_303790] using wordTrace_append hprefix tailTrace_303790
  have hstable : (prefixWord ++ tailWord_303790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303790).length < 2 ^ (prefixWord ++ tailWord_303790).sum := by decide
  have hdescent : baseEnd_303790 < baseStart_303790 := by decide
  rcases family_descends (prefixWord ++ tailWord_303790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303805 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_303805 : Nat := 118140960795 + 303805 * 2 ^ 59
def prefixEnd_303805 : Nat := 4983230072969 + 3 ^ 40 * 303805 * 2
def baseEnd_303805 : Nat := 103998660159526063493555

theorem tailTrace_303805 : CollatzResearch.WordTrace tailWord_303805 prefixEnd_303805 103998660159526063493555 := by
  unfold tailWord_303805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080678664373845608272869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7387119109582563738848579 11080678664373845608272869)
  ·
    refine ⟨2077627249570096051551163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11080678664373845608272869 2077627249570096051551163)
    ·
      refine ⟨3116440874355144077326745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077627249570096051551163 3116440874355144077326745)
      ·
        refine ⟨2337330655766358057995059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116440874355144077326745 2337330655766358057995059)
        ·
          refine ⟨3505995983649537086992589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337330655766358057995059 3505995983649537086992589)
          ·
            refine ⟨1314748493868576407622221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3505995983649537086992589 1314748493868576407622221)
            ·
              refine ⟨493030685200716152858333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314748493868576407622221 493030685200716152858333)
              ·
                refine ⟨184886506950268557321875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493030685200716152858333 184886506950268557321875)
                ·
                  refine ⟨277329760425402835982813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184886506950268557321875 277329760425402835982813)
                  ·
                    refine ⟨103998660159526063493555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277329760425402835982813 103998660159526063493555)
                    ·
                      rfl

theorem cell22_303805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_303805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303805 prefixEnd_303805 := by exact prefixLift 303805
  have htrace : WordTrace (prefixWord ++ tailWord_303805) baseStart_303805 baseEnd_303805 := by
    simpa [prefixWord, tailWord_303805, baseEnd_303805] using wordTrace_append hprefix tailTrace_303805
  have hstable : (prefixWord ++ tailWord_303805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303805).length < 2 ^ (prefixWord ++ tailWord_303805).sum := by decide
  have hdescent : baseEnd_303805 < baseStart_303805 := by decide
  rcases family_descends (prefixWord ++ tailWord_303805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303822 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_303822 : Nat := 118140960795 + 303822 * 2 ^ 59
def prefixEnd_303822 : Nat := 4983230072969 + 3 ^ 40 * 303822 * 2
def baseEnd_303822 : Nat := 104004479606943685818503

theorem tailTrace_303822 : CollatzResearch.WordTrace tailWord_303822 prefixEnd_303822 104004479606943685818503 := by
  unfold tailWord_303822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385162338164032188955215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7387532470208171674427813 1385162338164032188955215)
  ·
    refine ⟨2077743507246048283432823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385162338164032188955215 2077743507246048283432823)
    ·
      refine ⟨3116615260869072425149235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077743507246048283432823 3116615260869072425149235)
      ·
        refine ⟨4674922891303608637723853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116615260869072425149235 4674922891303608637723853)
        ·
          refine ⟨1753096084238853239146445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4674922891303608637723853 1753096084238853239146445)
          ·
            refine ⟨657411031589569964679917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1753096084238853239146445 657411031589569964679917)
            ·
              refine ⟨246529136846088736754969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657411031589569964679917 246529136846088736754969)
              ·
                refine ⟨184896852634566552566227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246529136846088736754969 184896852634566552566227)
                ·
                  refine ⟨277345278951849828849341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184896852634566552566227 277345278951849828849341)
                  ·
                    refine ⟨104004479606943685818503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277345278951849828849341 104004479606943685818503)
                    ·
                      rfl

theorem cell22_303822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_303822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303822 prefixEnd_303822 := by exact prefixLift 303822
  have htrace : WordTrace (prefixWord ++ tailWord_303822) baseStart_303822 baseEnd_303822 := by
    simpa [prefixWord, tailWord_303822, baseEnd_303822] using wordTrace_append hprefix tailTrace_303822
  have hstable : (prefixWord ++ tailWord_303822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303822).length < 2 ^ (prefixWord ++ tailWord_303822).sum := by decide
  have hdescent : baseEnd_303822 < baseStart_303822 := by decide
  rcases family_descends (prefixWord ++ tailWord_303822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303848 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_303848 : Nat := 118140960795 + 303848 * 2 ^ 59
def prefixEnd_303848 : Nat := 4983230072969 + 3 ^ 40 * 303848 * 2
def baseEnd_303848 : Nat := 104013379938288284668423

theorem tailTrace_303848 : CollatzResearch.WordTrace tailWord_303848 prefixEnd_303848 104013379938288284668423 := by
  unfold tailWord_303848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541123501609031976044099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7388164668812042634725465 5541123501609031976044099)
  ·
    refine ⟨8311685252413547964066149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541123501609031976044099 8311685252413547964066149)
    ·
      refine ⟨1558440984827540243262403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8311685252413547964066149 1558440984827540243262403)
      ·
        refine ⟨2337661477241310364893605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558440984827540243262403 2337661477241310364893605)
        ·
          refine ⟨438311526982745693417551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2337661477241310364893605 438311526982745693417551)
          ·
            refine ⟨657467290474118540126327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438311526982745693417551 657467290474118540126327)
            ·
              refine ⟨986200935711177810189491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657467290474118540126327 986200935711177810189491)
              ·
                refine ⟨1479301403566766715284237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986200935711177810189491 1479301403566766715284237)
                ·
                  refine ⟨554738026337537518231589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479301403566766715284237 554738026337537518231589)
                  ·
                    refine ⟨104013379938288284668423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554738026337537518231589 104013379938288284668423)
                    ·
                      rfl

theorem cell22_303848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_303848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303848 prefixEnd_303848 := by exact prefixLift 303848
  have htrace : WordTrace (prefixWord ++ tailWord_303848) baseStart_303848 baseEnd_303848 := by
    simpa [prefixWord, tailWord_303848, baseEnd_303848] using wordTrace_append hprefix tailTrace_303848
  have hstable : (prefixWord ++ tailWord_303848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303848).length < 2 ^ (prefixWord ++ tailWord_303848).sum := by decide
  have hdescent : baseEnd_303848 < baseStart_303848 := by decide
  rcases family_descends (prefixWord ++ tailWord_303848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303880 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_303880 : Nat := 118140960795 + 303880 * 2 ^ 59
def prefixEnd_303880 : Nat := 4983230072969 + 3 ^ 40 * 303880 * 2
def baseEnd_303880 : Nat := 34674778064083622622775

theorem tailTrace_303880 : CollatzResearch.WordTrace tailWord_303880 prefixEnd_303880 34674778064083622622775 := by
  unfold tailWord_303880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541707069551066708626547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7388942759401422278168729 5541707069551066708626547)
  ·
    refine ⟨8312560604326600062939821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5541707069551066708626547 8312560604326600062939821)
    ·
      refine ⟨3117210226622475023602433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8312560604326600062939821 3117210226622475023602433)
      ·
        refine ⟨2337907669966856267701825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117210226622475023602433 2337907669966856267701825)
        ·
          refine ⟨1753430752475142200776369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337907669966856267701825 1753430752475142200776369)
          ·
            refine ⟨1315073064356356650582277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753430752475142200776369 1315073064356356650582277)
            ·
              refine ⟨246576199566816871984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1315073064356356650582277 246576199566816871984177)
              ·
                refine ⟨184932149675112653988133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246576199566816871984177 184932149675112653988133)
                ·
                  refine ⟨34674778064083622622775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184932149675112653988133 34674778064083622622775)
                  ·
                    rfl

theorem cell22_303880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_303880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_303880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_303880 prefixEnd_303880 := by exact prefixLift 303880
  have htrace : WordTrace (prefixWord ++ tailWord_303880) baseStart_303880 baseEnd_303880 := by
    simpa [prefixWord, tailWord_303880, baseEnd_303880] using wordTrace_append hprefix tailTrace_303880
  have hstable : (prefixWord ++ tailWord_303880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303880).length < 2 ^ (prefixWord ++ tailWord_303880).sum := by decide
  have hdescent : baseEnd_303880 < baseStart_303880 := by decide
  rcases family_descends (prefixWord ++ tailWord_303880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304011 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_304011 : Nat := 118140960795 + 304011 * 2 ^ 59
def prefixEnd_304011 : Nat := 4983230072969 + 3 ^ 40 * 304011 * 2
def baseEnd_304011 : Nat := 104069178169410192842923

theorem tailTrace_304011 : CollatzResearch.WordTrace tailWord_304011 prefixEnd_304011 104069178169410192842923 := by
  unfold tailWord_304011
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088192101627542790271887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7392128067751695193514591 11088192101627542790271887)
  ·
    refine ⟨16632288152441314185407831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11088192101627542790271887 16632288152441314185407831)
    ·
      refine ⟨24948432228661971278111747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16632288152441314185407831 24948432228661971278111747)
      ·
        refine ⟨37422648342992956917167621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24948432228661971278111747 37422648342992956917167621)
        ·
          refine ⟨7016746564311179421968929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37422648342992956917167621 7016746564311179421968929)
          ·
            refine ⟨5262559923233384566476697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7016746564311179421968929 5262559923233384566476697)
            ·
              refine ⟨3946919942425038424857523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5262559923233384566476697 3946919942425038424857523)
              ·
                refine ⟨5920379913637557637286285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946919942425038424857523 5920379913637557637286285)
                ·
                  refine ⟨2220142467614084113982357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5920379913637557637286285 2220142467614084113982357)
                  ·
                    refine ⟨104069178169410192842923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2220142467614084113982357 104069178169410192842923)
                    ·
                      rfl

theorem cell22_304011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_304011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304011 prefixEnd_304011 := by exact prefixLift 304011
  have htrace : WordTrace (prefixWord ++ tailWord_304011) baseStart_304011 baseEnd_304011 := by
    simpa [prefixWord, tailWord_304011, baseEnd_304011] using wordTrace_append hprefix tailTrace_304011
  have hstable : (prefixWord ++ tailWord_304011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304011).length < 2 ^ (prefixWord ++ tailWord_304011).sum := by decide
  have hdescent : baseEnd_304011 < baseStart_304011 := by decide
  rcases family_descends (prefixWord ++ tailWord_304011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304049 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 4]
def baseStart_304049 : Nat := 118140960795 + 304049 * 2 ^ 59
def prefixEnd_304049 : Nat := 4983230072969 + 3 ^ 40 * 304049 * 2
def baseEnd_304049 : Nat := 34694062115330253464269

theorem tailTrace_304049 : CollatzResearch.WordTrace tailWord_304049 prefixEnd_304049 34694062115330253464269 := by
  unfold tailWord_304049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089578075489875280155201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7393052050326583520103467 11089578075489875280155201)
  ·
    refine ⟨8317183556617406460116401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11089578075489875280155201 8317183556617406460116401)
    ·
      refine ⟨6237887667463054845087301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8317183556617406460116401 6237887667463054845087301)
      ·
        refine ⟨1169603937649322783453869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6237887667463054845087301 1169603937649322783453869)
        ·
          refine ⟨438601476618496043795201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1169603937649322783453869 438601476618496043795201)
          ·
            refine ⟨328951107463872032846401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438601476618496043795201 328951107463872032846401)
            ·
              refine ⟨246713330597904024634801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328951107463872032846401 246713330597904024634801)
              ·
                refine ⟨185034997948428018476101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246713330597904024634801 185034997948428018476101)
                ·
                  refine ⟨34694062115330253464269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185034997948428018476101 34694062115330253464269)
                  ·
                    rfl

theorem cell22_304049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_304049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304049 prefixEnd_304049 := by exact prefixLift 304049
  have htrace : WordTrace (prefixWord ++ tailWord_304049) baseStart_304049 baseEnd_304049 := by
    simpa [prefixWord, tailWord_304049, baseEnd_304049] using wordTrace_append hprefix tailTrace_304049
  have hstable : (prefixWord ++ tailWord_304049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304049).length < 2 ^ (prefixWord ++ tailWord_304049).sum := by decide
  have hdescent : baseEnd_304049 < baseStart_304049 := by decide
  rcases family_descends (prefixWord ++ tailWord_304049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304075 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 3, 3]
def baseStart_304075 : Nat := 118140960795 + 304075 * 2 ^ 59
def prefixEnd_304075 : Nat := 4983230072969 + 3 ^ 40 * 304075 * 2
def baseEnd_304075 : Nat := 104091086677335359242727

theorem tailTrace_304075 : CollatzResearch.WordTrace tailWord_304075 prefixEnd_304075 104091086677335359242727 := by
  unfold tailWord_304075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090526373395681720601679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7393684248930454480401119 11090526373395681720601679)
  ·
    refine ⟨16635789560093522580902519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11090526373395681720601679 16635789560093522580902519)
    ·
      refine ⟨24953684340140283871353779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16635789560093522580902519 24953684340140283871353779)
      ·
        refine ⟨37430526510210425807030669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24953684340140283871353779 37430526510210425807030669)
        ·
          refine ⟨14036447441328909677636501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37430526510210425807030669 14036447441328909677636501)
          ·
            refine ⟨657958473812292641139211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14036447441328909677636501 657958473812292641139211)
            ·
              refine ⟨986937710718438961708817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657958473812292641139211 986937710718438961708817)
              ·
                refine ⟨740203283038829221281613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986937710718438961708817 740203283038829221281613)
                ·
                  refine ⟨277576231139560957980605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740203283038829221281613 277576231139560957980605)
                  ·
                    refine ⟨104091086677335359242727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277576231139560957980605 104091086677335359242727)
                    ·
                      rfl

theorem cell22_304075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].length) (baseStart_304075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304075 prefixEnd_304075 := by exact prefixLift 304075
  have htrace : WordTrace (prefixWord ++ tailWord_304075) baseStart_304075 baseEnd_304075 := by
    simpa [prefixWord, tailWord_304075, baseEnd_304075] using wordTrace_append hprefix tailTrace_304075
  have hstable : (prefixWord ++ tailWord_304075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304075).length < 2 ^ (prefixWord ++ tailWord_304075).sum := by decide
  have hdescent : baseEnd_304075 < baseStart_304075 := by decide
  rcases family_descends (prefixWord ++ tailWord_304075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304133 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 6]
def baseStart_304133 : Nat := 118140960795 + 304133 * 2 ^ 59
def prefixEnd_304133 : Nat := 4983230072969 + 3 ^ 40 * 304133 * 2
def baseEnd_304133 : Nat := 34703647087547513764183

theorem tailTrace_304133 : CollatzResearch.WordTrace tailWord_304133 prefixEnd_304133 34703647087547513764183 := by
  unfold tailWord_304133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092641807185557626213053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395094538123705084142035 11092641807185557626213053)
  ·
    refine ⟨4159740677694584109829895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11092641807185557626213053 4159740677694584109829895)
    ·
      refine ⟨6239611016541876164744843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4159740677694584109829895 6239611016541876164744843)
      ·
        refine ⟨9359416524812814247117265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6239611016541876164744843 9359416524812814247117265)
        ·
          refine ⟨7019562393609610685337949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9359416524812814247117265 7019562393609610685337949)
          ·
            refine ⟨2632335897603604007001731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7019562393609610685337949 2632335897603604007001731)
            ·
              refine ⟨3948503846405406010502597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632335897603604007001731 3948503846405406010502597)
              ·
                refine ⟨740344471201013626969237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3948503846405406010502597 740344471201013626969237)
                ·
                  refine ⟨34703647087547513764183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 740344471201013626969237 34703647087547513764183)
                  ·
                    rfl

theorem cell22_304133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_304133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304133 prefixEnd_304133 := by exact prefixLift 304133
  have htrace : WordTrace (prefixWord ++ tailWord_304133) baseStart_304133 baseEnd_304133 := by
    simpa [prefixWord, tailWord_304133, baseEnd_304133] using wordTrace_append hprefix tailTrace_304133
  have hstable : (prefixWord ++ tailWord_304133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304133).length < 2 ^ (prefixWord ++ tailWord_304133).sum := by decide
  have hdescent : baseEnd_304133 < baseStart_304133 := by decide
  rcases family_descends (prefixWord ++ tailWord_304133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304165 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_304165 : Nat := 118140960795 + 304165 * 2 ^ 59
def prefixEnd_304165 : Nat := 4983230072969 + 3 ^ 40 * 304165 * 2
def baseEnd_304165 : Nat := 104121895516605124492451

theorem tailTrace_304165 : CollatzResearch.WordTrace tailWord_304165 prefixEnd_304165 104121895516605124492451 := by
  unfold tailWord_304165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093808943069627091377949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395872628713084727585299 11093808943069627091377949)
  ·
    refine ⟨4160178353651110159266731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11093808943069627091377949 4160178353651110159266731)
    ·
      refine ⟨6240267530476665238900097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160178353651110159266731 6240267530476665238900097)
      ·
        refine ⟨4680200647857498929175073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6240267530476665238900097 4680200647857498929175073)
        ·
          refine ⟨3510150485893124196881305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4680200647857498929175073 3510150485893124196881305)
          ·
            refine ⟨2632612864419843147660979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510150485893124196881305 2632612864419843147660979)
            ·
              refine ⟨3948919296629764721491469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632612864419843147660979 3948919296629764721491469)
              ·
                refine ⟨1480844736236161770559301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3948919296629764721491469 1480844736236161770559301)
                ·
                  refine ⟨277658388044280331979869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480844736236161770559301 277658388044280331979869)
                  ·
                    refine ⟨104121895516605124492451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277658388044280331979869 104121895516605124492451)
                    ·
                      rfl

theorem cell22_304165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_304165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304165 prefixEnd_304165 := by exact prefixLift 304165
  have htrace : WordTrace (prefixWord ++ tailWord_304165) baseStart_304165 baseEnd_304165 := by
    simpa [prefixWord, tailWord_304165, baseEnd_304165] using wordTrace_append hprefix tailTrace_304165
  have hstable : (prefixWord ++ tailWord_304165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304165).length < 2 ^ (prefixWord ++ tailWord_304165).sum := by decide
  have hdescent : baseEnd_304165 < baseStart_304165 := by decide
  rcases family_descends (prefixWord ++ tailWord_304165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304167 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 6]
def baseStart_304167 : Nat := 118140960795 + 304167 * 2 ^ 59
def prefixEnd_304167 : Nat := 4983230072969 + 3 ^ 40 * 304167 * 2
def baseEnd_304167 : Nat := 34707526719159261980815

theorem tailTrace_304167 : CollatzResearch.WordTrace tailWord_304167 prefixEnd_304167 34707526719159261980815 := by
  unfold tailWord_304167
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093881889062381432950755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395921259374920955300503 11093881889062381432950755)
  ·
    refine ⟨16640822833593572149426133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11093881889062381432950755 16640822833593572149426133)
    ·
      refine ⟨390019285162349347252175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16640822833593572149426133 390019285162349347252175)
      ·
        refine ⟨585028927743524020878263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390019285162349347252175 585028927743524020878263)
        ·
          refine ⟨877543391615286031317395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585028927743524020878263 877543391615286031317395)
          ·
            refine ⟨1316315087422929046976093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877543391615286031317395 1316315087422929046976093)
            ·
              refine ⟨493618157783598392616035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316315087422929046976093 493618157783598392616035)
              ·
                refine ⟨740427236675397588924053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493618157783598392616035 740427236675397588924053)
                ·
                  refine ⟨34707526719159261980815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 740427236675397588924053 34707526719159261980815)
                  ·
                    rfl

theorem cell22_304167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].length) (baseStart_304167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304167 prefixEnd_304167 := by exact prefixLift 304167
  have htrace : WordTrace (prefixWord ++ tailWord_304167) baseStart_304167 baseEnd_304167 := by
    simpa [prefixWord, tailWord_304167, baseEnd_304167] using wordTrace_append hprefix tailTrace_304167
  have hstable : (prefixWord ++ tailWord_304167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304167).length < 2 ^ (prefixWord ++ tailWord_304167).sum := by decide
  have hdescent : baseEnd_304167 < baseStart_304167 := by decide
  rcases family_descends (prefixWord ++ tailWord_304167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304208 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_304208 : Nat := 118140960795 + 304208 * 2 ^ 59
def prefixEnd_304208 : Nat := 4983230072969 + 3 ^ 40 * 304208 * 2
def baseEnd_304208 : Nat := 104136615295367345667319

theorem tailTrace_304208 : CollatzResearch.WordTrace tailWord_304208 prefixEnd_304208 104136615295367345667319 := by
  unfold tailWord_304208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547688640956922717596639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7396918187942563623462185 5547688640956922717596639)
  ·
    refine ⟨8321532961435384076394959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547688640956922717596639 8321532961435384076394959)
    ·
      refine ⟨12482299442153076114592439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321532961435384076394959 12482299442153076114592439)
      ·
        refine ⟨18723449163229614171888659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482299442153076114592439 18723449163229614171888659)
        ·
          refine ⟨28085173744844421257832989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18723449163229614171888659 28085173744844421257832989)
          ·
            refine ⟨10531940154316657971687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28085173744844421257832989 10531940154316657971687371)
            ·
              refine ⟨15797910231474986957531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10531940154316657971687371 15797910231474986957531057)
              ·
                refine ⟨11848432673606240218148293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15797910231474986957531057 11848432673606240218148293)
                ·
                  refine ⟨2221581126301170040902805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11848432673606240218148293 2221581126301170040902805)
                  ·
                    refine ⟨104136615295367345667319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2221581126301170040902805 104136615295367345667319)
                    ·
                      rfl

theorem cell22_304208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_304208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304208 prefixEnd_304208 := by exact prefixLift 304208
  have htrace : WordTrace (prefixWord ++ tailWord_304208) baseStart_304208 baseEnd_304208 := by
    simpa [prefixWord, tailWord_304208, baseEnd_304208] using wordTrace_append hprefix tailTrace_304208
  have hstable : (prefixWord ++ tailWord_304208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304208).length < 2 ^ (prefixWord ++ tailWord_304208).sum := by decide
  have hdescent : baseEnd_304208 < baseStart_304208 := by decide
  rcases family_descends (prefixWord ++ tailWord_304208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304240 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_304240 : Nat := 118140960795 + 304240 * 2 ^ 59
def prefixEnd_304240 : Nat := 4983230072969 + 3 ^ 40 * 304240 * 2
def baseEnd_304240 : Nat := 34715856516443309622407

theorem tailTrace_304240 : CollatzResearch.WordTrace tailWord_304240 prefixEnd_304240 34715856516443309622407 := by
  unfold tailWord_304240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548272208898957450179087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7397696278531943266905449 5548272208898957450179087)
  ·
    refine ⟨8322408313348436175268631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548272208898957450179087 8322408313348436175268631)
    ·
      refine ⟨12483612470022654262902947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322408313348436175268631 12483612470022654262902947)
      ·
        refine ⟨18725418705033981394354421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483612470022654262902947 18725418705033981394354421)
        ·
          refine ⟨1755508003596935755720727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18725418705033981394354421 1755508003596935755720727)
          ·
            refine ⟨2633262005395403633581091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755508003596935755720727 2633262005395403633581091)
            ·
              refine ⟨3949893008093105450371637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633262005395403633581091 3949893008093105450371637)
              ·
                refine ⟨370302469508728635972341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3949893008093105450371637 370302469508728635972341)
                ·
                  refine ⟨34715856516443309622407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370302469508728635972341 34715856516443309622407)
                  ·
                    rfl

theorem cell22_304240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_304240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304240 prefixEnd_304240 := by exact prefixLift 304240
  have htrace : WordTrace (prefixWord ++ tailWord_304240) baseStart_304240 baseEnd_304240 := by
    simpa [prefixWord, tailWord_304240, baseEnd_304240] using wordTrace_append hprefix tailTrace_304240
  have hstable : (prefixWord ++ tailWord_304240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304240).length < 2 ^ (prefixWord ++ tailWord_304240).sum := by decide
  have hdescent : baseEnd_304240 < baseStart_304240 := by decide
  rcases family_descends (prefixWord ++ tailWord_304240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304261 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_304261 : Nat := 118140960795 + 304261 * 2 ^ 59
def prefixEnd_304261 : Nat := 4983230072969 + 3 ^ 40 * 304261 * 2
def baseEnd_304261 : Nat := 104154758278492874092157

theorem tailTrace_304261 : CollatzResearch.WordTrace tailWord_304261 prefixEnd_304261 104154758278492874092157 := by
  unfold tailWord_304261
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097310350721835486872637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7398206900481223657915091 11097310350721835486872637)
  ·
    refine ⟨4161491381520688307577239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11097310350721835486872637 4161491381520688307577239)
    ·
      refine ⟨6242237072281032461365859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161491381520688307577239 6242237072281032461365859)
      ·
        refine ⟨9363355608421548692048789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242237072281032461365859 9363355608421548692048789)
        ·
          refine ⟨438907294144760094939787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9363355608421548692048789 438907294144760094939787)
          ·
            refine ⟨658360941217140142409681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438907294144760094939787 658360941217140142409681)
            ·
              refine ⟨493770705912855106807261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658360941217140142409681 493770705912855106807261)
              ·
                refine ⟨185164014717320665052723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493770705912855106807261 185164014717320665052723)
                ·
                  refine ⟨277746022075980997579085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185164014717320665052723 277746022075980997579085)
                  ·
                    refine ⟨104154758278492874092157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277746022075980997579085 104154758278492874092157)
                    ·
                      rfl

theorem cell22_304261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_304261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304261 prefixEnd_304261 := by exact prefixLift 304261
  have htrace : WordTrace (prefixWord ++ tailWord_304261) baseStart_304261 baseEnd_304261 := by
    simpa [prefixWord, tailWord_304261, baseEnd_304261] using wordTrace_append hprefix tailTrace_304261
  have hstable : (prefixWord ++ tailWord_304261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304261).length < 2 ^ (prefixWord ++ tailWord_304261).sum := by decide
  have hdescent : baseEnd_304261 < baseStart_304261 := by decide
  rcases family_descends (prefixWord ++ tailWord_304261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304274 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_304274 : Nat := 118140960795 + 304274 * 2 ^ 59
def prefixEnd_304274 : Nat := 4983230072969 + 3 ^ 40 * 304274 * 2
def baseEnd_304274 : Nat := 34719736148055057839039

theorem tailTrace_304274 : CollatzResearch.WordTrace tailWord_304274 prefixEnd_304274 34719736148055057839039 := by
  unfold tailWord_304274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774446124918684676773969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7398522999783159138063917 2774446124918684676773969)
  ·
    refine ⟨2080834593689013507580477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2774446124918684676773969 2080834593689013507580477)
    ·
      refine ⟨780312972633380065342679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2080834593689013507580477 780312972633380065342679)
      ·
        refine ⟨1170469458950070098014019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780312972633380065342679 1170469458950070098014019)
        ·
          refine ⟨1755704188425105147021029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170469458950070098014019 1755704188425105147021029)
          ·
            refine ⟨329194535329707215066443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1755704188425105147021029 329194535329707215066443)
            ·
              refine ⟨493791802994560822599665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329194535329707215066443 493791802994560822599665)
              ·
                refine ⟨370343852245920616949749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493791802994560822599665 370343852245920616949749)
                ·
                  refine ⟨34719736148055057839039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370343852245920616949749 34719736148055057839039)
                  ·
                    rfl

theorem cell22_304274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_304274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304274 prefixEnd_304274 := by exact prefixLift 304274
  have htrace : WordTrace (prefixWord ++ tailWord_304274) baseStart_304274 baseEnd_304274 := by
    simpa [prefixWord, tailWord_304274, baseEnd_304274] using wordTrace_append hprefix tailTrace_304274
  have hstable : (prefixWord ++ tailWord_304274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304274).length < 2 ^ (prefixWord ++ tailWord_304274).sum := by decide
  have hdescent : baseEnd_304274 < baseStart_304274 := by decide
  rcases family_descends (prefixWord ++ tailWord_304274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304300 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_304300 : Nat := 118140960795 + 304300 * 2 ^ 59
def prefixEnd_304300 : Nat := 4983230072969 + 3 ^ 40 * 304300 * 2
def baseEnd_304300 : Nat := 104168108775509772367037

theorem tailTrace_304300 : CollatzResearch.WordTrace tailWord_304300 prefixEnd_304300 104168108775509772367037 := by
  unfold tailWord_304300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549366398790272573771177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7399155198387030098361569 5549366398790272573771177)
  ·
    refine ⟨4162024799092704430328383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5549366398790272573771177 4162024799092704430328383)
    ·
      refine ⟨6243037198639056645492575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162024799092704430328383 6243037198639056645492575)
      ·
        refine ⟨9364555797958584968238863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243037198639056645492575 9364555797958584968238863)
        ·
          refine ⟨14046833696937877452358295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9364555797958584968238863 14046833696937877452358295)
          ·
            refine ⟨21070250545406816178537443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14046833696937877452358295 21070250545406816178537443)
            ·
              refine ⟨31605375818110224267806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21070250545406816178537443 31605375818110224267806165)
              ·
                refine ⟨740750995736958381276707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31605375818110224267806165 740750995736958381276707)
                ·
                  refine ⟨1111126493605437571915061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740750995736958381276707 1111126493605437571915061)
                  ·
                    refine ⟨104168108775509772367037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1111126493605437571915061 104168108775509772367037)
                    ·
                      rfl

theorem cell22_304300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_304300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304300 prefixEnd_304300 := by exact prefixLift 304300
  have htrace : WordTrace (prefixWord ++ tailWord_304300) baseStart_304300 baseEnd_304300 := by
    simpa [prefixWord, tailWord_304300, baseEnd_304300] using wordTrace_append hprefix tailTrace_304300
  have hstable : (prefixWord ++ tailWord_304300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304300).length < 2 ^ (prefixWord ++ tailWord_304300).sum := by decide
  have hdescent : baseEnd_304300 < baseStart_304300 := by decide
  rcases family_descends (prefixWord ++ tailWord_304300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304317 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_304317 : Nat := 118140960795 + 304317 * 2 ^ 59
def prefixEnd_304317 : Nat := 4983230072969 + 3 ^ 40 * 304317 * 2
def baseEnd_304317 : Nat := 104173928222927394691985

theorem tailTrace_304317 : CollatzResearch.WordTrace tailWord_304317 prefixEnd_304317 104173928222927394691985 := by
  unfold tailWord_304317
  simp only [CollatzResearch.WordTrace]
  refine ⟨11099352838518957050911205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7399568559012638033940803 11099352838518957050911205)
  ·
    refine ⟨2081128657222304447045851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11099352838518957050911205 2081128657222304447045851)
    ·
      refine ⟨3121692985833456670568777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2081128657222304447045851 3121692985833456670568777)
      ·
        refine ⟨2341269739375092502926583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3121692985833456670568777 2341269739375092502926583)
        ·
          refine ⟨3511904609062638754389875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341269739375092502926583 3511904609062638754389875)
          ·
            refine ⟨5267856913593958131584813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511904609062638754389875 5267856913593958131584813)
            ·
              refine ⟨1975446342597734299344305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5267856913593958131584813 1975446342597734299344305)
              ·
                refine ⟨1481584756948300724508229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975446342597734299344305 1481584756948300724508229)
                ·
                  refine ⟨277797141927806385845293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481584756948300724508229 277797141927806385845293)
                  ·
                    refine ⟨104173928222927394691985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277797141927806385845293 104173928222927394691985)
                    ·
                      rfl

theorem cell22_304317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_304317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304317 prefixEnd_304317 := by exact prefixLift 304317
  have htrace : WordTrace (prefixWord ++ tailWord_304317) baseStart_304317 baseEnd_304317 := by
    simpa [prefixWord, tailWord_304317, baseEnd_304317] using wordTrace_append hprefix tailTrace_304317
  have hstable : (prefixWord ++ tailWord_304317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304317).length < 2 ^ (prefixWord ++ tailWord_304317).sum := by decide
  have hdescent : baseEnd_304317 < baseStart_304317 := by decide
  rcases family_descends (prefixWord ++ tailWord_304317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304330 : List Nat := [3, 1, 2, 1, 3, 2, 10]
def baseStart_304330 : Nat := 118140960795 + 304330 * 2 ^ 59
def prefixEnd_304330 : Nat := 4983230072969 + 3 ^ 40 * 304330 * 2
def baseEnd_304330 : Nat := 3858458458837025708035

theorem tailTrace_304330 : CollatzResearch.WordTrace tailWord_304330 prefixEnd_304330 3858458458837025708035 := by
  unfold tailWord_304330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774956746867965067783611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7399884658314573514089629 2774956746867965067783611)
  ·
    refine ⟨4162435120301947601675417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774956746867965067783611 4162435120301947601675417)
    ·
      refine ⟨3121826340226460701256563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4162435120301947601675417 3121826340226460701256563)
      ·
        refine ⟨4682739510339691051884845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121826340226460701256563 4682739510339691051884845)
        ·
          refine ⟨1756027316377384144456817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4682739510339691051884845 1756027316377384144456817)
          ·
            refine ⟨1317020487283038108342613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756027316377384144456817 1317020487283038108342613)
            ·
              refine ⟨3858458458837025708035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1317020487283038108342613 3858458458837025708035)
              ·
                rfl

theorem cell22_304330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 10].length) (baseStart_304330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304330 prefixEnd_304330 := by exact prefixLift 304330
  have htrace : WordTrace (prefixWord ++ tailWord_304330) baseStart_304330 baseEnd_304330 := by
    simpa [prefixWord, tailWord_304330, baseEnd_304330] using wordTrace_append hprefix tailTrace_304330
  have hstable : (prefixWord ++ tailWord_304330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304330).length < 2 ^ (prefixWord ++ tailWord_304330).sum := by decide
  have hdescent : baseEnd_304330 < baseStart_304330 := by decide
  rcases family_descends (prefixWord ++ tailWord_304330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304396 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_304396 : Nat := 118140960795 + 304396 * 2 ^ 59
def prefixEnd_304396 : Nat := 4983230072969 + 3 ^ 40 * 304396 * 2
def baseEnd_304396 : Nat := 104200971537397521966743

theorem tailTrace_304396 : CollatzResearch.WordTrace tailWord_304396 prefixEnd_304396 104200971537397521966743 := by
  unfold tailWord_304396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551117102616376771518521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7401489470155169028691361 5551117102616376771518521)
  ·
    refine ⟨4163337826962282578638891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5551117102616376771518521 4163337826962282578638891)
    ·
      refine ⟨6245006740443423867958337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163337826962282578638891 6245006740443423867958337)
      ·
        refine ⟨4683755055332567900968753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6245006740443423867958337 4683755055332567900968753)
        ·
          refine ⟨3512816291499425925726565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4683755055332567900968753 3512816291499425925726565)
          ·
            refine ⟨658653054656142361073731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3512816291499425925726565 658653054656142361073731)
            ·
              refine ⟨987979581984213541610597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658653054656142361073731 987979581984213541610597)
              ·
                refine ⟨185246171622040039051987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 987979581984213541610597 185246171622040039051987)
                ·
                  refine ⟨277869257433060058577981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185246171622040039051987 277869257433060058577981)
                  ·
                    refine ⟨104200971537397521966743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277869257433060058577981 104200971537397521966743)
                    ·
                      rfl

theorem cell22_304396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_304396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304396 prefixEnd_304396 := by exact prefixLift 304396
  have htrace : WordTrace (prefixWord ++ tailWord_304396) baseStart_304396 baseEnd_304396 := by
    simpa [prefixWord, tailWord_304396, baseEnd_304396] using wordTrace_append hprefix tailTrace_304396
  have hstable : (prefixWord ++ tailWord_304396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304396).length < 2 ^ (prefixWord ++ tailWord_304396).sum := by decide
  have hdescent : baseEnd_304396 < baseStart_304396 := by decide
  rcases family_descends (prefixWord ++ tailWord_304396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304407 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_304407 : Nat := 118140960795 + 304407 * 2 ^ 59
def prefixEnd_304407 : Nat := 4983230072969 + 3 ^ 40 * 304407 * 2
def baseEnd_304407 : Nat := 104204737062197159941709

theorem tailTrace_304407 : CollatzResearch.WordTrace tailWord_304407 prefixEnd_304407 104204737062197159941709 := by
  unfold tailWord_304407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102635408192902421687475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7401756938795268281124983 11102635408192902421687475)
  ·
    refine ⟨16653953112289353632531213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102635408192902421687475 16653953112289353632531213)
    ·
      refine ⟨6245232417108507612199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16653953112289353632531213 6245232417108507612199205)
      ·
        refine ⟨1170981078207845177287351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6245232417108507612199205 1170981078207845177287351)
        ·
          refine ⟨1756471617311767765931027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170981078207845177287351 1756471617311767765931027)
          ·
            refine ⟨2634707425967651648896541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756471617311767765931027 2634707425967651648896541)
            ·
              refine ⟨988015284737869368336203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2634707425967651648896541 988015284737869368336203)
              ·
                refine ⟨1482022927106804052504305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988015284737869368336203 1482022927106804052504305)
                ·
                  refine ⟨1111517195330103039378229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482022927106804052504305 1111517195330103039378229)
                  ·
                    refine ⟨104204737062197159941709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1111517195330103039378229 104204737062197159941709)
                    ·
                      rfl

theorem cell22_304407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_304407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304407 prefixEnd_304407 := by exact prefixLift 304407
  have htrace : WordTrace (prefixWord ++ tailWord_304407) baseStart_304407 baseEnd_304407 := by
    simpa [prefixWord, tailWord_304407, baseEnd_304407] using wordTrace_append hprefix tailTrace_304407
  have hstable : (prefixWord ++ tailWord_304407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304407).length < 2 ^ (prefixWord ++ tailWord_304407).sum := by decide
  have hdescent : baseEnd_304407 < baseStart_304407 := by decide
  rcases family_descends (prefixWord ++ tailWord_304407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304469 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_304469 : Nat := 118140960795 + 304469 * 2 ^ 59
def prefixEnd_304469 : Nat := 4983230072969 + 3 ^ 40 * 304469 * 2
def baseEnd_304469 : Nat := 104225960929249664891519

theorem tailTrace_304469 : CollatzResearch.WordTrace tailWord_304469 prefixEnd_304469 104225960929249664891519 := by
  unfold tailWord_304469
  simp only [CollatzResearch.WordTrace]
  refine ⟨11104896733968287010444461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7403264489312191340296307 11104896733968287010444461)
  ·
    refine ⟨4164336275238107628916673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11104896733968287010444461 4164336275238107628916673)
    ·
      refine ⟨3123252206428580721687505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4164336275238107628916673 3123252206428580721687505)
      ·
        refine ⟨2342439154821435541265629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123252206428580721687505 2342439154821435541265629)
        ·
          refine ⟨878414683058038327974611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2342439154821435541265629 878414683058038327974611)
          ·
            refine ⟨1317622024587057491961917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878414683058038327974611 1317622024587057491961917)
            ·
              refine ⟨494108259220146559485719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317622024587057491961917 494108259220146559485719)
              ·
                refine ⟨741162388830219839228579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494108259220146559485719 741162388830219839228579)
                ·
                  refine ⟨1111743583245329758842869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741162388830219839228579 1111743583245329758842869)
                  ·
                    refine ⟨104225960929249664891519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1111743583245329758842869 104225960929249664891519)
                    ·
                      rfl

theorem cell22_304469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_304469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304469 prefixEnd_304469 := by exact prefixLift 304469
  have htrace : WordTrace (prefixWord ++ tailWord_304469) baseStart_304469 baseEnd_304469 := by
    simpa [prefixWord, tailWord_304469, baseEnd_304469] using wordTrace_append hprefix tailTrace_304469
  have hstable : (prefixWord ++ tailWord_304469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304469).length < 2 ^ (prefixWord ++ tailWord_304469).sum := by decide
  have hdescent : baseEnd_304469 < baseStart_304469 := by decide
  rcases family_descends (prefixWord ++ tailWord_304469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304488 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_304488 : Nat := 118140960795 + 304488 * 2 ^ 59
def prefixEnd_304488 : Nat := 4983230072969 + 3 ^ 40 * 304488 * 2
def baseEnd_304488 : Nat := 34744155005846649555487

theorem tailTrace_304488 : CollatzResearch.WordTrace tailWord_304488 prefixEnd_304488 34744155005846649555487 := by
  unfold tailWord_304488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552794860449726627693059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7403726480599635503590745 5552794860449726627693059)
  ·
    refine ⟨8329192290674589941539589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552794860449726627693059 8329192290674589941539589)
    ·
      refine ⟨1561723554501485614038673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8329192290674589941539589 1561723554501485614038673)
      ·
        refine ⟨1171292665876114210529005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1561723554501485614038673 1171292665876114210529005)
        ·
          refine ⟨439234749703542828948377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1171292665876114210529005 439234749703542828948377)
          ·
            refine ⟨329426062277657121711283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439234749703542828948377 329426062277657121711283)
            ·
              refine ⟨494139093416485682566925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329426062277657121711283 494139093416485682566925)
              ·
                refine ⟨185302160031182130962597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494139093416485682566925 185302160031182130962597)
                ·
                  refine ⟨34744155005846649555487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185302160031182130962597 34744155005846649555487)
                  ·
                    rfl

theorem cell22_304488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_304488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304488 prefixEnd_304488 := by exact prefixLift 304488
  have htrace : WordTrace (prefixWord ++ tailWord_304488) baseStart_304488 baseEnd_304488 := by
    simpa [prefixWord, tailWord_304488, baseEnd_304488] using wordTrace_append hprefix tailTrace_304488
  have hstable : (prefixWord ++ tailWord_304488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304488).length < 2 ^ (prefixWord ++ tailWord_304488).sum := by decide
  have hdescent : baseEnd_304488 < baseStart_304488 := by decide
  rcases family_descends (prefixWord ++ tailWord_304488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304501 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_304501 : Nat := 118140960795 + 304501 * 2 ^ 59
def prefixEnd_304501 : Nat := 4983230072969 + 3 ^ 40 * 304501 * 2
def baseEnd_304501 : Nat := 104236915183212248091421

theorem tailTrace_304501 : CollatzResearch.WordTrace tailWord_304501 prefixEnd_304501 104236915183212248091421 := by
  unfold tailWord_304501
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106063869852356475609357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404042579901570983739571 11106063869852356475609357)
  ·
    refine ⟨4164773951194633678353509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11106063869852356475609357 4164773951194633678353509)
    ·
      refine ⟨780895115848993814691283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4164773951194633678353509 780895115848993814691283)
      ·
        refine ⟨1171342673773490722036925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780895115848993814691283 1171342673773490722036925)
        ·
          refine ⟨439253502665059020763847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1171342673773490722036925 439253502665059020763847)
          ·
            refine ⟨658880253997588531145771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439253502665059020763847 658880253997588531145771)
            ·
              refine ⟨988320380996382796718657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658880253997588531145771 988320380996382796718657)
              ·
                refine ⟨741240285747287097538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988320380996382796718657 741240285747287097538993)
                ·
                  refine ⟨555930214310465323154245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741240285747287097538993 555930214310465323154245)
                  ·
                    refine ⟨104236915183212248091421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 555930214310465323154245 104236915183212248091421)
                    ·
                      rfl

theorem cell22_304501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_304501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304501 prefixEnd_304501 := by exact prefixLift 304501
  have htrace : WordTrace (prefixWord ++ tailWord_304501) baseStart_304501 baseEnd_304501 := by
    simpa [prefixWord, tailWord_304501, baseEnd_304501] using wordTrace_append hprefix tailTrace_304501
  have hstable : (prefixWord ++ tailWord_304501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304501).length < 2 ^ (prefixWord ++ tailWord_304501).sum := by decide
  have hdescent : baseEnd_304501 < baseStart_304501 := by decide
  rcases family_descends (prefixWord ++ tailWord_304501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304565 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_304565 : Nat := 118140960795 + 304565 * 2 ^ 59
def prefixEnd_304565 : Nat := 4983230072969 + 3 ^ 40 * 304565 * 2
def baseEnd_304565 : Nat := 104258823691137414491225

theorem tailTrace_304565 : CollatzResearch.WordTrace tailWord_304565 prefixEnd_304565 104258823691137414491225 := by
  unfold tailWord_304565
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108398141620495405939149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7405598761080330270626099 11108398141620495405939149)
  ·
    refine ⟨4165649303107685777227181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11108398141620495405939149 4165649303107685777227181)
    ·
      refine ⟨1562118488665382166460193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4165649303107685777227181 1562118488665382166460193)
      ·
        refine ⟨1171588866499036624845145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562118488665382166460193 1171588866499036624845145)
        ·
          refine ⟨878691649874277468633859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1171588866499036624845145 878691649874277468633859)
          ·
            refine ⟨1318037474811416202950789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878691649874277468633859 1318037474811416202950789)
            ·
              refine ⟨247132026527140538053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1318037474811416202950789 247132026527140538053273)
              ·
                refine ⟨185349019895355403539955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247132026527140538053273 185349019895355403539955)
                ·
                  refine ⟨278023529843033105309933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185349019895355403539955 278023529843033105309933)
                  ·
                    refine ⟨104258823691137414491225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278023529843033105309933 104258823691137414491225)
                    ·
                      rfl

theorem cell22_304565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_304565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304565 prefixEnd_304565 := by exact prefixLift 304565
  have htrace : WordTrace (prefixWord ++ tailWord_304565) baseStart_304565 baseEnd_304565 := by
    simpa [prefixWord, tailWord_304565, baseEnd_304565] using wordTrace_append hprefix tailTrace_304565
  have hstable : (prefixWord ++ tailWord_304565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304565).length < 2 ^ (prefixWord ++ tailWord_304565).sum := by decide
  have hdescent : baseEnd_304565 < baseStart_304565 := by decide
  rcases family_descends (prefixWord ++ tailWord_304565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304696 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_304696 : Nat := 118140960795 + 304696 * 2 ^ 59
def prefixEnd_304696 : Nat := 4983230072969 + 3 ^ 40 * 304696 * 2
def baseEnd_304696 : Nat := 34767889222765579821941

theorem tailTrace_304696 : CollatzResearch.WordTrace tailWord_304696 prefixEnd_304696 34767889222765579821941 := by
  unfold tailWord_304696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556588052072952389478971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7408784069430603185971961 5556588052072952389478971)
  ·
    refine ⟨8334882078109428584218457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556588052072952389478971 8334882078109428584218457)
    ·
      refine ⟨6251161558582071438163843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8334882078109428584218457 6251161558582071438163843)
      ·
        refine ⟨9376742337873107157245765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251161558582071438163843 9376742337873107157245765)
        ·
          refine ⟨1758139188351207591983581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9376742337873107157245765 1758139188351207591983581)
          ·
            refine ⟨659302195631702846993843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1758139188351207591983581 659302195631702846993843)
            ·
              refine ⟨988953293447554270490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659302195631702846993843 988953293447554270490765)
              ·
                refine ⟨370857485042832851434037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988953293447554270490765 370857485042832851434037)
                ·
                  refine ⟨34767889222765579821941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 370857485042832851434037 34767889222765579821941)
                  ·
                    rfl

theorem cell22_304696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_304696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304696 prefixEnd_304696 := by exact prefixLift 304696
  have htrace : WordTrace (prefixWord ++ tailWord_304696) baseStart_304696 baseEnd_304696 := by
    simpa [prefixWord, tailWord_304696, baseEnd_304696] using wordTrace_append hprefix tailTrace_304696
  have hstable : (prefixWord ++ tailWord_304696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304696).length < 2 ^ (prefixWord ++ tailWord_304696).sum := by decide
  have hdescent : baseEnd_304696 < baseStart_304696 := by decide
  rcases family_descends (prefixWord ++ tailWord_304696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304758 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_304758 : Nat := 118140960795 + 304758 * 2 ^ 59
def prefixEnd_304758 : Nat := 4983230072969 + 3 ^ 40 * 304758 * 2
def baseEnd_304758 : Nat := 34774963845116414805211

theorem tailTrace_304758 : CollatzResearch.WordTrace tailWord_304758 prefixEnd_304758 34774963845116414805211 := by
  unfold tailWord_304758
  simp only [CollatzResearch.WordTrace]
  refine ⟨694714839370080585482183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7410291619947526245143285 694714839370080585482183)
  ·
    refine ⟨1042072259055120878223275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 694714839370080585482183 1042072259055120878223275)
    ·
      refine ⟨1563108388582681317334913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042072259055120878223275 1563108388582681317334913)
      ·
        refine ⟨1172331291437010988001185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563108388582681317334913 1172331291437010988001185)
        ·
          refine ⟨879248468577758241000889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172331291437010988001185 879248468577758241000889)
          ·
            refine ⟨659436351433318680750667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879248468577758241000889 659436351433318680750667)
            ·
              refine ⟨989154527149978021126001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659436351433318680750667 989154527149978021126001)
              ·
                refine ⟨741865895362483515844501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989154527149978021126001 741865895362483515844501)
                ·
                  refine ⟨34774963845116414805211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 741865895362483515844501 34774963845116414805211)
                  ·
                    rfl

theorem cell22_304758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_304758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304758 prefixEnd_304758 := by exact prefixLift 304758
  have htrace : WordTrace (prefixWord ++ tailWord_304758) baseStart_304758 baseEnd_304758 := by
    simpa [prefixWord, tailWord_304758, baseEnd_304758] using wordTrace_append hprefix tailTrace_304758
  have hstable : (prefixWord ++ tailWord_304758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304758).length < 2 ^ (prefixWord ++ tailWord_304758).sum := by decide
  have hdescent : baseEnd_304758 < baseStart_304758 := by decide
  rcases family_descends (prefixWord ++ tailWord_304758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_304784 : Nat := 118140960795 + 304784 * 2 ^ 59
def prefixEnd_304784 : Nat := 4983230072969 + 3 ^ 40 * 304784 * 2
def baseEnd_304784 : Nat := 104333791866693843265553

theorem tailTrace_304784 : CollatzResearch.WordTrace tailWord_304784 prefixEnd_304784 104333791866693843265553 := by
  unfold tailWord_304784
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558192863913547904080703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7410923818551397205440937 5558192863913547904080703)
  ·
    refine ⟨8337289295870321856121055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558192863913547904080703 8337289295870321856121055)
    ·
      refine ⟨12505933943805482784181583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337289295870321856121055 12505933943805482784181583)
      ·
        refine ⟨18758900915708224176272375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12505933943805482784181583 18758900915708224176272375)
        ·
          refine ⟨28138351373562336264408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18758900915708224176272375 28138351373562336264408563)
          ·
            refine ⟨42207527060343504396612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28138351373562336264408563 42207527060343504396612845)
            ·
              refine ⟨15827822647628814148729817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42207527060343504396612845 15827822647628814148729817)
              ·
                refine ⟨11870866985721610611547363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15827822647628814148729817 11870866985721610611547363)
                ·
                  refine ⟨17806300478582415917321045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11870866985721610611547363 17806300478582415917321045)
                  ·
                    refine ⟨104333791866693843265553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17806300478582415917321045 104333791866693843265553)
                    ·
                      rfl

theorem cell22_304784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_304784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304784 prefixEnd_304784 := by exact prefixLift 304784
  have htrace : WordTrace (prefixWord ++ tailWord_304784) baseStart_304784 baseEnd_304784 := by
    simpa [prefixWord, tailWord_304784, baseEnd_304784] using wordTrace_append hprefix tailTrace_304784
  have hstable : (prefixWord ++ tailWord_304784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304784).length < 2 ^ (prefixWord ++ tailWord_304784).sum := by decide
  have hdescent : baseEnd_304784 < baseStart_304784 := by decide
  rcases family_descends (prefixWord ++ tailWord_304784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304818 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_304818 : Nat := 118140960795 + 304818 * 2 ^ 59
def prefixEnd_304818 : Nat := 4983230072969 + 3 ^ 40 * 304818 * 2
def baseEnd_304818 : Nat := 104345430761529087915449

theorem tailTrace_304818 : CollatzResearch.WordTrace tailWord_304818 prefixEnd_304818 104345430761529087915449 := by
  unfold tailWord_304818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779406452425979903724777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7411750539802613076599405 2779406452425979903724777)
  ·
    refine ⟨2084554839319484927793583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2779406452425979903724777 2084554839319484927793583)
    ·
      refine ⟨3126832258979227391690375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084554839319484927793583 3126832258979227391690375)
      ·
        refine ⟨4690248388468841087535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126832258979227391690375 4690248388468841087535563)
        ·
          refine ⟨7035372582703261631303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690248388468841087535563 7035372582703261631303345)
          ·
            refine ⟨5276529437027446223477509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7035372582703261631303345 5276529437027446223477509)
            ·
              refine ⟨989349269442646166902033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5276529437027446223477509 989349269442646166902033)
              ·
                refine ⟨742011952081984625176525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989349269442646166902033 742011952081984625176525)
                ·
                  refine ⟨278254482030744234441197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742011952081984625176525 278254482030744234441197)
                  ·
                    refine ⟨104345430761529087915449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278254482030744234441197 104345430761529087915449)
                    ·
                      rfl

theorem cell22_304818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_304818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304818 prefixEnd_304818 := by exact prefixLift 304818
  have htrace : WordTrace (prefixWord ++ tailWord_304818) baseStart_304818 baseEnd_304818 := by
    simpa [prefixWord, tailWord_304818, baseEnd_304818] using wordTrace_append hprefix tailTrace_304818
  have hstable : (prefixWord ++ tailWord_304818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304818).length < 2 ^ (prefixWord ++ tailWord_304818).sum := by decide
  have hdescent : baseEnd_304818 < baseStart_304818 := by decide
  rcases family_descends (prefixWord ++ tailWord_304818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304852 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_304852 : Nat := 118140960795 + 304852 * 2 ^ 59
def prefixEnd_304852 : Nat := 4983230072969 + 3 ^ 40 * 304852 * 2
def baseEnd_304852 : Nat := 104357069656364332565345

theorem tailTrace_304852 : CollatzResearch.WordTrace tailWord_304852 prefixEnd_304852 104357069656364332565345 := by
  unfold tailWord_304852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559432945790371710818405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7412577261053828947757873 5559432945790371710818405)
  ·
    refine ⟨1042393677335694695778451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5559432945790371710818405 1042393677335694695778451)
    ·
      refine ⟨1563590516003542043667677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042393677335694695778451 1563590516003542043667677)
      ·
        refine ⟨586346443501328266375379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1563590516003542043667677 586346443501328266375379)
        ·
          refine ⟨879519665251992399563069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586346443501328266375379 879519665251992399563069)
          ·
            refine ⟨329819874469497149836151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 879519665251992399563069 329819874469497149836151)
            ·
              refine ⟨494729811704245724754227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329819874469497149836151 494729811704245724754227)
              ·
                refine ⟨742094717556368587131341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494729811704245724754227 742094717556368587131341)
                ·
                  refine ⟨278285519083638220174253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742094717556368587131341 278285519083638220174253)
                  ·
                    refine ⟨104357069656364332565345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278285519083638220174253 104357069656364332565345)
                    ·
                      rfl

theorem cell22_304852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_304852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304852 prefixEnd_304852 := by exact prefixLift 304852
  have htrace : WordTrace (prefixWord ++ tailWord_304852) baseStart_304852 baseEnd_304852 := by
    simpa [prefixWord, tailWord_304852, baseEnd_304852] using wordTrace_append hprefix tailTrace_304852
  have hstable : (prefixWord ++ tailWord_304852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304852).length < 2 ^ (prefixWord ++ tailWord_304852).sum := by decide
  have hdescent : baseEnd_304852 < baseStart_304852 := by decide
  rcases family_descends (prefixWord ++ tailWord_304852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304876 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_304876 : Nat := 118140960795 + 304876 * 2 ^ 59
def prefixEnd_304876 : Nat := 4983230072969 + 3 ^ 40 * 304876 * 2
def baseEnd_304876 : Nat := 34788428448945423321757

theorem tailTrace_304876 : CollatzResearch.WordTrace tailWord_304876 prefixEnd_304876 34788428448945423321757 := by
  unfold tailWord_304876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559870621746897760255241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7413160828995863680340321 5559870621746897760255241)
  ·
    refine ⟨4169902966310173320191431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5559870621746897760255241 4169902966310173320191431)
    ·
      refine ⟨6254854449465259980287147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169902966310173320191431 6254854449465259980287147)
      ·
        refine ⟨9382281674197889970430721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254854449465259980287147 9382281674197889970430721)
        ·
          refine ⟨7036711255648417477823041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382281674197889970430721 7036711255648417477823041)
          ·
            refine ⟨5277533441736313108367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036711255648417477823041 5277533441736313108367281)
            ·
              refine ⟨3958150081302234831275461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5277533441736313108367281 3958150081302234831275461)
              ·
                refine ⟨742153140244169030864149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3958150081302234831275461 742153140244169030864149)
                ·
                  refine ⟨34788428448945423321757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 742153140244169030864149 34788428448945423321757)
                  ·
                    rfl

theorem cell22_304876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_304876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304876 prefixEnd_304876 := by exact prefixLift 304876
  have htrace : WordTrace (prefixWord ++ tailWord_304876) baseStart_304876 baseEnd_304876 := by
    simpa [prefixWord, tailWord_304876, baseEnd_304876] using wordTrace_append hprefix tailTrace_304876
  have hstable : (prefixWord ++ tailWord_304876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304876).length < 2 ^ (prefixWord ++ tailWord_304876).sum := by decide
  have hdescent : baseEnd_304876 < baseStart_304876 := by decide
  rcases family_descends (prefixWord ++ tailWord_304876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
