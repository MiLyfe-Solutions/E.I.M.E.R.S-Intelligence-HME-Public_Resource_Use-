import V185TrunkScan23Chunk1040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6162884 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6162884 : Nat := 118140960795 + 6162884 * 2 ^ 59
def prefixEnd_6162884 : Nat := 4983230072969 + 3 ^ 40 * 6162884 * 2
def baseEnd_6162884 : Nat := 1054840569967856973902473

theorem tailTrace_6162884 : CollatzResearch.WordTrace tailWord_6162884 prefixEnd_6162884 1054840569967856973902473 := by
  unfold tailWord_6162884
  simp only [CollatzResearch.WordTrace]
  refine ⟨112389422902465639817787853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149852563869954186423717137 112389422902465639817787853)
  ·
    refine ⟨42146033588424614931670445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112389422902465639817787853 42146033588424614931670445)
    ·
      refine ⟨15804762595659230599376417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42146033588424614931670445 15804762595659230599376417)
      ·
        refine ⟨11853571946744422949532313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15804762595659230599376417 11853571946744422949532313)
        ·
          refine ⟨8890178960058317212149235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11853571946744422949532313 8890178960058317212149235)
          ·
            refine ⟨13335268440087475818223853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890178960058317212149235 13335268440087475818223853)
            ·
              refine ⟨5000725665032803431833945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13335268440087475818223853 5000725665032803431833945)
              ·
                refine ⟨3750544248774602573875459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000725665032803431833945 3750544248774602573875459)
                ·
                  refine ⟨5625816373161903860813189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750544248774602573875459 5625816373161903860813189)
                  ·
                    refine ⟨1054840569967856973902473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5625816373161903860813189 1054840569967856973902473)
                    ·
                      rfl

theorem cell23_6162884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6162884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162884 prefixEnd_6162884 := by exact prefixLift 6162884
  have htrace : WordTrace (prefixWord ++ tailWord_6162884) baseStart_6162884 baseEnd_6162884 := by
    simpa [prefixWord, tailWord_6162884, baseEnd_6162884] using wordTrace_append hprefix tailTrace_6162884
  have hstable : (prefixWord ++ tailWord_6162884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162884).length < 2 ^ (prefixWord ++ tailWord_6162884).sum := by decide
  have hdescent : baseEnd_6162884 < baseStart_6162884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162899 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5]
def baseStart_6162899 : Nat := 118140960795 + 6162899 * 2 ^ 59
def prefixEnd_6162899 : Nat := 4983230072969 + 3 ^ 40 * 6162899 * 2
def baseEnd_6162899 : Nat := 3164529412113388363019849

theorem tailTrace_6162899 : CollatzResearch.WordTrace tailWord_6162899 prefixEnd_6162899 3164529412113388363019849 := by
  unfold tailWord_6162899
  simp only [CollatzResearch.WordTrace]
  refine ⟨224779392899876937197371751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149852928599917958131581167 224779392899876937197371751)
  ·
    refine ⟨337169089349815405796057627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224779392899876937197371751 337169089349815405796057627)
    ·
      refine ⟨505753634024723108694086441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337169089349815405796057627 505753634024723108694086441)
      ·
        refine ⟨379315225518542331520564831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505753634024723108694086441 379315225518542331520564831)
        ·
          refine ⟨568972838277813497280847247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379315225518542331520564831 568972838277813497280847247)
          ·
            refine ⟨853459257416720245921270871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568972838277813497280847247 853459257416720245921270871)
            ·
              refine ⟨1280188886125080368881906307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853459257416720245921270871 1280188886125080368881906307)
              ·
                refine ⟨1920283329187620553322859461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280188886125080368881906307 1920283329187620553322859461)
                ·
                  refine ⟨360053124222678853748036149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920283329187620553322859461 360053124222678853748036149)
                  ·
                    refine ⟨33754980395876142538878389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 360053124222678853748036149 33754980395876142538878389)
                    ·
                      refine ⟨3164529412113388363019849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33754980395876142538878389 3164529412113388363019849)
                      ·
                        rfl

theorem cell23_6162899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_6162899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162899 prefixEnd_6162899 := by exact prefixLift 6162899
  have htrace : WordTrace (prefixWord ++ tailWord_6162899) baseStart_6162899 baseEnd_6162899 := by
    simpa [prefixWord, tailWord_6162899, baseEnd_6162899] using wordTrace_append hprefix tailTrace_6162899
  have hstable : (prefixWord ++ tailWord_6162899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162899).length < 2 ^ (prefixWord ++ tailWord_6162899).sum := by decide
  have hdescent : baseEnd_6162899 < baseStart_6162899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162906 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_6162906 : Nat := 118140960795 + 6162906 * 2 ^ 59
def prefixEnd_6162906 : Nat := 4983230072969 + 3 ^ 40 * 6162906 * 2
def baseEnd_6162906 : Nat := 1054844335492656611877439

theorem tailTrace_6162906 : CollatzResearch.WordTrace tailWord_6162906 prefixEnd_6162906 1054844335492656611877439 := by
  unfold tailWord_6162906
  simp only [CollatzResearch.WordTrace]
  refine ⟨56194912052712894348219143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149853098807234384928584381 56194912052712894348219143)
  ·
    refine ⟨84292368079069341522328715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56194912052712894348219143 84292368079069341522328715)
    ·
      refine ⟨126438552118604012283493073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84292368079069341522328715 126438552118604012283493073)
      ·
        refine ⟨94828914088953009212619805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126438552118604012283493073 94828914088953009212619805)
        ·
          refine ⟨35560842783357378454732427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94828914088953009212619805 35560842783357378454732427)
          ·
            refine ⟨53341264175036067682098641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35560842783357378454732427 53341264175036067682098641)
            ·
              refine ⟨40005948131277050761573981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53341264175036067682098641 40005948131277050761573981)
              ·
                refine ⟨15002230549228894035590243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40005948131277050761573981 15002230549228894035590243)
                ·
                  refine ⟨22503345823843341053385365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002230549228894035590243 22503345823843341053385365)
                  ·
                    refine ⟨1054844335492656611877439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22503345823843341053385365 1054844335492656611877439)
                    ·
                      rfl

theorem cell23_6162906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_6162906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162906 prefixEnd_6162906 := by exact prefixLift 6162906
  have htrace : WordTrace (prefixWord ++ tailWord_6162906) baseStart_6162906 baseEnd_6162906 := by
    simpa [prefixWord, tailWord_6162906, baseEnd_6162906] using wordTrace_append hprefix tailTrace_6162906
  have hstable : (prefixWord ++ tailWord_6162906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162906).length < 2 ^ (prefixWord ++ tailWord_6162906).sum := by decide
  have hdescent : baseEnd_6162906 < baseStart_6162906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162917 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6162917 : Nat := 118140960795 + 6162917 * 2 ^ 59
def prefixEnd_6162917 : Nat := 4983230072969 + 3 ^ 40 * 6162917 * 2
def baseEnd_6162917 : Nat := 3164538654765169292594767

theorem tailTrace_6162917 : CollatzResearch.WordTrace tailWord_6162917 prefixEnd_6162917 3164538654765169292594767 := by
  unfold tailWord_6162917
  simp only [CollatzResearch.WordTrace]
  refine ⟨224780049413811726271527005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149853366275874484181018003 224780049413811726271527005)
  ·
    refine ⟨84292518530179397351822627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224780049413811726271527005 84292518530179397351822627)
    ·
      refine ⟨126438777795269096027733941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84292518530179397351822627 126438777795269096027733941)
      ·
        refine ⟨11853635418306477752600057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126438777795269096027733941 11853635418306477752600057)
        ·
          refine ⟨8890226563729858314450043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11853635418306477752600057 8890226563729858314450043)
          ·
            refine ⟨13335339845594787471675065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890226563729858314450043 13335339845594787471675065)
            ·
              refine ⟨10001504884196090603756299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335339845594787471675065 10001504884196090603756299)
              ·
                refine ⟨15002257326294135905634449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001504884196090603756299 15002257326294135905634449)
                ·
                  refine ⟨11251692994720601929225837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15002257326294135905634449 11251692994720601929225837)
                  ·
                    refine ⟨4219384873020225723459689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11251692994720601929225837 4219384873020225723459689)
                    ·
                      refine ⟨3164538654765169292594767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219384873020225723459689 3164538654765169292594767)
                      ·
                        rfl

theorem cell23_6162917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6162917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162917 prefixEnd_6162917 := by exact prefixLift 6162917
  have htrace : WordTrace (prefixWord ++ tailWord_6162917) baseStart_6162917 baseEnd_6162917 := by
    simpa [prefixWord, tailWord_6162917, baseEnd_6162917] using wordTrace_append hprefix tailTrace_6162917
  have hstable : (prefixWord ++ tailWord_6162917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162917).length < 2 ^ (prefixWord ++ tailWord_6162917).sum := by decide
  have hdescent : baseEnd_6162917 < baseStart_6162917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162947 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 1, 2, 2]
def baseStart_6162947 : Nat := 118140960795 + 6162947 * 2 ^ 59
def prefixEnd_6162947 : Nat := 4983230072969 + 3 ^ 40 * 6162947 * 2
def baseEnd_6162947 : Nat := 3164554059184804175219629

theorem tailTrace_6162947 : CollatzResearch.WordTrace tailWord_6162947 prefixEnd_6162947 3164554059184804175219629 := by
  unfold tailWord_6162947
  simp only [CollatzResearch.WordTrace]
  refine ⟨224781143603703041395119095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149854095735802027596746063 224781143603703041395119095)
  ·
    refine ⟨337171715405554562092678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224781143603703041395119095 337171715405554562092678643)
    ·
      refine ⟨505757573108331843139017965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337171715405554562092678643 505757573108331843139017965)
      ·
        refine ⟨189659089915624441177131737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505757573108331843139017965 189659089915624441177131737)
        ·
          refine ⟨142244317436718330882848803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189659089915624441177131737 142244317436718330882848803)
          ·
            refine ⟨213366476155077496324273205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142244317436718330882848803 213366476155077496324273205)
            ·
              refine ⟨20003107139538515280400613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213366476155077496324273205 20003107139538515280400613)
              ·
                refine ⟨3750582588663471615075115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20003107139538515280400613 3750582588663471615075115)
                ·
                  refine ⟨5625873882995207422612673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750582588663471615075115 5625873882995207422612673)
                  ·
                    refine ⟨4219405412246405566959505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5625873882995207422612673 4219405412246405566959505)
                    ·
                      refine ⟨3164554059184804175219629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219405412246405566959505 3164554059184804175219629)
                      ·
                        rfl

theorem cell23_6162947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_6162947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162947 prefixEnd_6162947 := by exact prefixLift 6162947
  have htrace : WordTrace (prefixWord ++ tailWord_6162947) baseStart_6162947 baseEnd_6162947 := by
    simpa [prefixWord, tailWord_6162947, baseEnd_6162947] using wordTrace_append hprefix tailTrace_6162947
  have hstable : (prefixWord ++ tailWord_6162947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162947).length < 2 ^ (prefixWord ++ tailWord_6162947).sum := by decide
  have hdescent : baseEnd_6162947 < baseStart_6162947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162957 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6162957 : Nat := 118140960795 + 6162957 * 2 ^ 59
def prefixEnd_6162957 : Nat := 4983230072969 + 3 ^ 40 * 6162957 * 2
def baseEnd_6162957 : Nat := 1054853064663783045364861

theorem tailTrace_6162957 : CollatzResearch.WordTrace tailWord_6162957 prefixEnd_6162957 1054853064663783045364861 := by
  unfold tailWord_6162957
  simp only [CollatzResearch.WordTrace]
  refine ⟨224781508333666813102983125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149854338889111208735322083 224781508333666813102983125)
  ·
    refine ⟨5268316601570315932101167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 224781508333666813102983125 5268316601570315932101167)
    ·
      refine ⟨7902474902355473898151751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268316601570315932101167 7902474902355473898151751)
      ·
        refine ⟨11853712353533210847227627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902474902355473898151751 11853712353533210847227627)
        ·
          refine ⟨17780568530299816270841441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853712353533210847227627 17780568530299816270841441)
          ·
            refine ⟨13335426397724862203131081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17780568530299816270841441 13335426397724862203131081)
            ·
              refine ⟨10001569798293646652348311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335426397724862203131081 10001569798293646652348311)
              ·
                refine ⟨15002354697440469978522467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001569798293646652348311 15002354697440469978522467)
                ·
                  refine ⟨22503532046160704967783701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002354697440469978522467 22503532046160704967783701)
                  ·
                    refine ⟨1054853064663783045364861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22503532046160704967783701 1054853064663783045364861)
                    ·
                      rfl

theorem cell23_6162957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6162957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162957 prefixEnd_6162957 := by exact prefixLift 6162957
  have htrace : WordTrace (prefixWord ++ tailWord_6162957) baseStart_6162957 baseEnd_6162957 := by
    simpa [prefixWord, tailWord_6162957, baseEnd_6162957] using wordTrace_append hprefix tailTrace_6162957
  have hstable : (prefixWord ++ tailWord_6162957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162957).length < 2 ^ (prefixWord ++ tailWord_6162957).sum := by decide
  have hdescent : baseEnd_6162957 < baseStart_6162957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162963 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3]
def baseStart_6162963 : Nat := 118140960795 + 6162963 * 2 ^ 59
def prefixEnd_6162963 : Nat := 4983230072969 + 3 ^ 40 * 6162963 * 2
def baseEnd_6162963 : Nat := 3164562274875276112619555

theorem tailTrace_6162963 : CollatzResearch.WordTrace tailWord_6162963 prefixEnd_6162963 3164562274875276112619555 := by
  unfold tailWord_6162963
  simp only [CollatzResearch.WordTrace]
  refine ⟨224781727171645076127701543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149854484781096717418467695 224781727171645076127701543)
  ·
    refine ⟨337172590757467614191552315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224781727171645076127701543 337172590757467614191552315)
    ·
      refine ⟨505758886136201421287328473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337172590757467614191552315 505758886136201421287328473)
      ·
        refine ⟨379319164602151065965496355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505758886136201421287328473 379319164602151065965496355)
        ·
          refine ⟨568978746903226598948244533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379319164602151065965496355 568978746903226598948244533)
          ·
            refine ⟨53341757522177493651397925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 568978746903226598948244533 53341757522177493651397925)
            ·
              refine ⟨10001579535408280059637111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53341757522177493651397925 10001579535408280059637111)
              ·
                refine ⟨15002369303112420089455667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001579535408280059637111 15002369303112420089455667)
                ·
                  refine ⟨22503553954668630134183501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002369303112420089455667 22503553954668630134183501)
                  ·
                    refine ⟨8438832733000736300318813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22503553954668630134183501 8438832733000736300318813)
                    ·
                      refine ⟨3164562274875276112619555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438832733000736300318813 3164562274875276112619555)
                      ·
                        rfl

theorem cell23_6162963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_6162963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162963 prefixEnd_6162963 := by exact prefixLift 6162963
  have htrace : WordTrace (prefixWord ++ tailWord_6162963) baseStart_6162963 baseEnd_6162963 := by
    simpa [prefixWord, tailWord_6162963, baseEnd_6162963] using wordTrace_append hprefix tailTrace_6162963
  have hstable : (prefixWord ++ tailWord_6162963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162963).length < 2 ^ (prefixWord ++ tailWord_6162963).sum := by decide
  have hdescent : baseEnd_6162963 < baseStart_6162963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162964 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6162964 : Nat := 118140960795 + 6162964 * 2 ^ 59
def prefixEnd_6162964 : Nat := 4983230072969 + 3 ^ 40 * 6162964 * 2
def baseEnd_6162964 : Nat := 3164562788355930608707051

theorem tailTrace_6162964 : CollatzResearch.WordTrace tailWord_6162964 prefixEnd_6162964 3164562788355930608707051 := by
  unfold tailWord_6162964
  simp only [CollatzResearch.WordTrace]
  refine ⟨112390881822320726649243973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149854509096427635532325297 112390881822320726649243973)
  ·
    refine ⟨21073290341685136246733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112390881822320726649243973 21073290341685136246733245)
    ·
      refine ⟨7902483878131926092524967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21073290341685136246733245 7902483878131926092524967)
      ·
        refine ⟨11853725817197889138787451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902483878131926092524967 11853725817197889138787451)
        ·
          refine ⟨17780588725796833708181177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853725817197889138787451 17780588725796833708181177)
          ·
            refine ⟨13335441544347625281135883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17780588725796833708181177 13335441544347625281135883)
            ·
              refine ⟨20003162316521437921703825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335441544347625281135883 20003162316521437921703825)
              ·
                refine ⟨15002371737391078441277869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20003162316521437921703825 15002371737391078441277869)
                ·
                  refine ⟨5625889401521654415479201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15002371737391078441277869 5625889401521654415479201)
                  ·
                    refine ⟨4219417051141240811609401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5625889401521654415479201 4219417051141240811609401)
                    ·
                      refine ⟨3164562788355930608707051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219417051141240811609401 3164562788355930608707051)
                      ·
                        rfl

theorem cell23_6162964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6162964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162964 prefixEnd_6162964 := by exact prefixLift 6162964
  have htrace : WordTrace (prefixWord ++ tailWord_6162964) baseStart_6162964 baseEnd_6162964 := by
    simpa [prefixWord, tailWord_6162964, baseEnd_6162964] using wordTrace_append hprefix tailTrace_6162964
  have hstable : (prefixWord ++ tailWord_6162964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162964).length < 2 ^ (prefixWord ++ tailWord_6162964).sum := by decide
  have hdescent : baseEnd_6162964 < baseStart_6162964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6162984 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6162984 : Nat := 118140960795 + 6162984 * 2 ^ 59
def prefixEnd_6162984 : Nat := 4983230072969 + 3 ^ 40 * 6162984 * 2
def baseEnd_6162984 : Nat := 3164573057969020530456959

theorem tailTrace_6162984 : CollatzResearch.WordTrace tailWord_6162984 prefixEnd_6162984 3164573057969020530456959 := by
  unfold tailWord_6162984
  simp only [CollatzResearch.WordTrace]
  refine ⟨112391246552284498357108003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149854995403045997809477337 112391246552284498357108003)
  ·
    refine ⟨168586869828426747535662005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112391246552284498357108003 168586869828426747535662005)
    ·
      refine ⟨15805019046415007581468313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168586869828426747535662005 15805019046415007581468313)
      ·
        refine ⟨11853764284811255686101235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15805019046415007581468313 11853764284811255686101235)
        ·
          refine ⟨17780646427216883529151853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11853764284811255686101235 17780646427216883529151853)
          ·
            refine ⟨6667742410206331323431945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17780646427216883529151853 6667742410206331323431945)
            ·
              refine ⟨5000806807654748492573959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667742410206331323431945 5000806807654748492573959)
              ·
                refine ⟨7501210211482122738860939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000806807654748492573959 7501210211482122738860939)
                ·
                  refine ⟨11251815317223184108291409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501210211482122738860939 11251815317223184108291409)
                  ·
                    refine ⟨8438861487917388081218557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11251815317223184108291409 8438861487917388081218557)
                    ·
                      refine ⟨3164573057969020530456959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438861487917388081218557 3164573057969020530456959)
                      ·
                        rfl

theorem cell23_6162984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6162984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6162984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6162984 prefixEnd_6162984 := by exact prefixLift 6162984
  have htrace : WordTrace (prefixWord ++ tailWord_6162984) baseStart_6162984 baseEnd_6162984 := by
    simpa [prefixWord, tailWord_6162984, baseEnd_6162984] using wordTrace_append hprefix tailTrace_6162984
  have hstable : (prefixWord ++ tailWord_6162984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6162984).length < 2 ^ (prefixWord ++ tailWord_6162984).sum := by decide
  have hdescent : baseEnd_6162984 < baseStart_6162984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6162984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163014 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6163014 : Nat := 118140960795 + 6163014 * 2 ^ 59
def prefixEnd_6163014 : Nat := 4983230072969 + 3 ^ 40 * 6163014 * 2
def baseEnd_6163014 : Nat := 3164588462388655413081821

theorem tailTrace_6163014 : CollatzResearch.WordTrace tailWord_6163014 prefixEnd_6163014 3164588462388655413081821 := by
  unfold tailWord_6163014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024487102951884744931503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149855724862973541225205397 7024487102951884744931503)
  ·
    refine ⟨10536730654427827117397255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7024487102951884744931503 10536730654427827117397255)
    ·
      refine ⟨15805095981641740676095883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10536730654427827117397255 15805095981641740676095883)
      ·
        refine ⟨23707643972462611014143825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805095981641740676095883 23707643972462611014143825)
        ·
          refine ⟨17780732979346958260607869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23707643972462611014143825 17780732979346958260607869)
          ·
            refine ⟨6667774867255109347727951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17780732979346958260607869 6667774867255109347727951)
            ·
              refine ⟨10001662300882664021591927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667774867255109347727951 10001662300882664021591927)
              ·
                refine ⟨15002493451323996032387891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001662300882664021591927 15002493451323996032387891)
                ·
                  refine ⟨22503740176985994048581837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002493451323996032387891 22503740176985994048581837)
                  ·
                    refine ⟨8438902566369747768218189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22503740176985994048581837 8438902566369747768218189)
                    ·
                      refine ⟨3164588462388655413081821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8438902566369747768218189 3164588462388655413081821)
                      ·
                        rfl

theorem cell23_6163014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6163014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163014 prefixEnd_6163014 := by exact prefixLift 6163014
  have htrace : WordTrace (prefixWord ++ tailWord_6163014) baseStart_6163014 baseEnd_6163014 := by
    simpa [prefixWord, tailWord_6163014, baseEnd_6163014] using wordTrace_append hprefix tailTrace_6163014
  have hstable : (prefixWord ++ tailWord_6163014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163014).length < 2 ^ (prefixWord ++ tailWord_6163014).sum := by decide
  have hdescent : baseEnd_6163014 < baseStart_6163014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163073 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6163073 : Nat := 118140960795 + 6163073 * 2 ^ 59
def prefixEnd_6163073 : Nat := 4983230072969 + 3 ^ 40 * 6163073 * 2
def baseEnd_6163073 : Nat := 1054872919249090227414683

theorem tailTrace_6163073 : CollatzResearch.WordTrace tailWord_6163073 prefixEnd_6163073 1054872919249090227414683 := by
  unfold tailWord_6163073
  simp only [CollatzResearch.WordTrace]
  refine ⟨224785739201246564914205873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149857159467497709942803915 224785739201246564914205873)
  ·
    refine ⟨168589304400934923685654405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224785739201246564914205873 168589304400934923685654405)
    ·
      refine ⟨31610494575175298191060201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168589304400934923685654405 31610494575175298191060201)
      ·
        refine ⟨23707870931381473643295151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31610494575175298191060201 23707870931381473643295151)
        ·
          refine ⟨35561806397072210464942727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23707870931381473643295151 35561806397072210464942727)
          ·
            refine ⟨53342709595608315697414091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35561806397072210464942727 53342709595608315697414091)
            ·
              refine ⟨80014064393412473546121137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53342709595608315697414091 80014064393412473546121137)
              ·
                refine ⟨60010548295059355159590853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80014064393412473546121137 60010548295059355159590853)
                ·
                  refine ⟨11251977805323629092423285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60010548295059355159590853 11251977805323629092423285)
                  ·
                    refine ⟨1054872919249090227414683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11251977805323629092423285 1054872919249090227414683)
                    ·
                      rfl

theorem cell23_6163073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6163073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163073 prefixEnd_6163073 := by exact prefixLift 6163073
  have htrace : WordTrace (prefixWord ++ tailWord_6163073) baseStart_6163073 baseEnd_6163073 := by
    simpa [prefixWord, tailWord_6163073, baseEnd_6163073] using wordTrace_append hprefix tailTrace_6163073
  have hstable : (prefixWord ++ tailWord_6163073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163073).length < 2 ^ (prefixWord ++ tailWord_6163073).sum := by decide
  have hdescent : baseEnd_6163073 < baseStart_6163073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163090 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6163090 : Nat := 118140960795 + 6163090 * 2 ^ 59
def prefixEnd_6163090 : Nat := 4983230072969 + 3 ^ 40 * 6163090 * 2
def baseEnd_6163090 : Nat := 1054875828972799038577157

theorem tailTrace_6163090 : CollatzResearch.WordTrace tailWord_6163090 prefixEnd_6163090 1054875828972799038577157 := by
  unfold tailWord_6163090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56196589810546244204393681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149857572828123317878383149 56196589810546244204393681)
  ·
    refine ⟨42147442357909683153295261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56196589810546244204393681 42147442357909683153295261)
    ·
      refine ⟨15805290884216131182485723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42147442357909683153295261 15805290884216131182485723)
      ·
        refine ⟨23707936326324196773728585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805290884216131182485723 23707936326324196773728585)
        ·
          refine ⟨17780952244743147580296439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23707936326324196773728585 17780952244743147580296439)
          ·
            refine ⟨26671428367114721370444659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17780952244743147580296439 26671428367114721370444659)
            ·
              refine ⟨40007142550672082055666989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26671428367114721370444659 40007142550672082055666989)
              ·
                refine ⟨15002678456502030770875121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40007142550672082055666989 15002678456502030770875121)
                ·
                  refine ⟨11252008842376523078156341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15002678456502030770875121 11252008842376523078156341)
                  ·
                    refine ⟨1054875828972799038577157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11252008842376523078156341 1054875828972799038577157)
                    ·
                      rfl

theorem cell23_6163090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6163090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163090 prefixEnd_6163090 := by exact prefixLift 6163090
  have htrace : WordTrace (prefixWord ++ tailWord_6163090) baseStart_6163090 baseEnd_6163090 := by
    simpa [prefixWord, tailWord_6163090, baseEnd_6163090] using wordTrace_append hprefix tailTrace_6163090
  have hstable : (prefixWord ++ tailWord_6163090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163090).length < 2 ^ (prefixWord ++ tailWord_6163090).sum := by decide
  have hdescent : baseEnd_6163090 < baseStart_6163090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163111 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 5]
def baseStart_6163111 : Nat := 118140960795 + 6163111 * 2 ^ 59
def prefixEnd_6163111 : Nat := 4983230072969 + 3 ^ 40 * 6163111 * 2
def baseEnd_6163111 : Nat := 351626474445793503729875

theorem tailTrace_6163111 : CollatzResearch.WordTrace tailWord_6163111 prefixEnd_6163111 351626474445793503729875 := by
  unfold tailWord_6163111
  simp only [CollatzResearch.WordTrace]
  refine ⟨224787125175108897404089187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149858083450072598269392791 224787125175108897404089187)
  ·
    refine ⟨337180687762663346106133781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224787125175108897404089187 337180687762663346106133781)
    ·
      refine ⟨15805344738874844348725021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 337180687762663346106133781 15805344738874844348725021)
      ·
        refine ⟨5927004277078066630771883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15805344738874844348725021 5927004277078066630771883)
        ·
          refine ⟨8890506415617099946157825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927004277078066630771883 8890506415617099946157825)
          ·
            refine ⟨6667879811712824959618369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8890506415617099946157825 6667879811712824959618369)
            ·
              refine ⟨5000909858784618719713777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667879811712824959618369 5000909858784618719713777)
              ·
                refine ⟨3750682394088464039785333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000909858784618719713777 3750682394088464039785333)
                ·
                  refine ⟨351626474445793503729875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750682394088464039785333 351626474445793503729875)
                  ·
                    rfl

theorem cell23_6163111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 5].length) (baseStart_6163111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163111 prefixEnd_6163111 := by exact prefixLift 6163111
  have htrace : WordTrace (prefixWord ++ tailWord_6163111) baseStart_6163111 baseEnd_6163111 := by
    simpa [prefixWord, tailWord_6163111, baseEnd_6163111] using wordTrace_append hprefix tailTrace_6163111
  have hstable : (prefixWord ++ tailWord_6163111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163111).length < 2 ^ (prefixWord ++ tailWord_6163111).sum := by decide
  have hdescent : baseEnd_6163111 < baseStart_6163111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163127 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_6163127 : Nat := 118140960795 + 6163127 * 2 ^ 59
def prefixEnd_6163127 : Nat := 4983230072969 + 3 ^ 40 * 6163127 * 2
def baseEnd_6163127 : Nat := 3164646485702613470968801

theorem tailTrace_6163127 : CollatzResearch.WordTrace tailWord_6163127 prefixEnd_6163127 3164646485702613470968801 := by
  unfold tailWord_6163127
  simp only [CollatzResearch.WordTrace]
  refine ⟨224787708743050932136671635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149858472495367288091114423 224787708743050932136671635)
  ·
    refine ⟨337181563114576398205007453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224787708743050932136671635 337181563114576398205007453)
    ·
      refine ⟨126443086167966149326877795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337181563114576398205007453 126443086167966149326877795)
      ·
        refine ⟨189664629251949223990316693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126443086167966149326877795 189664629251949223990316693)
        ·
          refine ⟨8890529496185119874546095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 189664629251949223990316693 8890529496185119874546095)
          ·
            refine ⟨13335794244277679811819143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890529496185119874546095 13335794244277679811819143)
            ·
              refine ⟨20003691366416519717728715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13335794244277679811819143 20003691366416519717728715)
              ·
                refine ⟨30005537049624779576593073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20003691366416519717728715 30005537049624779576593073)
                ·
                  refine ⟨22504152787218584682444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30005537049624779576593073 22504152787218584682444805)
                  ·
                    refine ⟨4219528647603484627958401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22504152787218584682444805 4219528647603484627958401)
                    ·
                      refine ⟨3164646485702613470968801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219528647603484627958401 3164646485702613470968801)
                      ·
                        rfl

theorem cell23_6163127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_6163127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163127 prefixEnd_6163127 := by exact prefixLift 6163127
  have htrace : WordTrace (prefixWord ++ tailWord_6163127) baseStart_6163127 baseEnd_6163127 := by
    simpa [prefixWord, tailWord_6163127, baseEnd_6163127] using wordTrace_append hprefix tailTrace_6163127
  have hstable : (prefixWord ++ tailWord_6163127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163127).length < 2 ^ (prefixWord ++ tailWord_6163127).sum := by decide
  have hdescent : baseEnd_6163127 < baseStart_6163127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163143 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_6163143 : Nat := 118140960795 + 6163143 * 2 ^ 59
def prefixEnd_6163143 : Nat := 4983230072969 + 3 ^ 40 * 6163143 * 2
def baseEnd_6163143 : Nat := 3164654701393085408368727

theorem tailTrace_6163143 : CollatzResearch.WordTrace tailWord_6163143 prefixEnd_6163143 3164654701393085408368727 := by
  unfold tailWord_6163143
  simp only [CollatzResearch.WordTrace]
  refine ⟨224788292310992966869254083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149858861540661977912836055 224788292310992966869254083)
  ·
    refine ⟨337182438466489450303881125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224788292310992966869254083 337182438466489450303881125)
    ·
      refine ⟨63221707212466771931977711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337182438466489450303881125 63221707212466771931977711)
      ·
        refine ⟨94832560818700157897966567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63221707212466771931977711 94832560818700157897966567)
        ·
          refine ⟨142248841228050236846949851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94832560818700157897966567 142248841228050236846949851)
          ·
            refine ⟨213373261842075355270424777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142248841228050236846949851 213373261842075355270424777)
            ·
              refine ⟨160029946381556516452818583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213373261842075355270424777 160029946381556516452818583)
              ·
                refine ⟨240044919572334774679227875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160029946381556516452818583 240044919572334774679227875)
                ·
                  refine ⟨360067379358502162018841813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240044919572334774679227875 360067379358502162018841813)
                  ·
                    refine ⟨8439079203714894422316605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 360067379358502162018841813 8439079203714894422316605)
                    ·
                      refine ⟨3164654701393085408368727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439079203714894422316605 3164654701393085408368727)
                      ·
                        rfl

theorem cell23_6163143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_6163143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163143 prefixEnd_6163143 := by exact prefixLift 6163143
  have htrace : WordTrace (prefixWord ++ tailWord_6163143) baseStart_6163143 baseEnd_6163143 := by
    simpa [prefixWord, tailWord_6163143, baseEnd_6163143] using wordTrace_append hprefix tailTrace_6163143
  have hstable : (prefixWord ++ tailWord_6163143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163143).length < 2 ^ (prefixWord ++ tailWord_6163143).sum := by decide
  have hdescent : baseEnd_6163143 < baseStart_6163143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5]
def baseStart_6163203 : Nat := 118140960795 + 6163203 * 2 ^ 59
def prefixEnd_6163203 : Nat := 4983230072969 + 3 ^ 40 * 6163203 * 2
def baseEnd_6163203 : Nat := 3164685510232355173618451

theorem tailTrace_6163203 : CollatzResearch.WordTrace tailWord_6163203 prefixEnd_6163203 3164685510232355173618451 := by
  unfold tailWord_6163203
  simp only [CollatzResearch.WordTrace]
  refine ⟨224790480690775597116438263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149860320460517064744292175 224790480690775597116438263)
  ·
    refine ⟨337185721036163395674657395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224790480690775597116438263 337185721036163395674657395)
    ·
      refine ⟨505778581554245093511986093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337185721036163395674657395 505778581554245093511986093)
      ·
        refine ⟨189666968082841910066994785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505778581554245093511986093 189666968082841910066994785)
        ·
          refine ⟨142250226062131432550246089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189666968082841910066994785 142250226062131432550246089)
          ·
            refine ⟨106687669546598574412684567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142250226062131432550246089 106687669546598574412684567)
            ·
              refine ⟨160031504319897861619026851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106687669546598574412684567 160031504319897861619026851)
              ·
                refine ⟨240047256479846792428540277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160031504319897861619026851 240047256479846792428540277)
                ·
                  refine ⟨22504430294985636790175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240047256479846792428540277 22504430294985636790175651)
                  ·
                    refine ⟨33756645442478455185263477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22504430294985636790175651 33756645442478455185263477)
                    ·
                      refine ⟨3164685510232355173618451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33756645442478455185263477 3164685510232355173618451)
                      ·
                        rfl

theorem cell23_6163203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_6163203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163203 prefixEnd_6163203 := by exact prefixLift 6163203
  have htrace : WordTrace (prefixWord ++ tailWord_6163203) baseStart_6163203 baseEnd_6163203 := by
    simpa [prefixWord, tailWord_6163203, baseEnd_6163203] using wordTrace_append hprefix tailTrace_6163203
  have hstable : (prefixWord ++ tailWord_6163203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163203).length < 2 ^ (prefixWord ++ tailWord_6163203).sum := by decide
  have hdescent : baseEnd_6163203 < baseStart_6163203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163210 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_6163210 : Nat := 118140960795 + 6163210 * 2 ^ 59
def prefixEnd_6163210 : Nat := 4983230072969 + 3 ^ 40 * 6163210 * 2
def baseEnd_6163210 : Nat := 1054896368198978882076973

theorem tailTrace_6163210 : CollatzResearch.WordTrace tailWord_6163210 prefixEnd_6163210 1054896368198978882076973 := by
  unfold tailWord_6163210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56197684000437559327985771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149860490667833491541295389 56197684000437559327985771)
  ·
    refine ⟨84296526000656338991978657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56197684000437559327985771 84296526000656338991978657)
    ·
      refine ⟨63222394500492254243983993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84296526000656338991978657 63222394500492254243983993)
      ·
        refine ⟨47416795875369190682987995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63222394500492254243983993 47416795875369190682987995)
        ·
          refine ⟨71125193813053786024481993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47416795875369190682987995 71125193813053786024481993)
          ·
            refine ⟨53343895359790339518361495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71125193813053786024481993 53343895359790339518361495)
            ·
              refine ⟨80015843039685509277542243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53343895359790339518361495 80015843039685509277542243)
              ·
                refine ⟨120023764559528263916313365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80015843039685509277542243 120023764559528263916313365)
                ·
                  refine ⟨5626113963727887371077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120023764559528263916313365 5626113963727887371077189)
                  ·
                    refine ⟨1054896368198978882076973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626113963727887371077189 1054896368198978882076973)
                    ·
                      rfl

theorem cell23_6163210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_6163210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163210 prefixEnd_6163210 := by exact prefixLift 6163210
  have htrace : WordTrace (prefixWord ++ tailWord_6163210) baseStart_6163210 baseEnd_6163210 := by
    simpa [prefixWord, tailWord_6163210, baseEnd_6163210] using wordTrace_append hprefix tailTrace_6163210
  have hstable : (prefixWord ++ tailWord_6163210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163210).length < 2 ^ (prefixWord ++ tailWord_6163210).sum := by decide
  have hdescent : baseEnd_6163210 < baseStart_6163210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163217 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_6163217 : Nat := 118140960795 + 6163217 * 2 ^ 59
def prefixEnd_6163217 : Nat := 4983230072969 + 3 ^ 40 * 6163217 * 2
def baseEnd_6163217 : Nat := 3164692698961518118843387

theorem tailTrace_6163217 : CollatzResearch.WordTrace tailWord_6163217 prefixEnd_6163217 3164692698961518118843387 := by
  unfold tailWord_6163217
  simp only [CollatzResearch.WordTrace]
  refine ⟨224790991312724877507447905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149860660875149918338298603 224790991312724877507447905)
  ·
    refine ⟨168593243484543658130585929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224790991312724877507447905 168593243484543658130585929)
    ·
      refine ⟨126444932613407743597939447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168593243484543658130585929 126444932613407743597939447)
      ·
        refine ⟨189667398920111615396909171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126444932613407743597939447 189667398920111615396909171)
        ·
          refine ⟨284501098380167423095363757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189667398920111615396909171 284501098380167423095363757)
          ·
            refine ⟨106687911892562783660761409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284501098380167423095363757 106687911892562783660761409)
            ·
              refine ⟨80015933919422087745571057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106687911892562783660761409 80015933919422087745571057)
              ·
                refine ⟨60011950439566565809178293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80015933919422087745571057 60011950439566565809178293)
                ·
                  refine ⟨5626120353709365544610465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60011950439566565809178293 5626120353709365544610465)
                  ·
                    refine ⟨4219590265282024158457849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626120353709365544610465 4219590265282024158457849)
                    ·
                      refine ⟨3164692698961518118843387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219590265282024158457849 3164692698961518118843387)
                      ·
                        rfl

theorem cell23_6163217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_6163217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163217 prefixEnd_6163217 := by exact prefixLift 6163217
  have htrace : WordTrace (prefixWord ++ tailWord_6163217) baseStart_6163217 baseEnd_6163217 := by
    simpa [prefixWord, tailWord_6163217, baseEnd_6163217] using wordTrace_append hprefix tailTrace_6163217
  have hstable : (prefixWord ++ tailWord_6163217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163217).length < 2 ^ (prefixWord ++ tailWord_6163217).sum := by decide
  have hdescent : baseEnd_6163217 < baseStart_6163217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163240 : List Nat := [2, 1, 5, 1, 1, 1, 4, 8]
def baseStart_6163240 : Nat := 118140960795 + 6163240 * 2 ^ 59
def prefixEnd_6163240 : Nat := 4983230072969 + 3 ^ 40 * 6163240 * 2
def baseEnd_6163240 : Nat := 117211278111724871439103

theorem tailTrace_6163240 : CollatzResearch.WordTrace tailWord_6163240 prefixEnd_6163240 117211278111724871439103 := by
  unfold tailWord_6163240
  simp only [CollatzResearch.WordTrace]
  refine ⟨112395915095820776217767587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149861220127761034957023449 112395915095820776217767587)
  ·
    refine ⟨168593872643731164326651381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112395915095820776217767587 168593872643731164326651381)
    ·
      refine ⟨15805675560349796655623567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168593872643731164326651381 15805675560349796655623567)
      ·
        refine ⟨23708513340524694983435351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805675560349796655623567 23708513340524694983435351)
        ·
          refine ⟨35562770010787042475153027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23708513340524694983435351 35562770010787042475153027)
          ·
            refine ⟨53344155016180563712729541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35562770010787042475153027 53344155016180563712729541)
            ·
              refine ⟨10002029065533855696136789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53344155016180563712729541 10002029065533855696136789)
              ·
                refine ⟨117211278111724871439103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10002029065533855696136789 117211278111724871439103)
                ·
                  rfl

theorem cell23_6163240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 8].length) (baseStart_6163240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163240 prefixEnd_6163240 := by exact prefixLift 6163240
  have htrace : WordTrace (prefixWord ++ tailWord_6163240) baseStart_6163240 baseEnd_6163240 := by
    simpa [prefixWord, tailWord_6163240, baseEnd_6163240] using wordTrace_append hprefix tailTrace_6163240
  have hstable : (prefixWord ++ tailWord_6163240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163240).length < 2 ^ (prefixWord ++ tailWord_6163240).sum := by decide
  have hdescent : baseEnd_6163240 < baseStart_6163240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163268 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6163268 : Nat := 118140960795 + 6163268 * 2 ^ 59
def prefixEnd_6163268 : Nat := 4983230072969 + 3 ^ 40 * 6163268 * 2
def baseEnd_6163268 : Nat := 3164718886474897419305653

theorem tailTrace_6163268 : CollatzResearch.WordTrace tailWord_6163268 prefixEnd_6163268 3164718886474897419305653 := by
  unfold tailWord_6163268
  simp only [CollatzResearch.WordTrace]
  refine ⟨112396425717770056608777229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149861900957026742145036305 112396425717770056608777229)
  ·
    refine ⟨42148659644163771228291461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112396425717770056608777229 42148659644163771228291461)
    ·
      refine ⟨7902873683280707105304649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42148659644163771228291461 7902873683280707105304649)
      ·
        refine ⟨5927155262460530328978487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7902873683280707105304649 5927155262460530328978487)
        ·
          refine ⟨8890732893690795493467731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927155262460530328978487 8890732893690795493467731)
          ·
            refine ⟨13336099340536193240201597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890732893690795493467731 13336099340536193240201597)
            ·
              refine ⟨5001037252701072465075599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13336099340536193240201597 5001037252701072465075599)
              ·
                refine ⟨7501555879051608697613399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001037252701072465075599 7501555879051608697613399)
                ·
                  refine ⟨11252333818577413046420099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501555879051608697613399 11252333818577413046420099)
                  ·
                    refine ⟨16878500727866119569630149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11252333818577413046420099 16878500727866119569630149)
                    ·
                      refine ⟨3164718886474897419305653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16878500727866119569630149 3164718886474897419305653)
                      ·
                        rfl

theorem cell23_6163268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6163268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163268 prefixEnd_6163268 := by exact prefixLift 6163268
  have htrace : WordTrace (prefixWord ++ tailWord_6163268) baseStart_6163268 baseEnd_6163268 := by
    simpa [prefixWord, tailWord_6163268, baseEnd_6163268] using wordTrace_append hprefix tailTrace_6163268
  have hstable : (prefixWord ++ tailWord_6163268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163268).length < 2 ^ (prefixWord ++ tailWord_6163268).sum := by decide
  have hdescent : baseEnd_6163268 < baseStart_6163268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163283 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 8]
def baseStart_6163283 : Nat := 118140960795 + 6163283 * 2 ^ 59
def prefixEnd_6163283 : Nat := 4983230072969 + 3 ^ 40 * 6163283 * 2
def baseEnd_6163283 : Nat := 1054908862894904953539361

theorem tailTrace_6163283 : CollatzResearch.WordTrace tailWord_6163283 prefixEnd_6163283 1054908862894904953539361 := by
  unfold tailWord_6163283
  simp only [CollatzResearch.WordTrace]
  refine ⟨224793398530485770779350503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149862265686990513852900335 224793398530485770779350503)
  ·
    refine ⟨337190097795728656169025755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224793398530485770779350503 337190097795728656169025755)
    ·
      refine ⟨505785146693592984253538633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337190097795728656169025755 505785146693592984253538633)
      ·
        refine ⟨379338860020194738190153975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505785146693592984253538633 379338860020194738190153975)
        ·
          refine ⟨569008290030292107285230963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379338860020194738190153975 569008290030292107285230963)
          ·
            refine ⟨853512435045438160927846445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569008290030292107285230963 853512435045438160927846445)
            ·
              refine ⟨320067163142039310347942417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853512435045438160927846445 320067163142039310347942417)
              ·
                refine ⟨240050372356529482760956813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320067163142039310347942417 240050372356529482760956813)
                ·
                  refine ⟨90018889633698556035358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240050372356529482760956813 90018889633698556035358805)
                  ·
                    refine ⟨1054908862894904953539361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90018889633698556035358805 1054908862894904953539361)
                    ·
                      rfl

theorem cell23_6163283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 8].length) (baseStart_6163283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163283 prefixEnd_6163283 := by exact prefixLift 6163283
  have htrace : WordTrace (prefixWord ++ tailWord_6163283) baseStart_6163283 baseEnd_6163283 := by
    simpa [prefixWord, tailWord_6163283, baseEnd_6163283] using wordTrace_append hprefix tailTrace_6163283
  have hstable : (prefixWord ++ tailWord_6163283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163283).length < 2 ^ (prefixWord ++ tailWord_6163283).sum := by decide
  have hdescent : baseEnd_6163283 < baseStart_6163283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163290 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_6163290 : Nat := 118140960795 + 6163290 * 2 ^ 59
def prefixEnd_6163290 : Nat := 4983230072969 + 3 ^ 40 * 6163290 * 2
def baseEnd_6163290 : Nat := 3164730183049296333230551

theorem tailTrace_6163290 : CollatzResearch.WordTrace tailWord_6163290 prefixEnd_6163290 3164730183049296333230551 := by
  unfold tailWord_6163290
  simp only [CollatzResearch.WordTrace]
  refine ⟨56198413460365102743713831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149862435894306940649903549 56198413460365102743713831)
  ·
    refine ⟨84297620190547654115570747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56198413460365102743713831 84297620190547654115570747)
    ·
      refine ⟨126446430285821481173356121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84297620190547654115570747 126446430285821481173356121)
      ·
        refine ⟨94834822714366110880017091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126446430285821481173356121 94834822714366110880017091)
        ·
          refine ⟨142252234071549166320025637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94834822714366110880017091 142252234071549166320025637)
          ·
            refine ⟨26672293888415468685004807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142252234071549166320025637 26672293888415468685004807)
            ·
              refine ⟨40008440832623203027507211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26672293888415468685004807 40008440832623203027507211)
              ·
                refine ⟨60012661248934804541260817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40008440832623203027507211 60012661248934804541260817)
                ·
                  refine ⟨45009495936701103405945613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60012661248934804541260817 45009495936701103405945613)
                  ·
                    refine ⟨16878560976262913777229605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45009495936701103405945613 16878560976262913777229605)
                    ·
                      refine ⟨3164730183049296333230551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16878560976262913777229605 3164730183049296333230551)
                      ·
                        rfl

theorem cell23_6163290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_6163290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163290 prefixEnd_6163290 := by exact prefixLift 6163290
  have htrace : WordTrace (prefixWord ++ tailWord_6163290) baseStart_6163290 baseEnd_6163290 := by
    simpa [prefixWord, tailWord_6163290, baseEnd_6163290] using wordTrace_append hprefix tailTrace_6163290
  have hstable : (prefixWord ++ tailWord_6163290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163290).length < 2 ^ (prefixWord ++ tailWord_6163290).sum := by decide
  have hdescent : baseEnd_6163290 < baseStart_6163290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163300 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_6163300 : Nat := 118140960795 + 6163300 * 2 ^ 59
def prefixEnd_6163300 : Nat := 4983230072969 + 3 ^ 40 * 6163300 * 2
def baseEnd_6163300 : Nat := 1054911772618613764701835

theorem tailTrace_6163300 : CollatzResearch.WordTrace tailWord_6163300 prefixEnd_6163300 1054911772618613764701835 := by
  unfold tailWord_6163300
  simp only [CollatzResearch.WordTrace]
  refine ⟨112397009285712091341359677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149862679047616121788479569 112397009285712091341359677)
  ·
    refine ⟨42148878482142034253009879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112397009285712091341359677 42148878482142034253009879)
    ·
      refine ⟨63223317723213051379514819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42148878482142034253009879 63223317723213051379514819)
      ·
        refine ⟨94834976584819577069272229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63223317723213051379514819 94834976584819577069272229)
        ·
          refine ⟨17781558109653670700488543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94834976584819577069272229 17781558109653670700488543)
          ·
            refine ⟨26672337164480506050732815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17781558109653670700488543 26672337164480506050732815)
            ·
              refine ⟨40008505746720759076099223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26672337164480506050732815 40008505746720759076099223)
              ·
                refine ⟨60012758620081138614148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40008505746720759076099223 60012758620081138614148835)
                ·
                  refine ⟨90019137930121707921223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60012758620081138614148835 90019137930121707921223253)
                  ·
                    refine ⟨1054911772618613764701835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90019137930121707921223253 1054911772618613764701835)
                    ·
                      rfl

theorem cell23_6163300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_6163300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163300 prefixEnd_6163300 := by exact prefixLift 6163300
  have htrace : WordTrace (prefixWord ++ tailWord_6163300) baseStart_6163300 baseEnd_6163300 := by
    simpa [prefixWord, tailWord_6163300, baseEnd_6163300] using wordTrace_append hprefix tailTrace_6163300
  have hstable : (prefixWord ++ tailWord_6163300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163300).length < 2 ^ (prefixWord ++ tailWord_6163300).sum := by decide
  have hdescent : baseEnd_6163300 < baseStart_6163300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163307 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 4, 2]
def baseStart_6163307 : Nat := 118140960795 + 6163307 * 2 ^ 59
def prefixEnd_6163307 : Nat := 4983230072969 + 3 ^ 40 * 6163307 * 2
def baseEnd_6163307 : Nat := 3164738912220422766717973

theorem tailTrace_6163307 : CollatzResearch.WordTrace tailWord_6163307 prefixEnd_6163307 3164738912220422766717973 := by
  unfold tailWord_6163307
  simp only [CollatzResearch.WordTrace]
  refine ⟨224794273882398822878224175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149862849254932548585482783 224794273882398822878224175)
  ·
    refine ⟨337191410823598234317336263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224794273882398822878224175 337191410823598234317336263)
    ·
      refine ⟨505787116235397351476004395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337191410823598234317336263 505787116235397351476004395)
      ·
        refine ⟨758680674353096027214006593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505787116235397351476004395 758680674353096027214006593)
        ·
          refine ⟨569010505764822020410504945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758680674353096027214006593 569010505764822020410504945)
          ·
            refine ⟨426757879323616515307878709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569010505764822020410504945 426757879323616515307878709)
            ·
              refine ⟨40008551186589048310113629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426757879323616515307878709 40008551186589048310113629)
              ·
                refine ⟨15003206694970893116292611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40008551186589048310113629 15003206694970893116292611)
                ·
                  refine ⟨22504810042456339674438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15003206694970893116292611 22504810042456339674438917)
                  ·
                    refine ⟨4219651882960563688957297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22504810042456339674438917 4219651882960563688957297)
                    ·
                      refine ⟨3164738912220422766717973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219651882960563688957297 3164738912220422766717973)
                      ·
                        rfl

theorem cell23_6163307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 4, 2].length) (baseStart_6163307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163307 prefixEnd_6163307 := by exact prefixLift 6163307
  have htrace : WordTrace (prefixWord ++ tailWord_6163307) baseStart_6163307 baseEnd_6163307 := by
    simpa [prefixWord, tailWord_6163307, baseEnd_6163307] using wordTrace_append hprefix tailTrace_6163307
  have hstable : (prefixWord ++ tailWord_6163307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163307).length < 2 ^ (prefixWord ++ tailWord_6163307).sum := by decide
  have hdescent : baseEnd_6163307 < baseStart_6163307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163357 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_6163357 : Nat := 118140960795 + 6163357 * 2 ^ 59
def prefixEnd_6163357 : Nat := 4983230072969 + 3 ^ 40 * 6163357 * 2
def baseEnd_6163357 : Nat := 3164764586253147571092743

theorem tailTrace_6163357 : CollatzResearch.WordTrace tailWord_6163357 prefixEnd_6163357 3164764586253147571092743 := by
  unfold tailWord_6163357
  simp only [CollatzResearch.WordTrace]
  refine ⟨224796097532217681417544325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149864065021478454278362883 224796097532217681417544325)
  ·
    refine ⟨42149268287290815265789561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224796097532217681417544325 42149268287290815265789561)
    ·
      refine ⟨31611951215468111449342171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42149268287290815265789561 31611951215468111449342171)
      ·
        refine ⟨47417926823202167174013257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31611951215468111449342171 47417926823202167174013257)
        ·
          refine ⟨35563445117401625380509943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47417926823202167174013257 35563445117401625380509943)
          ·
            refine ⟨53345167676102438070764915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35563445117401625380509943 53345167676102438070764915)
            ·
              refine ⟨80017751514153657106147373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53345167676102438070764915 80017751514153657106147373)
              ·
                refine ⟨30006656817807621414805265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80017751514153657106147373 30006656817807621414805265)
                ·
                  refine ⟨22504992613355716061103949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30006656817807621414805265 22504992613355716061103949)
                  ·
                    refine ⟨8439372230008393522913981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22504992613355716061103949 8439372230008393522913981)
                    ·
                      refine ⟨3164764586253147571092743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439372230008393522913981 3164764586253147571092743)
                      ·
                        rfl

theorem cell23_6163357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_6163357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163357 prefixEnd_6163357 := by exact prefixLift 6163357
  have htrace : WordTrace (prefixWord ++ tailWord_6163357) baseStart_6163357 baseEnd_6163357 := by
    simpa [prefixWord, tailWord_6163357, baseEnd_6163357] using wordTrace_append hprefix tailTrace_6163357
  have hstable : (prefixWord ++ tailWord_6163357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163357).length < 2 ^ (prefixWord ++ tailWord_6163357).sum := by decide
  have hdescent : baseEnd_6163357 < baseStart_6163357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163360 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_6163360 : Nat := 118140960795 + 6163360 * 2 ^ 59
def prefixEnd_6163360 : Nat := 4983230072969 + 3 ^ 40 * 6163360 * 2
def baseEnd_6163360 : Nat := 1054922042231703686451743

theorem tailTrace_6163360 : CollatzResearch.WordTrace tailWord_6163360 prefixEnd_6163360 1054922042231703686451743 := by
  unfold tailWord_6163360
  simp only [CollatzResearch.WordTrace]
  refine ⟨112398103475603406464951767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149864137967471208619935689 112398103475603406464951767)
  ·
    refine ⟨168597155213405109697427651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112398103475603406464951767 168597155213405109697427651)
    ·
      refine ⟨252895732820107664546141477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168597155213405109697427651 252895732820107664546141477)
      ·
        refine ⟨47417949903770187102401527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252895732820107664546141477 47417949903770187102401527)
        ·
          refine ⟨71126924855655280653602291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47417949903770187102401527 71126924855655280653602291)
          ·
            refine ⟨106690387283482920980403437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71126924855655280653602291 106690387283482920980403437)
            ·
              refine ⟨40008895231306095367651289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106690387283482920980403437 40008895231306095367651289)
              ·
                refine ⟨30006671423479571525738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40008895231306095367651289 30006671423479571525738467)
                ·
                  refine ⟨45010007135219357288607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30006671423479571525738467 45010007135219357288607701)
                  ·
                    refine ⟨1054922042231703686451743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45010007135219357288607701 1054922042231703686451743)
                    ·
                      rfl

theorem cell23_6163360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_6163360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163360 prefixEnd_6163360 := by exact prefixLift 6163360
  have htrace : WordTrace (prefixWord ++ tailWord_6163360) baseStart_6163360 baseEnd_6163360 := by
    simpa [prefixWord, tailWord_6163360, baseEnd_6163360] using wordTrace_append hprefix tailTrace_6163360
  have hstable : (prefixWord ++ tailWord_6163360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163360).length < 2 ^ (prefixWord ++ tailWord_6163360).sum := by decide
  have hdescent : baseEnd_6163360 < baseStart_6163360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163434 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_6163434 : Nat := 118140960795 + 6163434 * 2 ^ 59
def prefixEnd_6163434 : Nat := 4983230072969 + 3 ^ 40 * 6163434 * 2
def baseEnd_6163434 : Nat := 3164804124263543769829889

theorem tailTrace_6163434 : CollatzResearch.WordTrace tailWord_6163434 prefixEnd_6163434 3164804124263543769829889 := by
  unfold tailWord_6163434
  simp only [CollatzResearch.WordTrace]
  refine ⟨56199726488234680892024339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149865937301959149045398237 56199726488234680892024339)
  ·
    refine ⟨84299589732352021338036509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56199726488234680892024339 84299589732352021338036509)
    ·
      refine ⟨31612346149632008001763691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84299589732352021338036509 31612346149632008001763691)
      ·
        refine ⟨47418519224448012002645537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31612346149632008001763691 47418519224448012002645537)
        ·
          refine ⟨35563889418336009001984153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47418519224448012002645537 35563889418336009001984153)
          ·
            refine ⟨26672917063752006751488115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35563889418336009001984153 26672917063752006751488115)
            ·
              refine ⟨40009375595628010127232173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26672917063752006751488115 40009375595628010127232173)
              ·
                refine ⟨15003515848360503797712065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40009375595628010127232173 15003515848360503797712065)
                ·
                  refine ⟨11252636886270377848284049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15003515848360503797712065 11252636886270377848284049)
                  ·
                    refine ⟨8439477664702783386213037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11252636886270377848284049 8439477664702783386213037)
                    ·
                      refine ⟨3164804124263543769829889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439477664702783386213037 3164804124263543769829889)
                      ·
                        rfl

theorem cell23_6163434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_6163434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163434 prefixEnd_6163434 := by exact prefixLift 6163434
  have htrace : WordTrace (prefixWord ++ tailWord_6163434) baseStart_6163434 baseEnd_6163434 := by
    simpa [prefixWord, tailWord_6163434, baseEnd_6163434] using wordTrace_append hprefix tailTrace_6163434
  have hstable : (prefixWord ++ tailWord_6163434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163434).length < 2 ^ (prefixWord ++ tailWord_6163434).sum := by decide
  have hdescent : baseEnd_6163434 < baseStart_6163434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_6163440 : Nat := 118140960795 + 6163440 * 2 ^ 59
def prefixEnd_6163440 : Nat := 4983230072969 + 3 ^ 40 * 6163440 * 2
def baseEnd_6163440 : Nat := 3164807205147470746354861

theorem tailTrace_6163440 : CollatzResearch.WordTrace tailWord_6163440 prefixEnd_6163440 3164807205147470746354861 := by
  unfold tailWord_6163440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112399562395458493296407887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149866083193944657728543849 112399562395458493296407887)
  ·
    refine ⟨168599343593187739944611831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112399562395458493296407887 168599343593187739944611831)
    ·
      refine ⟨252899015389781609916917747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168599343593187739944611831 252899015389781609916917747)
      ·
        refine ⟨379348523084672414875376621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252899015389781609916917747 379348523084672414875376621)
        ·
          refine ⟨142255696156752155578266233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379348523084672414875376621 142255696156752155578266233)
          ·
            refine ⟨106691772117564116683699675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142255696156752155578266233 106691772117564116683699675)
            ·
              refine ⟨160037658176346175025549513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106691772117564116683699675 160037658176346175025549513)
              ·
                refine ⟨120028243632259631269162135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160037658176346175025549513 120028243632259631269162135)
                ·
                  refine ⟨180042365448389446903743203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120028243632259631269162135 180042365448389446903743203)
                  ·
                    refine ⟨270063548172584170355614805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180042365448389446903743203 270063548172584170355614805)
                    ·
                      refine ⟨3164807205147470746354861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 270063548172584170355614805 3164807205147470746354861)
                      ·
                        rfl

theorem cell23_6163440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_6163440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163440 prefixEnd_6163440 := by exact prefixLift 6163440
  have htrace : WordTrace (prefixWord ++ tailWord_6163440) baseStart_6163440 baseEnd_6163440 := by
    simpa [prefixWord, tailWord_6163440, baseEnd_6163440] using wordTrace_append hprefix tailTrace_6163440
  have hstable : (prefixWord ++ tailWord_6163440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163440).length < 2 ^ (prefixWord ++ tailWord_6163440).sum := by decide
  have hdescent : baseEnd_6163440 < baseStart_6163440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163467 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 3, 5]
def baseStart_6163467 : Nat := 118140960795 + 6163467 * 2 ^ 59
def prefixEnd_6163467 : Nat := 4983230072969 + 3 ^ 40 * 6163467 * 2
def baseEnd_6163467 : Nat := 1054940356375047380239079

theorem tailTrace_6163467 : CollatzResearch.WordTrace tailWord_6163467 prefixEnd_6163467 1054940356375047380239079 := by
  unfold tailWord_6163467
  simp only [CollatzResearch.WordTrace]
  refine ⟨224800109561819170204048655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149866739707879446802699103 224800109561819170204048655)
  ·
    refine ⟨337200164342728755306072983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224800109561819170204048655 337200164342728755306072983)
    ·
      refine ⟨505800246514093132959109475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337200164342728755306072983 505800246514093132959109475)
      ·
        refine ⟨758700369771139699438664213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505800246514093132959109475 758700369771139699438664213)
        ·
          refine ⟨35564079833022173411187385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 758700369771139699438664213 35564079833022173411187385)
          ·
            refine ⟨26673059874766630058390539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35564079833022173411187385 26673059874766630058390539)
            ·
              refine ⟨40009589812149945087585809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26673059874766630058390539 40009589812149945087585809)
              ·
                refine ⟨30007192359112458815689357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40009589812149945087585809 30007192359112458815689357)
                ·
                  refine ⟨11252697134667172055883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30007192359112458815689357 11252697134667172055883509)
                  ·
                    refine ⟨1054940356375047380239079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11252697134667172055883509 1054940356375047380239079)
                    ·
                      rfl

theorem cell23_6163467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 5].length) (baseStart_6163467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163467 prefixEnd_6163467 := by exact prefixLift 6163467
  have htrace : WordTrace (prefixWord ++ tailWord_6163467) baseStart_6163467 baseEnd_6163467 := by
    simpa [prefixWord, tailWord_6163467, baseEnd_6163467] using wordTrace_append hprefix tailTrace_6163467
  have hstable : (prefixWord ++ tailWord_6163467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163467).length < 2 ^ (prefixWord ++ tailWord_6163467).sum := by decide
  have hdescent : baseEnd_6163467 < baseStart_6163467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163491 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 2, 3, 2]
def baseStart_6163491 : Nat := 118140960795 + 6163491 * 2 ^ 59
def prefixEnd_6163491 : Nat := 4983230072969 + 3 ^ 40 * 6163491 * 2
def baseEnd_6163491 : Nat := 3164833392660850046817127

theorem tailTrace_6163491 : CollatzResearch.WordTrace tailWord_6163491 prefixEnd_6163491 3164833392660850046817127 := by
  unfold tailWord_6163491
  simp only [CollatzResearch.WordTrace]
  refine ⟨224800984913732222302922327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149867323275821481535281551 224800984913732222302922327)
  ·
    refine ⟨337201477370598333454383491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224800984913732222302922327 337201477370598333454383491)
    ·
      refine ⟨505802216055897500181575237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337201477370598333454383491 505802216055897500181575237)
      ·
        refine ⟨94837915510480781284045357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505802216055897500181575237 94837915510480781284045357)
        ·
          refine ⟨35564218316430292981517009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94837915510480781284045357 35564218316430292981517009)
          ·
            refine ⟨26673163737322719736137757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35564218316430292981517009 26673163737322719736137757)
            ·
              refine ⟨10002436401496019901051659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26673163737322719736137757 10002436401496019901051659)
              ·
                refine ⟨15003654602244029851577489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002436401496019901051659 15003654602244029851577489)
                ·
                  refine ⟨11252740951683022388683117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15003654602244029851577489 11252740951683022388683117)
                  ·
                    refine ⟨4219777856881133395756169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11252740951683022388683117 4219777856881133395756169)
                    ·
                      refine ⟨3164833392660850046817127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219777856881133395756169 3164833392660850046817127)
                      ·
                        rfl

theorem cell23_6163491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_6163491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163491 prefixEnd_6163491 := by exact prefixLift 6163491
  have htrace : WordTrace (prefixWord ++ tailWord_6163491) baseStart_6163491 baseEnd_6163491 := by
    simpa [prefixWord, tailWord_6163491, baseEnd_6163491] using wordTrace_append hprefix tailTrace_6163491
  have hstable : (prefixWord ++ tailWord_6163491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163491).length < 2 ^ (prefixWord ++ tailWord_6163491).sum := by decide
  have hdescent : baseEnd_6163491 < baseStart_6163491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163504 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_6163504 : Nat := 118140960795 + 6163504 * 2 ^ 59
def prefixEnd_6163504 : Nat := 4983230072969 + 3 ^ 40 * 6163504 * 2
def baseEnd_6163504 : Nat := 3164840067909358495954567

theorem tailTrace_6163504 : CollatzResearch.WordTrace tailWord_6163504 prefixEnd_6163504 3164840067909358495954567 := by
  unfold tailWord_6163504
  simp only [CollatzResearch.WordTrace]
  refine ⟨112400729531342562761572783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149867639375123417015430377 112400729531342562761572783)
  ·
    refine ⟨168601094297013844142359175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112400729531342562761572783 168601094297013844142359175)
    ·
      refine ⟨252901641445520766213538763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168601094297013844142359175 252901641445520766213538763)
      ·
        refine ⟨379352462168281149320308145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252901641445520766213538763 379352462168281149320308145)
        ·
          refine ⟨284514346626210861990231109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379352462168281149320308145 284514346626210861990231109)
          ·
            refine ⟨53346439992414536623168333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284514346626210861990231109 53346439992414536623168333)
            ·
              refine ⟨20004914997155451233688125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53346439992414536623168333 20004914997155451233688125)
              ·
                refine ⟨7501843123933294212633047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20004914997155451233688125 7501843123933294212633047)
                ·
                  refine ⟨11252764685899941318949571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501843123933294212633047 11252764685899941318949571)
                  ·
                    refine ⟨16879147028849911978424357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11252764685899941318949571 16879147028849911978424357)
                    ·
                      refine ⟨3164840067909358495954567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16879147028849911978424357 3164840067909358495954567)
                      ·
                        rfl

theorem cell23_6163504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_6163504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163504 prefixEnd_6163504 := by exact prefixLift 6163504
  have htrace : WordTrace (prefixWord ++ tailWord_6163504) baseStart_6163504 baseEnd_6163504 := by
    simpa [prefixWord, tailWord_6163504, baseEnd_6163504] using wordTrace_append hprefix tailTrace_6163504
  have hstable : (prefixWord ++ tailWord_6163504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163504).length < 2 ^ (prefixWord ++ tailWord_6163504).sum := by decide
  have hdescent : baseEnd_6163504 < baseStart_6163504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163507 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_6163507 : Nat := 118140960795 + 6163507 * 2 ^ 59
def prefixEnd_6163507 : Nat := 4983230072969 + 3 ^ 40 * 6163507 * 2
def baseEnd_6163507 : Nat := 3164841608351321984217053

theorem tailTrace_6163507 : CollatzResearch.WordTrace tailWord_6163507 prefixEnd_6163507 3164841608351321984217053 := by
  unfold tailWord_6163507
  simp only [CollatzResearch.WordTrace]
  refine ⟨224801568481674257035504775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149867712321116171357003183 224801568481674257035504775)
  ·
    refine ⟨337202352722511385553257163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224801568481674257035504775 337202352722511385553257163)
    ·
      refine ⟨505803529083767078329885745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337202352722511385553257163 505803529083767078329885745)
      ·
        refine ⟨379352646812825308747414309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505803529083767078329885745 379352646812825308747414309)
        ·
          refine ⟨71128621277404745390140183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379352646812825308747414309 71128621277404745390140183)
          ·
            refine ⟨106692931916107118085210275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71128621277404745390140183 106692931916107118085210275)
            ·
              refine ⟨160039397874160677127815413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106692931916107118085210275 160039397874160677127815413)
              ·
                refine ⟨15003693550702563480732695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160039397874160677127815413 15003693550702563480732695)
                ·
                  refine ⟨22505540326053845221099043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15003693550702563480732695 22505540326053845221099043)
                  ·
                    refine ⟨33758310489080767831648565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22505540326053845221099043 33758310489080767831648565)
                    ·
                      refine ⟨3164841608351321984217053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33758310489080767831648565 3164841608351321984217053)
                      ·
                        rfl

theorem cell23_6163507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_6163507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163507 prefixEnd_6163507 := by exact prefixLift 6163507
  have htrace : WordTrace (prefixWord ++ tailWord_6163507) baseStart_6163507 baseEnd_6163507 := by
    simpa [prefixWord, tailWord_6163507, baseEnd_6163507] using wordTrace_append hprefix tailTrace_6163507
  have hstable : (prefixWord ++ tailWord_6163507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163507).length < 2 ^ (prefixWord ++ tailWord_6163507).sum := by decide
  have hdescent : baseEnd_6163507 < baseStart_6163507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163538 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_6163538 : Nat := 118140960795 + 6163538 * 2 ^ 59
def prefixEnd_6163538 : Nat := 4983230072969 + 3 ^ 40 * 6163538 * 2
def baseEnd_6163538 : Nat := 3164857526251611362929411

theorem tailTrace_6163538 : CollatzResearch.WordTrace tailWord_6163538 prefixEnd_6163538 3164857526251611362929411 := by
  unfold tailWord_6163538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200674786140487332470817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149868466096374632886588845 56200674786140487332470817)
  ·
    refine ⟨42150506089605365499353113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56200674786140487332470817 42150506089605365499353113)
    ·
      refine ⟨31612879567204024124514835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42150506089605365499353113 31612879567204024124514835)
      ·
        refine ⟨47419319350806036186772253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31612879567204024124514835 47419319350806036186772253)
        ·
          refine ⟨17782244756552263570039595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47419319350806036186772253 17782244756552263570039595)
          ·
            refine ⟨26673367134828395355059393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782244756552263570039595 26673367134828395355059393)
            ·
              refine ⟨20005025351121296516294545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26673367134828395355059393 20005025351121296516294545)
              ·
                refine ⟨15003769013340972387220909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20005025351121296516294545 15003769013340972387220909)
                ·
                  refine ⟨5626413380002864645207841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15003769013340972387220909 5626413380002864645207841)
                  ·
                    refine ⟨4219810035002148483905881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626413380002864645207841 4219810035002148483905881)
                    ·
                      refine ⟨3164857526251611362929411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219810035002148483905881 3164857526251611362929411)
                      ·
                        rfl

theorem cell23_6163538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_6163538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163538 prefixEnd_6163538 := by exact prefixLift 6163538
  have htrace : WordTrace (prefixWord ++ tailWord_6163538) baseStart_6163538 baseEnd_6163538 := by
    simpa [prefixWord, tailWord_6163538, baseEnd_6163538] using wordTrace_append hprefix tailTrace_6163538
  have hstable : (prefixWord ++ tailWord_6163538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163538).length < 2 ^ (prefixWord ++ tailWord_6163538).sum := by decide
  have hdescent : baseEnd_6163538 < baseStart_6163538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163541 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6163541 : Nat := 118140960795 + 6163541 * 2 ^ 59
def prefixEnd_6163541 : Nat := 4983230072969 + 3 ^ 40 * 6163541 * 2
def baseEnd_6163541 : Nat := 3164859066693574851191897

theorem tailTrace_6163541 : CollatzResearch.WordTrace tailWord_6163541 prefixEnd_6163541 3164859066693574851191897 := by
  unfold tailWord_6163541
  simp only [CollatzResearch.WordTrace]
  refine ⟨224802808563551080842242477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149868539042367387228161651 224802808563551080842242477)
  ·
    refine ⟨84301053211331655315840929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224802808563551080842242477 84301053211331655315840929)
    ·
      refine ⟨63225789908498741486880697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84301053211331655315840929 63225789908498741486880697)
      ·
        refine ⟨47419342431374056115160523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63225789908498741486880697 47419342431374056115160523)
        ·
          refine ⟨71129013647061084172740785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47419342431374056115160523 71129013647061084172740785)
          ·
            refine ⟨53346760235295813129555589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71129013647061084172740785 53346760235295813129555589)
            ·
              refine ⟨10002517544117964961791673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53346760235295813129555589 10002517544117964961791673)
              ·
                refine ⟨7501888158088473721343755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10002517544117964961791673 7501888158088473721343755)
                ·
                  refine ⟨11252832237132710582015633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501888158088473721343755 11252832237132710582015633)
                  ·
                    refine ⟨8439624177849532936511725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11252832237132710582015633 8439624177849532936511725)
                    ·
                      refine ⟨3164859066693574851191897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439624177849532936511725 3164859066693574851191897)
                      ·
                        rfl

theorem cell23_6163541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6163541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163541 prefixEnd_6163541 := by exact prefixLift 6163541
  have htrace : WordTrace (prefixWord ++ tailWord_6163541) baseStart_6163541 baseEnd_6163541 := by
    simpa [prefixWord, tailWord_6163541, baseEnd_6163541] using wordTrace_append hprefix tailTrace_6163541
  have hstable : (prefixWord ++ tailWord_6163541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163541).length < 2 ^ (prefixWord ++ tailWord_6163541).sum := by decide
  have hdescent : baseEnd_6163541 < baseStart_6163541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163549 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6163549 : Nat := 118140960795 + 6163549 * 2 ^ 59
def prefixEnd_6163549 : Nat := 4983230072969 + 3 ^ 40 * 6163549 * 2
def baseEnd_6163549 : Nat := 3164863174538810819891861

theorem tailTrace_6163549 : CollatzResearch.WordTrace tailWord_6163549 prefixEnd_6163549 3164863174538810819891861 := by
  unfold tailWord_6163549
  simp only [CollatzResearch.WordTrace]
  refine ⟨224803100347522098208533701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149868733565014732139022467 224803100347522098208533701)
  ·
    refine ⟨42150581315160393414100069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224803100347522098208533701 42150581315160393414100069)
    ·
      refine ⟨7903233996592573765143763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42150581315160393414100069 7903233996592573765143763)
      ·
        refine ⟨11854850994888860647715645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903233996592573765143763 11854850994888860647715645)
        ·
          refine ⟨4445569123083322742893367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11854850994888860647715645 4445569123083322742893367)
          ·
            refine ⟨6668353684624984114340051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445569123083322742893367 6668353684624984114340051)
            ·
              refine ⟨10002530526937476171510077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668353684624984114340051 10002530526937476171510077)
              ·
                refine ⟨3750948947601553564316279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10002530526937476171510077 3750948947601553564316279)
                ·
                  refine ⟨5626423421402330346474419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3750948947601553564316279 5626423421402330346474419)
                  ·
                    refine ⟨8439635132103495519711629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626423421402330346474419 8439635132103495519711629)
                    ·
                      refine ⟨3164863174538810819891861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439635132103495519711629 3164863174538810819891861)
                      ·
                        rfl

theorem cell23_6163549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6163549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163549 prefixEnd_6163549 := by exact prefixLift 6163549
  have htrace : WordTrace (prefixWord ++ tailWord_6163549) baseStart_6163549 baseEnd_6163549 := by
    simpa [prefixWord, tailWord_6163549, baseEnd_6163549] using wordTrace_append hprefix tailTrace_6163549
  have hstable : (prefixWord ++ tailWord_6163549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163549).length < 2 ^ (prefixWord ++ tailWord_6163549).sum := by decide
  have hdescent : baseEnd_6163549 < baseStart_6163549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163567 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_6163567 : Nat := 118140960795 + 6163567 * 2 ^ 59
def prefixEnd_6163567 : Nat := 4983230072969 + 3 ^ 40 * 6163567 * 2
def baseEnd_6163567 : Nat := 3164872417190591749466777

theorem tailTrace_6163567 : CollatzResearch.WordTrace tailWord_6163567 prefixEnd_6163567 3164872417190591749466777 := by
  unfold tailWord_6163567
  simp only [CollatzResearch.WordTrace]
  refine ⟨224803756861456887282688955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149869171240971258188459303 224803756861456887282688955)
  ·
    refine ⟨337205635292185330924033433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224803756861456887282688955 337205635292185330924033433)
    ·
      refine ⟨252904226469138998193025075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337205635292185330924033433 252904226469138998193025075)
      ·
        refine ⟨379356339703708497289537613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252904226469138998193025075 379356339703708497289537613)
        ·
          refine ⟨142258627388890686483576605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379356339703708497289537613 142258627388890686483576605)
          ·
            refine ⟨53346985270834007431341227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142258627388890686483576605 53346985270834007431341227)
            ·
              refine ⟨80020477906251011147011841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53346985270834007431341227 80020477906251011147011841)
              ·
                refine ⟨60015358429688258360258881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80020477906251011147011841 60015358429688258360258881)
                ·
                  refine ⟨45011518822266193770194161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60015358429688258360258881 45011518822266193770194161)
                  ·
                    refine ⟨33758639116699645327645621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45011518822266193770194161 33758639116699645327645621)
                    ·
                      refine ⟨3164872417190591749466777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33758639116699645327645621 3164872417190591749466777)
                      ·
                        rfl

theorem cell23_6163567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_6163567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163567 prefixEnd_6163567 := by exact prefixLift 6163567
  have htrace : WordTrace (prefixWord ++ tailWord_6163567) baseStart_6163567 baseEnd_6163567 := by
    simpa [prefixWord, tailWord_6163567, baseEnd_6163567] using wordTrace_append hprefix tailTrace_6163567
  have hstable : (prefixWord ++ tailWord_6163567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163567).length < 2 ^ (prefixWord ++ tailWord_6163567).sum := by decide
  have hdescent : baseEnd_6163567 < baseStart_6163567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163574 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6163574 : Nat := 118140960795 + 6163574 * 2 ^ 59
def prefixEnd_6163574 : Nat := 4983230072969 + 3 ^ 40 * 6163574 * 2
def baseEnd_6163574 : Nat := 1054958670518391074026415

theorem tailTrace_6163574 : CollatzResearch.WordTrace tailWord_6163574 prefixEnd_6163574 1054958670518391074026415 := by
  unfold tailWord_6163574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050250760776970467387111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149869341448287684985462517 14050250760776970467387111)
  ·
    refine ⟨21075376141165455701080667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14050250760776970467387111 21075376141165455701080667)
    ·
      refine ⟨31613064211748183551621001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21075376141165455701080667 31613064211748183551621001)
      ·
        refine ⟨23709798158811137663715751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31613064211748183551621001 23709798158811137663715751)
        ·
          refine ⟨35564697238216706495573627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23709798158811137663715751 35564697238216706495573627)
          ·
            refine ⟨53347045857325059743360441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35564697238216706495573627 53347045857325059743360441)
            ·
              refine ⟨40010284392993794807520331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53347045857325059743360441 40010284392993794807520331)
              ·
                refine ⟨60015426589490692211280497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40010284392993794807520331 60015426589490692211280497)
                ·
                  refine ⟨45011569942118019158460373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60015426589490692211280497 45011569942118019158460373)
                  ·
                    refine ⟨1054958670518391074026415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45011569942118019158460373 1054958670518391074026415)
                    ·
                      rfl

theorem cell23_6163574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6163574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163574 prefixEnd_6163574 := by exact prefixLift 6163574
  have htrace : WordTrace (prefixWord ++ tailWord_6163574) baseStart_6163574 baseEnd_6163574 := by
    simpa [prefixWord, tailWord_6163574, baseEnd_6163574] using wordTrace_append hprefix tailTrace_6163574
  have hstable : (prefixWord ++ tailWord_6163574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163574).length < 2 ^ (prefixWord ++ tailWord_6163574).sum := by decide
  have hdescent : baseEnd_6163574 < baseStart_6163574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163581 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_6163581 : Nat := 118140960795 + 6163581 * 2 ^ 59
def prefixEnd_6163581 : Nat := 4983230072969 + 3 ^ 40 * 6163581 * 2
def baseEnd_6163581 : Nat := 3164879605919754694691713

theorem tailTrace_6163581 : CollatzResearch.WordTrace tailWord_6163581 prefixEnd_6163581 3164879605919754694691713 := by
  unfold tailWord_6163581
  simp only [CollatzResearch.WordTrace]
  refine ⟨224804267483406167673698597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149869511655604111782465731 224804267483406167673698597)
  ·
    refine ⟨42150800153138656438818487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224804267483406167673698597 42150800153138656438818487)
    ·
      refine ⟨63226200229707984658227731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42150800153138656438818487 63226200229707984658227731)
      ·
        refine ⟨94839300344561976987341597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63226200229707984658227731 94839300344561976987341597)
        ·
          refine ⟨35564737629210741370253099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94839300344561976987341597 35564737629210741370253099)
          ·
            refine ⟨53347106443816112055379649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35564737629210741370253099 53347106443816112055379649)
            ·
              refine ⟨40010329832862084041534737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53347106443816112055379649 40010329832862084041534737)
              ·
                refine ⟨30007747374646563031151053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40010329832862084041534737 30007747374646563031151053)
                ·
                  refine ⟨11252905265492461136681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30007747374646563031151053 11252905265492461136681645)
                  ·
                    refine ⟨4219839474559672926255617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11252905265492461136681645 4219839474559672926255617)
                    ·
                      refine ⟨3164879605919754694691713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219839474559672926255617 3164879605919754694691713)
                      ·
                        rfl

theorem cell23_6163581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_6163581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163581 prefixEnd_6163581 := by exact prefixLift 6163581
  have htrace : WordTrace (prefixWord ++ tailWord_6163581) baseStart_6163581 baseEnd_6163581 := by
    simpa [prefixWord, tailWord_6163581, baseEnd_6163581] using wordTrace_append hprefix tailTrace_6163581
  have hstable : (prefixWord ++ tailWord_6163581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163581).length < 2 ^ (prefixWord ++ tailWord_6163581).sum := by decide
  have hdescent : baseEnd_6163581 < baseStart_6163581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163582 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6163582 : Nat := 118140960795 + 6163582 * 2 ^ 59
def prefixEnd_6163582 : Nat := 4983230072969 + 3 ^ 40 * 6163582 * 2
def baseEnd_6163582 : Nat := 1054960039800136396926403

theorem tailTrace_6163582 : CollatzResearch.WordTrace tailWord_6163582 prefixEnd_6163582 1054960039800136396926403 := by
  unfold tailWord_6163582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28100537994550318105560625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149869535970935029896323333 28100537994550318105560625)
  ·
    refine ⟨21075403495912738579170469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28100537994550318105560625 21075403495912738579170469)
    ·
      refine ⟨3951638155483638483594463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21075403495912738579170469 3951638155483638483594463)
      ·
        refine ⟨5927457233225457725391695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951638155483638483594463 5927457233225457725391695)
        ·
          refine ⟨8891185849838186588087543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5927457233225457725391695 8891185849838186588087543)
          ·
            refine ⟨13336778774757279882131315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891185849838186588087543 13336778774757279882131315)
            ·
              refine ⟨20005168162135919823196973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336778774757279882131315 20005168162135919823196973)
              ·
                refine ⟨7501938060800969933698865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20005168162135919823196973 7501938060800969933698865)
                ·
                  refine ⟨5626453545600727450274149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7501938060800969933698865 5626453545600727450274149)
                  ·
                    refine ⟨1054960039800136396926403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626453545600727450274149 1054960039800136396926403)
                    ·
                      rfl

theorem cell23_6163582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6163582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163582 prefixEnd_6163582 := by exact prefixLift 6163582
  have htrace : WordTrace (prefixWord ++ tailWord_6163582) baseStart_6163582 baseEnd_6163582 := by
    simpa [prefixWord, tailWord_6163582, baseEnd_6163582] using wordTrace_append hprefix tailTrace_6163582
  have hstable : (prefixWord ++ tailWord_6163582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163582).length < 2 ^ (prefixWord ++ tailWord_6163582).sum := by decide
  have hdescent : baseEnd_6163582 < baseStart_6163582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163587 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 8]
def baseStart_6163587 : Nat := 118140960795 + 6163587 * 2 ^ 59
def prefixEnd_6163587 : Nat := 4983230072969 + 3 ^ 40 * 6163587 * 2
def baseEnd_6163587 : Nat := 1054960895601227223738895

theorem tailTrace_6163587 : CollatzResearch.WordTrace tailWord_6163587 prefixEnd_6163587 1054960895601227223738895 := by
  unfold tailWord_6163587
  simp only [CollatzResearch.WordTrace]
  refine ⟨224804486321384430698417015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149869657547589620465611343 224804486321384430698417015)
  ·
    refine ⟨337206729482076646047625523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224804486321384430698417015 337206729482076646047625523)
    ·
      refine ⟨505810094223114969071438285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337206729482076646047625523 505810094223114969071438285)
      ·
        refine ⟨189678785333668113401789357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505810094223114969071438285 189678785333668113401789357)
        ·
          refine ⟨71129544500125542525671009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189678785333668113401789357 71129544500125542525671009)
          ·
            refine ⟨53347158375094156894253257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71129544500125542525671009 53347158375094156894253257)
            ·
              refine ⟨40010368781320617670689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53347158375094156894253257 40010368781320617670689943)
              ·
                refine ⟨60015553171980926506034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40010368781320617670689943 60015553171980926506034915)
                ·
                  refine ⟨90023329757971389759052373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60015553171980926506034915 90023329757971389759052373)
                  ·
                    refine ⟨1054960895601227223738895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90023329757971389759052373 1054960895601227223738895)
                    ·
                      rfl

theorem cell23_6163587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_6163587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163587 prefixEnd_6163587 := by exact prefixLift 6163587
  have htrace : WordTrace (prefixWord ++ tailWord_6163587) baseStart_6163587 baseEnd_6163587 := by
    simpa [prefixWord, tailWord_6163587, baseEnd_6163587] using wordTrace_append hprefix tailTrace_6163587
  have hstable : (prefixWord ++ tailWord_6163587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163587).length < 2 ^ (prefixWord ++ tailWord_6163587).sum := by decide
  have hdescent : baseEnd_6163587 < baseStart_6163587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163588 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_6163588 : Nat := 118140960795 + 6163588 * 2 ^ 59
def prefixEnd_6163588 : Nat := 4983230072969 + 3 ^ 40 * 6163588 * 2
def baseEnd_6163588 : Nat := 3164883200284336167304181

theorem tailTrace_6163588 : CollatzResearch.WordTrace tailWord_6163588 prefixEnd_6163588 3164883200284336167304181 := by
  unfold tailWord_6163588
  simp only [CollatzResearch.WordTrace]
  refine ⟨112402261397190403934601709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149869681862920538579468945 112402261397190403934601709)
  ·
    refine ⟨42150848023946401475475641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112402261397190403934601709 42150848023946401475475641)
    ·
      refine ⟨31613136017959801106606731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42150848023946401475475641 31613136017959801106606731)
      ·
        refine ⟨47419704026939701659910097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31613136017959801106606731 47419704026939701659910097)
        ·
          refine ⟨35564778020204776244932573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47419704026939701659910097 35564778020204776244932573)
          ·
            refine ⟨13336791757576791091849715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35564778020204776244932573 13336791757576791091849715)
            ·
              refine ⟨20005187636365186637774573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336791757576791091849715 20005187636365186637774573)
              ·
                refine ⟨7501945363636944989165465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20005187636365186637774573 7501945363636944989165465)
                ·
                  refine ⟨5626459022727708741874099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7501945363636944989165465 5626459022727708741874099)
                  ·
                    refine ⟨8439688534091563112811149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626459022727708741874099 8439688534091563112811149)
                    ·
                      refine ⟨3164883200284336167304181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439688534091563112811149 3164883200284336167304181)
                      ·
                        rfl

theorem cell23_6163588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_6163588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163588 prefixEnd_6163588 := by exact prefixLift 6163588
  have htrace : WordTrace (prefixWord ++ tailWord_6163588) baseStart_6163588 baseEnd_6163588 := by
    simpa [prefixWord, tailWord_6163588, baseEnd_6163588] using wordTrace_append hprefix tailTrace_6163588
  have hstable : (prefixWord ++ tailWord_6163588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163588).length < 2 ^ (prefixWord ++ tailWord_6163588).sum := by decide
  have hdescent : baseEnd_6163588 < baseStart_6163588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163598 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6163598 : Nat := 118140960795 + 6163598 * 2 ^ 59
def prefixEnd_6163598 : Nat := 4983230072969 + 3 ^ 40 * 6163598 * 2
def baseEnd_6163598 : Nat := 3164888335090881128179135

theorem tailTrace_6163598 : CollatzResearch.WordTrace tailWord_6163598 prefixEnd_6163598 3164888335090881128179135 := by
  unfold tailWord_6163598
  simp only [CollatzResearch.WordTrace]
  refine ⟨28100610940543072447133431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149869925016229719718044965 28100610940543072447133431)
  ·
    refine ⟨42150916410814608670700147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28100610940543072447133431 42150916410814608670700147)
    ·
      refine ⟨63226374616221913006050221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42150916410814608670700147 63226374616221913006050221)
      ·
        refine ⟨23709890481083217377268833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63226374616221913006050221 23709890481083217377268833)
        ·
          refine ⟨17782417860812413032951625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23709890481083217377268833 17782417860812413032951625)
          ·
            refine ⟨13336813395609309774713719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17782417860812413032951625 13336813395609309774713719)
            ·
              refine ⟨20005220093413964662070579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13336813395609309774713719 20005220093413964662070579)
              ·
                refine ⟨30007830140120946993105869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20005220093413964662070579 30007830140120946993105869)
                ·
                  refine ⟨11252936302545355122414701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30007830140120946993105869 11252936302545355122414701)
                  ·
                    refine ⟨4219851113454508170905513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11252936302545355122414701 4219851113454508170905513)
                    ·
                      refine ⟨3164888335090881128179135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219851113454508170905513 3164888335090881128179135)
                      ·
                        rfl

theorem cell23_6163598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6163598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163598 prefixEnd_6163598 := by exact prefixLift 6163598
  have htrace : WordTrace (prefixWord ++ tailWord_6163598) baseStart_6163598 baseEnd_6163598 := by
    simpa [prefixWord, tailWord_6163598, baseEnd_6163598] using wordTrace_append hprefix tailTrace_6163598
  have hstable : (prefixWord ++ tailWord_6163598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163598).length < 2 ^ (prefixWord ++ tailWord_6163598).sum := by decide
  have hdescent : baseEnd_6163598 < baseStart_6163598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163711 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 3, 4]
def baseStart_6163711 : Nat := 118140960795 + 6163711 * 2 ^ 59
def prefixEnd_6163711 : Nat := 4983230072969 + 3 ^ 40 * 6163711 * 2
def baseEnd_6163711 : Nat := 1054982119468279728688705

theorem tailTrace_6163711 : CollatzResearch.WordTrace tailWord_6163711 prefixEnd_6163711 1054982119468279728688705 := by
  unfold tailWord_6163711
  simp only [CollatzResearch.WordTrace]
  refine ⟨224809008972935199875930987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149872672648623466583953991 224809008972935199875930987)
  ·
    refine ⟨337213513459402799813896481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224809008972935199875930987 337213513459402799813896481)
    ·
      refine ⟨252910135094552099860422361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337213513459402799813896481 252910135094552099860422361)
      ·
        refine ⟨189682601320914074895316771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252910135094552099860422361 189682601320914074895316771)
        ·
          refine ⟨284523901981371112342975157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189682601320914074895316771 284523901981371112342975157)
          ·
            refine ⟨26674115810753541782153921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284523901981371112342975157 26674115810753541782153921)
            ·
              refine ⟨20005586858065156336615441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26674115810753541782153921 20005586858065156336615441)
              ·
                refine ⟨15004190143548867252461581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20005586858065156336615441 15004190143548867252461581)
                ·
                  refine ⟨5626571303830825219673093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15004190143548867252461581 5626571303830825219673093)
                  ·
                    refine ⟨1054982119468279728688705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626571303830825219673093 1054982119468279728688705)
                    ·
                      rfl

theorem cell23_6163711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_6163711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163711 prefixEnd_6163711 := by exact prefixLift 6163711
  have htrace : WordTrace (prefixWord ++ tailWord_6163711) baseStart_6163711 baseEnd_6163711 := by
    simpa [prefixWord, tailWord_6163711, baseEnd_6163711] using wordTrace_append hprefix tailTrace_6163711
  have hstable : (prefixWord ++ tailWord_6163711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163711).length < 2 ^ (prefixWord ++ tailWord_6163711).sum := by decide
  have hdescent : baseEnd_6163711 < baseStart_6163711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163721 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_6163721 : Nat := 118140960795 + 6163721 * 2 ^ 59
def prefixEnd_6163721 : Nat := 4983230072969 + 3 ^ 40 * 6163721 * 2
def baseEnd_6163721 : Nat := 3164951493211384146941069

theorem tailTrace_6163721 : CollatzResearch.WordTrace tailWord_6163721 prefixEnd_6163721 3164951493211384146941069 := by
  unfold tailWord_6163721
  simp only [CollatzResearch.WordTrace]
  refine ⟨224809373702898971583795017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149872915801932647722530011 224809373702898971583795017)
  ·
    refine ⟨168607030277174228687846263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224809373702898971583795017 168607030277174228687846263)
    ·
      refine ⟨252910545415761343031769395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168607030277174228687846263 252910545415761343031769395)
      ·
        refine ⟨379365818123642014547654093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252910545415761343031769395 379365818123642014547654093)
        ·
          refine ⟨142262181796365755455370285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379365818123642014547654093 142262181796365755455370285)
          ·
            refine ⟨53348318173637158295763857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142262181796365755455370285 53348318173637158295763857)
            ·
              refine ⟨40011238630227868721822893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53348318173637158295763857 40011238630227868721822893)
              ·
                refine ⟨15004214486335450770683585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40011238630227868721822893 15004214486335450770683585)
                ·
                  refine ⟨11253160864751588078012689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15004214486335450770683585 11253160864751588078012689)
                  ·
                    refine ⟨8439870648563691058509517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11253160864751588078012689 8439870648563691058509517)
                    ·
                      refine ⟨3164951493211384146941069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439870648563691058509517 3164951493211384146941069)
                      ·
                        rfl

theorem cell23_6163721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_6163721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163721 prefixEnd_6163721 := by exact prefixLift 6163721
  have htrace : WordTrace (prefixWord ++ tailWord_6163721) baseStart_6163721 baseEnd_6163721 := by
    simpa [prefixWord, tailWord_6163721, baseEnd_6163721] using wordTrace_append hprefix tailTrace_6163721
  have hstable : (prefixWord ++ tailWord_6163721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163721).length < 2 ^ (prefixWord ++ tailWord_6163721).sum := by decide
  have hdescent : baseEnd_6163721 < baseStart_6163721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163724 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 8]
def baseStart_6163724 : Nat := 118140960795 + 6163724 * 2 ^ 59
def prefixEnd_6163724 : Nat := 4983230072969 + 3 ^ 40 * 6163724 * 2
def baseEnd_6163724 : Nat := 351661448183705292800395

theorem tailTrace_6163724 : CollatzResearch.WordTrace tailWord_6163724 prefixEnd_6163724 351661448183705292800395 := by
  unfold tailWord_6163724
  simp only [CollatzResearch.WordTrace]
  refine ⟨112404741560944051548077113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149872988747925402064102817 112404741560944051548077113)
  ·
    refine ⟨84303556170708038661057835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112404741560944051548077113 84303556170708038661057835)
    ·
      refine ⟨126455334256062057991586753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84303556170708038661057835 126455334256062057991586753)
      ·
        refine ⟨94841500692046543493690065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126455334256062057991586753 94841500692046543493690065)
        ·
          refine ⟨71131125519034907620267549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94841500692046543493690065 71131125519034907620267549)
          ·
            refine ⟨26674172069638090357600331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71131125519034907620267549 26674172069638090357600331)
            ·
              refine ⟨40011258104457135536400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26674172069638090357600331 40011258104457135536400497)
              ·
                refine ⟨30008443578342851652300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40011258104457135536400497 30008443578342851652300373)
                ·
                  refine ⟨351661448183705292800395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30008443578342851652300373 351661448183705292800395)
                  ·
                    rfl

theorem cell23_6163724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_6163724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163724 prefixEnd_6163724 := by exact prefixLift 6163724
  have htrace : WordTrace (prefixWord ++ tailWord_6163724) baseStart_6163724 baseEnd_6163724 := by
    simpa [prefixWord, tailWord_6163724, baseEnd_6163724] using wordTrace_append hprefix tailTrace_6163724
  have hstable : (prefixWord ++ tailWord_6163724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163724).length < 2 ^ (prefixWord ++ tailWord_6163724).sum := by decide
  have hdescent : baseEnd_6163724 < baseStart_6163724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163738 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_6163738 : Nat := 118140960795 + 6163738 * 2 ^ 59
def prefixEnd_6163738 : Nat := 4983230072969 + 3 ^ 40 * 6163738 * 2
def baseEnd_6163738 : Nat := 3164960222382510580428491

theorem tailTrace_6163738 : CollatzResearch.WordTrace tailWord_6163738 prefixEnd_6163738 3164960222382510580428491 := by
  unfold tailWord_6163738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56202498435959345871790967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149873329162558255658109245 56202498435959345871790967)
  ·
    refine ⟨84303747653939018807686451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56202498435959345871790967 84303747653939018807686451)
    ·
      refine ⟨126455621480908528211529677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84303747653939018807686451 126455621480908528211529677)
      ·
        refine ⟨47420858055340698079323629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126455621480908528211529677 47420858055340698079323629)
        ·
          refine ⟨17782821770752761779746361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47420858055340698079323629 17782821770752761779746361)
          ·
            refine ⟨13337116328064571334809771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17782821770752761779746361 13337116328064571334809771)
            ·
              refine ⟨20005674492096857002214657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337116328064571334809771 20005674492096857002214657)
              ·
                refine ⟨15004255869072642751660993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20005674492096857002214657 15004255869072642751660993)
                ·
                  refine ⟨11253191901804482063745745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15004255869072642751660993 11253191901804482063745745)
                  ·
                    refine ⟨8439893926353361547809309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11253191901804482063745745 8439893926353361547809309)
                    ·
                      refine ⟨3164960222382510580428491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439893926353361547809309 3164960222382510580428491)
                      ·
                        rfl

theorem cell23_6163738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_6163738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163738 prefixEnd_6163738 := by exact prefixLift 6163738
  have htrace : WordTrace (prefixWord ++ tailWord_6163738) baseStart_6163738 baseEnd_6163738 := by
    simpa [prefixWord, tailWord_6163738, baseEnd_6163738] using wordTrace_append hprefix tailTrace_6163738
  have hstable : (prefixWord ++ tailWord_6163738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163738).length < 2 ^ (prefixWord ++ tailWord_6163738).sum := by decide
  have hdescent : baseEnd_6163738 < baseStart_6163738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163741 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 8]
def baseStart_6163741 : Nat := 118140960795 + 6163741 * 2 ^ 59
def prefixEnd_6163741 : Nat := 4983230072969 + 3 ^ 40 * 6163741 * 2
def baseEnd_6163741 : Nat := 351662418091608229854553

theorem tailTrace_6163741 : CollatzResearch.WordTrace tailWord_6163741 prefixEnd_6163741 351662418091608229854553 := by
  unfold tailWord_6163741
  simp only [CollatzResearch.WordTrace]
  refine ⟨224810103162826514999523077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149873402108551009999682051 224810103162826514999523077)
  ·
    refine ⟨42151894343029971562410577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224810103162826514999523077 42151894343029971562410577)
    ·
      refine ⟨31613920757272478671807933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42151894343029971562410577 31613920757272478671807933)
      ·
        refine ⟨11855220283977179501927975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31613920757272478671807933 11855220283977179501927975)
        ·
          refine ⟨17782830425965769252891963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11855220283977179501927975 17782830425965769252891963)
          ·
            refine ⟨26674245638948653879337945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782830425965769252891963 26674245638948653879337945)
            ·
              refine ⟨20005684229211490409503459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26674245638948653879337945 20005684229211490409503459)
              ·
                refine ⟨30008526343817235614255189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20005684229211490409503459 30008526343817235614255189)
                ·
                  refine ⟨351662418091608229854553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30008526343817235614255189 351662418091608229854553)
                  ·
                    rfl

theorem cell23_6163741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_6163741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163741 prefixEnd_6163741 := by exact prefixLift 6163741
  have htrace : WordTrace (prefixWord ++ tailWord_6163741) baseStart_6163741 baseEnd_6163741 := by
    simpa [prefixWord, tailWord_6163741, baseEnd_6163741] using wordTrace_append hprefix tailTrace_6163741
  have hstable : (prefixWord ++ tailWord_6163741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163741).length < 2 ^ (prefixWord ++ tailWord_6163741).sum := by decide
  have hdescent : baseEnd_6163741 < baseStart_6163741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163791 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 6, 2]
def baseStart_6163791 : Nat := 118140960795 + 6163791 * 2 ^ 59
def prefixEnd_6163791 : Nat := 4983230072969 + 3 ^ 40 * 6163791 * 2
def baseEnd_6163791 : Nat := 3164987436857198873065747

theorem tailTrace_6163791 : CollatzResearch.WordTrace tailWord_6163791 prefixEnd_6163791 3164987436857198873065747 := by
  unfold tailWord_6163791
  simp only [CollatzResearch.WordTrace]
  refine ⟨224811926812645373538843227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149874617875096915692562151 224811926812645373538843227)
  ·
    refine ⟨337217890218968060308264841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224811926812645373538843227 337217890218968060308264841)
    ·
      refine ⟨252913417664226045231198631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337217890218968060308264841 252913417664226045231198631)
      ·
        refine ⟨379370126496339067846797947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252913417664226045231198631 379370126496339067846797947)
        ·
          refine ⟨569055189744508601770196921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379370126496339067846797947 569055189744508601770196921)
          ·
            refine ⟨426791392308381451327647691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569055189744508601770196921 426791392308381451327647691)
            ·
              refine ⟨640187088462572176991471537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426791392308381451327647691 640187088462572176991471537)
              ·
                refine ⟨480140316346929132743603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640187088462572176991471537 480140316346929132743603653)
                ·
                  refine ⟨90026309315049212389425685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480140316346929132743603653 90026309315049212389425685)
                  ·
                    refine ⟨4219983249142931830754329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90026309315049212389425685 4219983249142931830754329)
                    ·
                      refine ⟨3164987436857198873065747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4219983249142931830754329 3164987436857198873065747)
                      ·
                        rfl

theorem cell23_6163791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 6, 2].length) (baseStart_6163791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163791 prefixEnd_6163791 := by exact prefixLift 6163791
  have htrace : WordTrace (prefixWord ++ tailWord_6163791) baseStart_6163791 baseEnd_6163791 := by
    simpa [prefixWord, tailWord_6163791, baseEnd_6163791] using wordTrace_append hprefix tailTrace_6163791
  have hstable : (prefixWord ++ tailWord_6163791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163791).length < 2 ^ (prefixWord ++ tailWord_6163791).sum := by decide
  have hdescent : baseEnd_6163791 < baseStart_6163791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163801 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_6163801 : Nat := 118140960795 + 6163801 * 2 ^ 59
def prefixEnd_6163801 : Nat := 4983230072969 + 3 ^ 40 * 6163801 * 2
def baseEnd_6163801 : Nat := 1054997523887914611313567

theorem tailTrace_6163801 : CollatzResearch.WordTrace tailWord_6163801 prefixEnd_6163801 1054997523887914611313567 := by
  unfold tailWord_6163801
  simp only [CollatzResearch.WordTrace]
  refine ⟨224812291542609145246707257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149874861028406096831138171 224812291542609145246707257)
  ·
    refine ⟨168609218656956858935030443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224812291542609145246707257 168609218656956858935030443)
    ·
      refine ⟨252913827985435288402545665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168609218656956858935030443 252913827985435288402545665)
      ·
        refine ⟨189685370989076466301909249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252913827985435288402545665 189685370989076466301909249)
        ·
          refine ⟨142264028241807349726431937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189685370989076466301909249 142264028241807349726431937)
          ·
            refine ⟨106698021181355512294823953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142264028241807349726431937 106698021181355512294823953)
            ·
              refine ⟨80023515886016634221117965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106698021181355512294823953 80023515886016634221117965)
              ·
                refine ⟨30008818457256237832919237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80023515886016634221117965 30008818457256237832919237)
                ·
                  refine ⟨5626653460735544593672357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30008818457256237832919237 5626653460735544593672357)
                  ·
                    refine ⟨1054997523887914611313567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626653460735544593672357 1054997523887914611313567)
                    ·
                      rfl

theorem cell23_6163801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_6163801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163801 prefixEnd_6163801 := by exact prefixLift 6163801
  have htrace : WordTrace (prefixWord ++ tailWord_6163801) baseStart_6163801 baseEnd_6163801 := by
    simpa [prefixWord, tailWord_6163801, baseEnd_6163801] using wordTrace_append hprefix tailTrace_6163801
  have hstable : (prefixWord ++ tailWord_6163801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163801).length < 2 ^ (prefixWord ++ tailWord_6163801).sum := by decide
  have hdescent : baseEnd_6163801 < baseStart_6163801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163802 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_6163802 : Nat := 118140960795 + 6163802 * 2 ^ 59
def prefixEnd_6163802 : Nat := 4983230072969 + 3 ^ 40 * 6163802 * 2
def baseEnd_6163802 : Nat := 3164993085144398330028197

theorem tailTrace_6163802 : CollatzResearch.WordTrace tailWord_6163802 prefixEnd_6163802 3164993085144398330028197 := by
  unfold tailWord_6163802
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203082003901380604373415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149874885343737014944995773 56203082003901380604373415)
  ·
    refine ⟨84304623005852070906560123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56203082003901380604373415 84304623005852070906560123)
    ·
      refine ⟨126456934508778106359840185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84304623005852070906560123 126456934508778106359840185)
      ·
        refine ⟨94842700881583579769880139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126456934508778106359840185 94842700881583579769880139)
        ·
          refine ⟨142264051322375369654820209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94842700881583579769880139 142264051322375369654820209)
          ·
            refine ⟨106698038491781527241115157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142264051322375369654820209 106698038491781527241115157)
            ·
              refine ⟨5001470554302259089427273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106698038491781527241115157 5001470554302259089427273)
              ·
                refine ⟨3751102915726694317070455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001470554302259089427273 3751102915726694317070455)
                ·
                  refine ⟨5626654373590041475605683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3751102915726694317070455 5626654373590041475605683)
                  ·
                    refine ⟨8439981560385062213408525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626654373590041475605683 8439981560385062213408525)
                    ·
                      refine ⟨3164993085144398330028197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8439981560385062213408525 3164993085144398330028197)
                      ·
                        rfl

theorem cell23_6163802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_6163802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163802 prefixEnd_6163802 := by exact prefixLift 6163802
  have htrace : WordTrace (prefixWord ++ tailWord_6163802) baseStart_6163802 baseEnd_6163802 := by
    simpa [prefixWord, tailWord_6163802, baseEnd_6163802] using wordTrace_append hprefix tailTrace_6163802
  have hstable : (prefixWord ++ tailWord_6163802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163802).length < 2 ^ (prefixWord ++ tailWord_6163802).sum := by decide
  have hdescent : baseEnd_6163802 < baseStart_6163802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163829 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6163829 : Nat := 118140960795 + 6163829 * 2 ^ 59
def prefixEnd_6163829 : Nat := 4983230072969 + 3 ^ 40 * 6163829 * 2
def baseEnd_6163829 : Nat := 3165006949122069724390573

theorem tailTrace_6163829 : CollatzResearch.WordTrace tailWord_6163829 prefixEnd_6163829 3165006949122069724390573 := by
  unfold tailWord_6163829
  simp only [CollatzResearch.WordTrace]
  refine ⟨224813312786507706028726541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149875541857671804019151027 224813312786507706028726541)
  ·
    refine ⟨84304992294940389760772453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224813312786507706028726541 84304992294940389760772453)
    ·
      refine ⟨15807186055301323080144835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84304992294940389760772453 15807186055301323080144835)
      ·
        refine ⟨23710779082951984620217253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807186055301323080144835 23710779082951984620217253)
        ·
          refine ⟨4445771078053497116290735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23710779082951984620217253 4445771078053497116290735)
          ·
            refine ⟨6668656617080245674436103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445771078053497116290735 6668656617080245674436103)
            ·
              refine ⟨10002984925620368511654155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668656617080245674436103 10002984925620368511654155)
              ·
                refine ⟨15004477388430552767481233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002984925620368511654155 15004477388430552767481233)
                ·
                  refine ⟨11253358041322914575610925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15004477388430552767481233 11253358041322914575610925)
                  ·
                    refine ⟨4220009265496092965854097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11253358041322914575610925 4220009265496092965854097)
                    ·
                      refine ⟨3165006949122069724390573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220009265496092965854097 3165006949122069724390573)
                      ·
                        rfl

theorem cell23_6163829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6163829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163829 prefixEnd_6163829 := by exact prefixLift 6163829
  have htrace : WordTrace (prefixWord ++ tailWord_6163829) baseStart_6163829 baseEnd_6163829 := by
    simpa [prefixWord, tailWord_6163829, baseEnd_6163829] using wordTrace_append hprefix tailTrace_6163829
  have hstable : (prefixWord ++ tailWord_6163829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163829).length < 2 ^ (prefixWord ++ tailWord_6163829).sum := by decide
  have hdescent : baseEnd_6163829 < baseStart_6163829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163831 : List Nat := [1, 1, 3, 1, 1, 2, 7, 7]
def baseStart_6163831 : Nat := 118140960795 + 6163831 * 2 ^ 59
def prefixEnd_6163831 : Nat := 4983230072969 + 3 ^ 40 * 6163831 * 2
def baseEnd_6163831 : Nat := 117222517632717730243169

theorem tailTrace_6163831 : CollatzResearch.WordTrace tailWord_6163831 prefixEnd_6163831 117222517632717730243169 := by
  unfold tailWord_6163831
  simp only [CollatzResearch.WordTrace]
  refine ⟨224813385732500460370299347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149875590488333640246866231 224813385732500460370299347)
  ·
    refine ⟨337220078598750690555449021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224813385732500460370299347 337220078598750690555449021)
    ·
      refine ⟨126457529474531508958293383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337220078598750690555449021 126457529474531508958293383)
      ·
        refine ⟨189686294211797263437440075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126457529474531508958293383 189686294211797263437440075)
        ·
          refine ⟨284529441317695895156160113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189686294211797263437440075 284529441317695895156160113)
          ·
            refine ⟨213397080988271921367120085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284529441317695895156160113 213397080988271921367120085)
            ·
              refine ⟨5001494085662623157041877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213397080988271921367120085 5001494085662623157041877)
              ·
                refine ⟨117222517632717730243169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5001494085662623157041877 117222517632717730243169)
                ·
                  rfl

theorem cell23_6163831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 7].length) (baseStart_6163831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163831 prefixEnd_6163831 := by exact prefixLift 6163831
  have htrace : WordTrace (prefixWord ++ tailWord_6163831) baseStart_6163831 baseEnd_6163831 := by
    simpa [prefixWord, tailWord_6163831, baseEnd_6163831] using wordTrace_append hprefix tailTrace_6163831
  have hstable : (prefixWord ++ tailWord_6163831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163831).length < 2 ^ (prefixWord ++ tailWord_6163831).sum := by decide
  have hdescent : baseEnd_6163831 < baseStart_6163831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163842 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6163842 : Nat := 118140960795 + 6163842 * 2 ^ 59
def prefixEnd_6163842 : Nat := 4983230072969 + 3 ^ 40 * 6163842 * 2
def baseEnd_6163842 : Nat := 3165013624370578173528013

theorem tailTrace_6163842 : CollatzResearch.WordTrace tailWord_6163842 prefixEnd_6163842 3165013624370578173528013 := by
  unfold tailWord_6163842
  simp only [CollatzResearch.WordTrace]
  refine ⟨56203446733865152312237445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149875857956973739499299853 56203446733865152312237445)
  ·
    refine ⟨10538146262599716058544521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56203446733865152312237445 10538146262599716058544521)
    ·
      refine ⟨7903609696949787043908391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538146262599716058544521 7903609696949787043908391)
      ·
        refine ⟨11855414545424680565862587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903609696949787043908391 11855414545424680565862587)
        ·
          refine ⟨17783121818137020848793881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11855414545424680565862587 17783121818137020848793881)
          ·
            refine ⟨13337341363602765636595411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17783121818137020848793881 13337341363602765636595411)
            ·
              refine ⟨20006012045404148454893117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337341363602765636595411 20006012045404148454893117)
              ·
                refine ⟨7502254517026555670584919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20006012045404148454893117 7502254517026555670584919)
                ·
                  refine ⟨11253381775539833505877379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502254517026555670584919 11253381775539833505877379)
                  ·
                    refine ⟨16880072663309750258816069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11253381775539833505877379 16880072663309750258816069)
                    ·
                      refine ⟨3165013624370578173528013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16880072663309750258816069 3165013624370578173528013)
                      ·
                        rfl

theorem cell23_6163842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6163842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163842 prefixEnd_6163842 := by exact prefixLift 6163842
  have htrace : WordTrace (prefixWord ++ tailWord_6163842) baseStart_6163842 baseEnd_6163842 := by
    simpa [prefixWord, tailWord_6163842, baseEnd_6163842] using wordTrace_append hprefix tailTrace_6163842
  have hstable : (prefixWord ++ tailWord_6163842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163842).length < 2 ^ (prefixWord ++ tailWord_6163842).sum := by decide
  have hdescent : baseEnd_6163842 < baseStart_6163842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163845 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_6163845 : Nat := 118140960795 + 6163845 * 2 ^ 59
def prefixEnd_6163845 : Nat := 4983230072969 + 3 ^ 40 * 6163845 * 2
def baseEnd_6163845 : Nat := 3165015164812541661790499

theorem tailTrace_6163845 : CollatzResearch.WordTrace tailWord_6163845 prefixEnd_6163845 3165015164812541661790499 := by
  unfold tailWord_6163845
  simp only [CollatzResearch.WordTrace]
  refine ⟨224813896354449740761308989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149875930902966493840872659 224813896354449740761308989)
  ·
    refine ⟨84305211132918652785490871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224813896354449740761308989 84305211132918652785490871)
    ·
      refine ⟨126457816699377979178236307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84305211132918652785490871 126457816699377979178236307)
      ·
        refine ⟨189686725049066968767354461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126457816699377979178236307 189686725049066968767354461)
        ·
          refine ⟨71132521893400113287757923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189686725049066968767354461 71132521893400113287757923)
          ·
            refine ⟨106698782840100169931636885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71132521893400113287757923 106698782840100169931636885)
            ·
              refine ⟨5001505445629695465545479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106698782840100169931636885 5001505445629695465545479)
              ·
                refine ⟨7502258168444543198318219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001505445629695465545479 7502258168444543198318219)
                ·
                  refine ⟨11253387252666814797477329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502258168444543198318219 11253387252666814797477329)
                  ·
                    refine ⟨8440040439500111098107997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11253387252666814797477329 8440040439500111098107997)
                    ·
                      refine ⟨3165015164812541661790499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440040439500111098107997 3165015164812541661790499)
                      ·
                        rfl

theorem cell23_6163845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_6163845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163845 prefixEnd_6163845 := by exact prefixLift 6163845
  have htrace : WordTrace (prefixWord ++ tailWord_6163845) baseStart_6163845 baseEnd_6163845 := by
    simpa [prefixWord, tailWord_6163845, baseEnd_6163845] using wordTrace_append hprefix tailTrace_6163845
  have hstable : (prefixWord ++ tailWord_6163845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163845).length < 2 ^ (prefixWord ++ tailWord_6163845).sum := by decide
  have hdescent : baseEnd_6163845 < baseStart_6163845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163915 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 4, 2, 2]
def baseStart_6163915 : Nat := 118140960795 + 6163915 * 2 ^ 59
def prefixEnd_6163915 : Nat := 4983230072969 + 3 ^ 40 * 6163915 * 2
def baseEnd_6163915 : Nat := 3165051108458356387915177

theorem tailTrace_6163915 : CollatzResearch.WordTrace tailWord_6163915 prefixEnd_6163915 3165051108458356387915177 := by
  unfold tailWord_6163915
  simp only [CollatzResearch.WordTrace]
  refine ⟨224816449464196142716357199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149877632976130761810904799 224816449464196142716357199)
  ·
    refine ⟨337224674196294214074535799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224816449464196142716357199 337224674196294214074535799)
    ·
      refine ⟨505837011294441321111803699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337224674196294214074535799 505837011294441321111803699)
      ·
        refine ⟨758755516941661981667705549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505837011294441321111803699 758755516941661981667705549)
        ·
          refine ⟨284533318853123243125389581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 758755516941661981667705549 284533318853123243125389581)
          ·
            refine ⟨106699994569921216172021093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284533318853123243125389581 106699994569921216172021093)
            ·
              refine ⟨20006248981860228032253955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106699994569921216172021093 20006248981860228032253955)
              ·
                refine ⟨30009373472790342048380933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20006248981860228032253955 30009373472790342048380933)
                ·
                  refine ⟨5626757526148189134071425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30009373472790342048380933 5626757526148189134071425)
                  ·
                    refine ⟨4220068144611141850553569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626757526148189134071425 4220068144611141850553569)
                    ·
                      refine ⟨3165051108458356387915177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220068144611141850553569 3165051108458356387915177)
                      ·
                        rfl

theorem cell23_6163915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 2, 2].length) (baseStart_6163915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163915 prefixEnd_6163915 := by exact prefixLift 6163915
  have htrace : WordTrace (prefixWord ++ tailWord_6163915) baseStart_6163915 baseEnd_6163915 := by
    simpa [prefixWord, tailWord_6163915, baseEnd_6163915] using wordTrace_append hprefix tailTrace_6163915
  have hstable : (prefixWord ++ tailWord_6163915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163915).length < 2 ^ (prefixWord ++ tailWord_6163915).sum := by decide
  have hdescent : baseEnd_6163915 < baseStart_6163915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163926 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_6163926 : Nat := 118140960795 + 6163926 * 2 ^ 59
def prefixEnd_6163926 : Nat := 4983230072969 + 3 ^ 40 * 6163926 * 2
def baseEnd_6163926 : Nat := 3165056756745555844877627

theorem tailTrace_6163926 : CollatzResearch.WordTrace tailWord_6163926 prefixEnd_6163926 3165056756745555844877627 := by
  unfold tailWord_6163926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051053166697268224687977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149877900444770861063338421 14051053166697268224687977)
  ·
    refine ⟨10538289875022951168515983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14051053166697268224687977 10538289875022951168515983)
    ·
      refine ⟨15807434812534426752773975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10538289875022951168515983 15807434812534426752773975)
      ·
        refine ⟨23711152218801640129160963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807434812534426752773975 23711152218801640129160963)
        ·
          refine ⟨35566728328202460193741445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23711152218801640129160963 35566728328202460193741445)
          ·
            refine ⟨6668761561537961286326521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35566728328202460193741445 6668761561537961286326521)
            ·
              refine ⟨5001571171153470964744891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668761561537961286326521 5001571171153470964744891)
              ·
                refine ⟨7502356756730206447117337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001571171153470964744891 7502356756730206447117337)
                ·
                  refine ⟨5626767567547654835338003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7502356756730206447117337 5626767567547654835338003)
                  ·
                    refine ⟨8440151351321482253007005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5626767567547654835338003 8440151351321482253007005)
                    ·
                      refine ⟨3165056756745555844877627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440151351321482253007005 3165056756745555844877627)
                      ·
                        rfl

theorem cell23_6163926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_6163926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163926 prefixEnd_6163926 := by exact prefixLift 6163926
  have htrace : WordTrace (prefixWord ++ tailWord_6163926) baseStart_6163926 baseEnd_6163926 := by
    simpa [prefixWord, tailWord_6163926, baseEnd_6163926] using wordTrace_append hprefix tailTrace_6163926
  have hstable : (prefixWord ++ tailWord_6163926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163926).length < 2 ^ (prefixWord ++ tailWord_6163926).sum := by decide
  have hdescent : baseEnd_6163926 < baseStart_6163926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163951 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 7]
def baseStart_6163951 : Nat := 118140960795 + 6163951 * 2 ^ 59
def prefixEnd_6163951 : Nat := 4983230072969 + 3 ^ 40 * 6163951 * 2
def baseEnd_6163951 : Nat := 1055023197920639415688337

theorem tailTrace_6163951 : CollatzResearch.WordTrace tailWord_6163951 prefixEnd_6163951 1055023197920639415688337 := by
  unfold tailWord_6163951
  simp only [CollatzResearch.WordTrace]
  refine ⟨224817762492065720864667707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149878508328043813909778471 224817762492065720864667707)
  ·
    refine ⟨337226643738098581297001561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224817762492065720864667707 337226643738098581297001561)
    ·
      refine ⟨252919982803573935972751171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337226643738098581297001561 252919982803573935972751171)
      ·
        refine ⟨379379974205360903959126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252919982803573935972751171 379379974205360903959126757)
        ·
          refine ⟨71133745163505169492336267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379379974205360903959126757 71133745163505169492336267)
          ·
            refine ⟨106700617745257754238504401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71133745163505169492336267 106700617745257754238504401)
            ·
              refine ⟨80025463308943315678878301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106700617745257754238504401 80025463308943315678878301)
              ·
                refine ⟨30009548740853743379579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80025463308943315678878301 30009548740853743379579363)
                ·
                  refine ⟨45014323111280615069369045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30009548740853743379579363 45014323111280615069369045)
                  ·
                    refine ⟨1055023197920639415688337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45014323111280615069369045 1055023197920639415688337)
                    ·
                      rfl

theorem cell23_6163951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_6163951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163951 prefixEnd_6163951 := by exact prefixLift 6163951
  have htrace : WordTrace (prefixWord ++ tailWord_6163951) baseStart_6163951 baseEnd_6163951 := by
    simpa [prefixWord, tailWord_6163951, baseEnd_6163951] using wordTrace_append hprefix tailTrace_6163951
  have hstable : (prefixWord ++ tailWord_6163951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163951).length < 2 ^ (prefixWord ++ tailWord_6163951).sum := by decide
  have hdescent : baseEnd_6163951 < baseStart_6163951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163972 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 5]
def baseStart_6163972 : Nat := 118140960795 + 6163972 * 2 ^ 59
def prefixEnd_6163972 : Nat := 4983230072969 + 3 ^ 40 * 6163972 * 2
def baseEnd_6163972 : Nat := 351675597428406962766935

theorem tailTrace_6163972 : CollatzResearch.WordTrace tailWord_6163972 prefixEnd_6163972 351675597428406962766935 := by
  unfold tailWord_6163972
  simp only [CollatzResearch.WordTrace]
  refine ⟨112409264212494820725591085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149879018949993094300788113 112409264212494820725591085)
  ·
    refine ⟨42153474079685557772096657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112409264212494820725591085 42153474079685557772096657)
    ·
      refine ⟨31615105559764168329072493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42153474079685557772096657 31615105559764168329072493)
      ·
        refine ⟨11855664584911563123402185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31615105559764168329072493 11855664584911563123402185)
        ·
          refine ⟨8891748438683672342551639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855664584911563123402185 8891748438683672342551639)
          ·
            refine ⟨13337622658025508513827459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891748438683672342551639 13337622658025508513827459)
            ·
              refine ⟨20006433987038262770741189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13337622658025508513827459 20006433987038262770741189)
              ·
                refine ⟨3751206372569674269513973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20006433987038262770741189 3751206372569674269513973)
                ·
                  refine ⟨351675597428406962766935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751206372569674269513973 351675597428406962766935)
                  ·
                    rfl

theorem cell23_6163972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_6163972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163972 prefixEnd_6163972 := by exact prefixLift 6163972
  have htrace : WordTrace (prefixWord ++ tailWord_6163972) baseStart_6163972 baseEnd_6163972 := by
    simpa [prefixWord, tailWord_6163972, baseEnd_6163972] using wordTrace_append hprefix tailTrace_6163972
  have hstable : (prefixWord ++ tailWord_6163972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163972).length < 2 ^ (prefixWord ++ tailWord_6163972).sum := by decide
  have hdescent : baseEnd_6163972 < baseStart_6163972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163975 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6163975 : Nat := 118140960795 + 6163975 * 2 ^ 59
def prefixEnd_6163975 : Nat := 4983230072969 + 3 ^ 40 * 6163975 * 2
def baseEnd_6163975 : Nat := 3165081917297626153164901

theorem tailTrace_6163975 : CollatzResearch.WordTrace tailWord_6163975 prefixEnd_6163975 3165081917297626153164901 := by
  unfold tailWord_6163975
  simp only [CollatzResearch.WordTrace]
  refine ⟨224818637843978772963541379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149879091895985848642360919 224818637843978772963541379)
  ·
    refine ⟨337227956765968159445312069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224818637843978772963541379 337227956765968159445312069)
    ·
      refine ⟨63230241893619029895996013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337227956765968159445312069 63230241893619029895996013)
      ·
        refine ⟨23711340710107136210998505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63230241893619029895996013 23711340710107136210998505)
        ·
          refine ⟨17783505532580352158248879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23711340710107136210998505 17783505532580352158248879)
          ·
            refine ⟨26675258298870528237373319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17783505532580352158248879 26675258298870528237373319)
            ·
              refine ⟨40012887448305792356059979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26675258298870528237373319 40012887448305792356059979)
              ·
                refine ⟨60019331172458688534089969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40012887448305792356059979 60019331172458688534089969)
                ·
                  refine ⟨45014498379344016400567477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60019331172458688534089969 45014498379344016400567477)
                  ·
                    refine ⟨4220109223063501537553201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45014498379344016400567477 4220109223063501537553201)
                    ·
                      refine ⟨3165081917297626153164901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220109223063501537553201 3165081917297626153164901)
                      ·
                        rfl

theorem cell23_6163975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6163975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163975 prefixEnd_6163975 := by exact prefixLift 6163975
  have htrace : WordTrace (prefixWord ++ tailWord_6163975) baseStart_6163975 baseEnd_6163975 := by
    simpa [prefixWord, tailWord_6163975, baseEnd_6163975] using wordTrace_append hprefix tailTrace_6163975
  have hstable : (prefixWord ++ tailWord_6163975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163975).length < 2 ^ (prefixWord ++ tailWord_6163975).sum := by decide
  have hdescent : baseEnd_6163975 < baseStart_6163975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6163978 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6163978 : Nat := 118140960795 + 6163978 * 2 ^ 59
def prefixEnd_6163978 : Nat := 4983230072969 + 3 ^ 40 * 6163978 * 2
def baseEnd_6163978 : Nat := 3165083457739589641427387

theorem tailTrace_6163978 : CollatzResearch.WordTrace tailWord_6163978 prefixEnd_6163978 3165083457739589641427387 := by
  unfold tailWord_6163978
  simp only [CollatzResearch.WordTrace]
  refine ⟨56204686815741976118975147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149879164841978602983933725 56204686815741976118975147)
  ·
    refine ⟨84307030223612964178462721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56204686815741976118975147 84307030223612964178462721)
    ·
      refine ⟨63230272667709723133847041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84307030223612964178462721 63230272667709723133847041)
      ·
        refine ⟨47422704500782292350385281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63230272667709723133847041 47422704500782292350385281)
        ·
          refine ⟨35567028375586719262788961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47422704500782292350385281 35567028375586719262788961)
          ·
            refine ⟨26675271281690039447091721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35567028375586719262788961 26675271281690039447091721)
            ·
              refine ⟨20006453461267529585318791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26675271281690039447091721 20006453461267529585318791)
              ·
                refine ⟨30009680191901294377978187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20006453461267529585318791 30009680191901294377978187)
                ·
                  refine ⟨45014520287851941566967281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30009680191901294377978187 45014520287851941566967281)
                  ·
                    refine ⟨33760890215888956175225461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45014520287851941566967281 33760890215888956175225461)
                    ·
                      refine ⟨3165083457739589641427387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33760890215888956175225461 3165083457739589641427387)
                      ·
                        rfl

theorem cell23_6163978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6163978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6163978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6163978 prefixEnd_6163978 := by exact prefixLift 6163978
  have htrace : WordTrace (prefixWord ++ tailWord_6163978) baseStart_6163978 baseEnd_6163978 := by
    simpa [prefixWord, tailWord_6163978, baseEnd_6163978] using wordTrace_append hprefix tailTrace_6163978
  have hstable : (prefixWord ++ tailWord_6163978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6163978).length < 2 ^ (prefixWord ++ tailWord_6163978).sum := by decide
  have hdescent : baseEnd_6163978 < baseStart_6163978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6163978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164058 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_6164058 : Nat := 118140960795 + 6164058 * 2 ^ 59
def prefixEnd_6164058 : Nat := 4983230072969 + 3 ^ 40 * 6164058 * 2
def baseEnd_6164058 : Nat := 1055041512063983109475673

theorem tailTrace_6164058 : CollatzResearch.WordTrace tailWord_6164058 prefixEnd_6164058 1055041512063983109475673 := by
  unfold tailWord_6164058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56205416275669519534703207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149881110068452052092541885 56205416275669519534703207)
  ·
    refine ⟨84308124413504279302054811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56205416275669519534703207 84308124413504279302054811)
    ·
      refine ⟨126462186620256418953082217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84308124413504279302054811 126462186620256418953082217)
      ·
        refine ⟨94846639965192314214811663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126462186620256418953082217 94846639965192314214811663)
        ·
          refine ⟨142269959947788471322217495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94846639965192314214811663 142269959947788471322217495)
          ·
            refine ⟨213404939921682706983326243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142269959947788471322217495 213404939921682706983326243)
            ·
              refine ⟨320107409882524060474989365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213404939921682706983326243 320107409882524060474989365)
              ·
                refine ⟨30010069676486630669530253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320107409882524060474989365 30010069676486630669530253)
                ·
                  refine ⟨11253776128682486501073845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30010069676486630669530253 11253776128682486501073845)
                  ·
                    refine ⟨1055041512063983109475673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11253776128682486501073845 1055041512063983109475673)
                    ·
                      rfl

theorem cell23_6164058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_6164058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164058 prefixEnd_6164058 := by exact prefixLift 6164058
  have htrace : WordTrace (prefixWord ++ tailWord_6164058) baseStart_6164058 baseEnd_6164058 := by
    simpa [prefixWord, tailWord_6164058, baseEnd_6164058] using wordTrace_append hprefix tailTrace_6164058
  have hstable : (prefixWord ++ tailWord_6164058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164058).length < 2 ^ (prefixWord ++ tailWord_6164058).sum := by decide
  have hdescent : baseEnd_6164058 < baseStart_6164058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164065 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_6164065 : Nat := 118140960795 + 6164065 * 2 ^ 59
def prefixEnd_6164065 : Nat := 4983230072969 + 3 ^ 40 * 6164065 * 2
def baseEnd_6164065 : Nat := 3165128130556530801039487

theorem tailTrace_6164065 : CollatzResearch.WordTrace tailWord_6164065 prefixEnd_6164065 3165128130556530801039487 := by
  unfold tailWord_6164065
  simp only [CollatzResearch.WordTrace]
  refine ⟨224821920413652718334317649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149881280275768478889545099 224821920413652718334317649)
  ·
    refine ⟨168616440310239538750738237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224821920413652718334317649 168616440310239538750738237)
    ·
      refine ⟨63231165116339827031526839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168616440310239538750738237 63231165116339827031526839)
      ·
        refine ⟨94846747674509740547290259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63231165116339827031526839 94846747674509740547290259)
        ·
          refine ⟨142270121511764610820935389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94846747674509740547290259 142270121511764610820935389)
          ·
            refine ⟨53351295566911729057850771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142270121511764610820935389 53351295566911729057850771)
            ·
              refine ⟨80026943350367593586776157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53351295566911729057850771 80026943350367593586776157)
              ·
                refine ⟨30010103756387847595041059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80026943350367593586776157 30010103756387847595041059)
                ·
                  refine ⟨45015155634581771392561589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30010103756387847595041059 45015155634581771392561589)
                  ·
                    refine ⟨4220170840742041068052649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45015155634581771392561589 4220170840742041068052649)
                    ·
                      refine ⟨3165128130556530801039487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220170840742041068052649 3165128130556530801039487)
                      ·
                        rfl

theorem cell23_6164065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_6164065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164065 prefixEnd_6164065 := by exact prefixLift 6164065
  have htrace : WordTrace (prefixWord ++ tailWord_6164065) baseStart_6164065 baseEnd_6164065 := by
    simpa [prefixWord, tailWord_6164065, baseEnd_6164065] using wordTrace_append hprefix tailTrace_6164065
  have hstable : (prefixWord ++ tailWord_6164065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164065).length < 2 ^ (prefixWord ++ tailWord_6164065).sum := by decide
  have hdescent : baseEnd_6164065 < baseStart_6164065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164082 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6164082 : Nat := 118140960795 + 6164082 * 2 ^ 59
def prefixEnd_6164082 : Nat := 4983230072969 + 3 ^ 40 * 6164082 * 2
def baseEnd_6164082 : Nat := 3165136859727657234526909

theorem tailTrace_6164082 : CollatzResearch.WordTrace tailWord_6164082 prefixEnd_6164082 3165136859727657234526909 := by
  unfold tailWord_6164082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56205635113647782559421625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149881693636394086825124333 56205635113647782559421625)
  ·
    refine ⟨42154226335235836919566219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56205635113647782559421625 42154226335235836919566219)
    ·
      refine ⟨63231339502853755379349329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42154226335235836919566219 63231339502853755379349329)
      ·
        refine ⟨47423504627140316534511997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63231339502853755379349329 47423504627140316534511997)
        ·
          refine ⟨17783814235177618700441999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47423504627140316534511997 17783814235177618700441999)
          ·
            refine ⟨26675721352766428050662999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17783814235177618700441999 26675721352766428050662999)
            ·
              refine ⟨40013582029149642075994499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26675721352766428050662999 40013582029149642075994499)
              ·
                refine ⟨60020373043724463113991749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40013582029149642075994499 60020373043724463113991749)
                ·
                  refine ⟨11253819945698336833873453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60020373043724463113991749 11253819945698336833873453)
                  ·
                    refine ⟨4220182479636876312702545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11253819945698336833873453 4220182479636876312702545)
                    ·
                      refine ⟨3165136859727657234526909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220182479636876312702545 3165136859727657234526909)
                      ·
                        rfl

theorem cell23_6164082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6164082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164082 prefixEnd_6164082 := by exact prefixLift 6164082
  have htrace : WordTrace (prefixWord ++ tailWord_6164082) baseStart_6164082 baseEnd_6164082 := by
    simpa [prefixWord, tailWord_6164082, baseEnd_6164082] using wordTrace_append hprefix tailTrace_6164082
  have hstable : (prefixWord ++ tailWord_6164082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164082).length < 2 ^ (prefixWord ++ tailWord_6164082).sum := by decide
  have hdescent : baseEnd_6164082 < baseStart_6164082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164108 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6164108 : Nat := 118140960795 + 6164108 * 2 ^ 59
def prefixEnd_6164108 : Nat := 4983230072969 + 3 ^ 40 * 6164108 * 2
def baseEnd_6164108 : Nat := 3165150210224674132801789

theorem tailTrace_6164108 : CollatzResearch.WordTrace tailWord_6164108 prefixEnd_6164108 3165150210224674132801789 := by
  unfold tailWord_6164108
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411744376248468339066489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149882325834997957785421985 112411744376248468339066489)
  ·
    refine ⟨84308808282186351254299867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112411744376248468339066489 84308808282186351254299867)
    ·
      refine ⟨126463212423279526881449801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84308808282186351254299867 126463212423279526881449801)
      ·
        refine ⟨94847409317459645161087351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126463212423279526881449801 94847409317459645161087351)
        ·
          refine ⟨142271113976189467741631027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94847409317459645161087351 142271113976189467741631027)
          ·
            refine ⟨213406670964284201612446541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142271113976189467741631027 213406670964284201612446541)
            ·
              refine ⟨80027501611606575604667453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213406670964284201612446541 80027501611606575604667453)
              ·
                refine ⟨30010313104352465851750295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80027501611606575604667453 30010313104352465851750295)
                ·
                  refine ⟨45015469656528698777625443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30010313104352465851750295 45015469656528698777625443)
                  ·
                    refine ⟨67523204484793048166438165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45015469656528698777625443 67523204484793048166438165)
                    ·
                      refine ⟨3165150210224674132801789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67523204484793048166438165 3165150210224674132801789)
                      ·
                        rfl

theorem cell23_6164108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6164108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164108 prefixEnd_6164108 := by exact prefixLift 6164108
  have htrace : WordTrace (prefixWord ++ tailWord_6164108) baseStart_6164108 baseEnd_6164108 := by
    simpa [prefixWord, tailWord_6164108, baseEnd_6164108] using wordTrace_append hprefix tailTrace_6164108
  have hstable : (prefixWord ++ tailWord_6164108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164108).length < 2 ^ (prefixWord ++ tailWord_6164108).sum := by decide
  have hdescent : baseEnd_6164108 < baseStart_6164108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164112 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2]
def baseStart_6164112 : Nat := 118140960795 + 6164112 * 2 ^ 59
def prefixEnd_6164112 : Nat := 4983230072969 + 3 ^ 40 * 6164112 * 2
def baseEnd_6164112 : Nat := 3165152264147292117151771

theorem tailTrace_6164112 : CollatzResearch.WordTrace tailWord_6164112 prefixEnd_6164112 3165152264147292117151771 := by
  unfold tailWord_6164112
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411817322241222680639295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149882423096321630240852393 112411817322241222680639295)
  ·
    refine ⟨168617725983361834020958943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112411817322241222680639295 168617725983361834020958943)
    ·
      refine ⟨252926588975042751031438415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168617725983361834020958943 252926588975042751031438415)
      ·
        refine ⟨379389883462564126547157623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252926588975042751031438415 379389883462564126547157623)
        ·
          refine ⟨569084825193846189820736435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379389883462564126547157623 569084825193846189820736435)
          ·
            refine ⟨853627237790769284731104653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569084825193846189820736435 853627237790769284731104653)
            ·
              refine ⟨320110214171538481774164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853627237790769284731104653 320110214171538481774164245)
              ·
                refine ⟨15005166289290866333163949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 320110214171538481774164245 15005166289290866333163949)
                ·
                  refine ⟨5626937358484074874936481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15005166289290866333163949 5626937358484074874936481)
                  ·
                    refine ⟨4220203018863056156202361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5626937358484074874936481 4220203018863056156202361)
                    ·
                      refine ⟨3165152264147292117151771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220203018863056156202361 3165152264147292117151771)
                      ·
                        rfl

theorem cell23_6164112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2].length) (baseStart_6164112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164112 prefixEnd_6164112 := by exact prefixLift 6164112
  have htrace : WordTrace (prefixWord ++ tailWord_6164112) baseStart_6164112 baseEnd_6164112 := by
    simpa [prefixWord, tailWord_6164112, baseEnd_6164112] using wordTrace_append hprefix tailTrace_6164112
  have hstable : (prefixWord ++ tailWord_6164112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164112).length < 2 ^ (prefixWord ++ tailWord_6164112).sum := by decide
  have hdescent : baseEnd_6164112 < baseStart_6164112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164116 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6164116 : Nat := 118140960795 + 6164116 * 2 ^ 59
def prefixEnd_6164116 : Nat := 4983230072969 + 3 ^ 40 * 6164116 * 2
def baseEnd_6164116 : Nat := 3165154318069910101501753

theorem tailTrace_6164116 : CollatzResearch.WordTrace tailWord_6164116 prefixEnd_6164116 3165154318069910101501753 := by
  unfold tailWord_6164116
  simp only [CollatzResearch.WordTrace]
  refine ⟨112411890268233977022212101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149882520357645302696282801 112411890268233977022212101)
  ·
    refine ⟨21077229425293870691664769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112411890268233977022212101 21077229425293870691664769)
    ·
      refine ⟨15807922068970403018748577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21077229425293870691664769 15807922068970403018748577)
      ·
        refine ⟨11855941551727802264061433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15807922068970403018748577 11855941551727802264061433)
        ·
          refine ⟨8891956163795851698046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855941551727802264061433 8891956163795851698046075)
          ·
            refine ⟨13337934245693777547069113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891956163795851698046075 13337934245693777547069113)
            ·
              refine ⟨10003450684270333160301835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13337934245693777547069113 10003450684270333160301835)
              ·
                refine ⟨15005176026405499740452753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003450684270333160301835 15005176026405499740452753)
                ·
                  refine ⟨11253882019804124805339565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15005176026405499740452753 11253882019804124805339565)
                  ·
                    refine ⟨4220205757426546802002337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11253882019804124805339565 4220205757426546802002337)
                    ·
                      refine ⟨3165154318069910101501753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220205757426546802002337 3165154318069910101501753)
                      ·
                        rfl

theorem cell23_6164116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6164116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164116 prefixEnd_6164116 := by exact prefixLift 6164116
  have htrace : WordTrace (prefixWord ++ tailWord_6164116) baseStart_6164116 baseEnd_6164116 := by
    simpa [prefixWord, tailWord_6164116, baseEnd_6164116] using wordTrace_append hprefix tailTrace_6164116
  have hstable : (prefixWord ++ tailWord_6164116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164116).length < 2 ^ (prefixWord ++ tailWord_6164116).sum := by decide
  have hdescent : baseEnd_6164116 < baseStart_6164116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164129 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6164129 : Nat := 118140960795 + 6164129 * 2 ^ 59
def prefixEnd_6164129 : Nat := 4983230072969 + 3 ^ 40 * 6164129 * 2
def baseEnd_6164129 : Nat := 3165160993318418550639193

theorem tailTrace_6164129 : CollatzResearch.WordTrace tailWord_6164129 prefixEnd_6164129 3165160993318418550639193 := by
  unfold tailWord_6164129
  simp only [CollatzResearch.WordTrace]
  refine ⟨224824254685420857264647441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149882836456947238176431627 224824254685420857264647441)
  ·
    refine ⟨168618191014065642948485581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224824254685420857264647441 168618191014065642948485581)
    ·
      refine ⟨63231821630274616105682093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168618191014065642948485581 63231821630274616105682093)
      ·
        refine ⟨23711933111352981039630785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63231821630274616105682093 23711933111352981039630785)
        ·
          refine ⟨17783949833514735779723089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23711933111352981039630785 17783949833514735779723089)
          ·
            refine ⟨13337962375136051834792317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17783949833514735779723089 13337962375136051834792317)
            ·
              refine ⟨5001735890676019438047119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13337962375136051834792317 5001735890676019438047119)
              ·
                refine ⟨7502603836014029157070679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001735890676019438047119 7502603836014029157070679)
                ·
                  refine ⟨11253905754021043735606019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502603836014029157070679 11253905754021043735606019)
                  ·
                    refine ⟨16880858631031565603409029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11253905754021043735606019 16880858631031565603409029)
                    ·
                      refine ⟨3165160993318418550639193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16880858631031565603409029 3165160993318418550639193)
                      ·
                        rfl

theorem cell23_6164129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6164129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164129 prefixEnd_6164129 := by exact prefixLift 6164129
  have htrace : WordTrace (prefixWord ++ tailWord_6164129) baseStart_6164129 baseEnd_6164129 := by
    simpa [prefixWord, tailWord_6164129, baseEnd_6164129] using wordTrace_append hprefix tailTrace_6164129
  have hstable : (prefixWord ++ tailWord_6164129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164129).length < 2 ^ (prefixWord ++ tailWord_6164129).sum := by decide
  have hdescent : baseEnd_6164129 < baseStart_6164129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164132 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_6164132 : Nat := 118140960795 + 6164132 * 2 ^ 59
def prefixEnd_6164132 : Nat := 4983230072969 + 3 ^ 40 * 6164132 * 2
def baseEnd_6164132 : Nat := 3165162533760382038901679

theorem tailTrace_6164132 : CollatzResearch.WordTrace tailWord_6164132 prefixEnd_6164132 3165162533760382038901679 := by
  unfold tailWord_6164132
  simp only [CollatzResearch.WordTrace]
  refine ⟨112412182052204994388503325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149882909402939992518004433 112412182052204994388503325)
  ·
    refine ⟨42154568269576872895688747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112412182052204994388503325 42154568269576872895688747)
    ·
      refine ⟨63231852404365309343533121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42154568269576872895688747 63231852404365309343533121)
      ·
        refine ⟨47423889303273982007649841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63231852404365309343533121 47423889303273982007649841)
        ·
          refine ⟨35567916977455486505737381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47423889303273982007649841 35567916977455486505737381)
          ·
            refine ⟨6668984433272903719825759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35567916977455486505737381 6668984433272903719825759)
            ·
              refine ⟨10003476649909355579738639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668984433272903719825759 10003476649909355579738639)
              ·
                refine ⟨15005214974864033369607959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10003476649909355579738639 15005214974864033369607959)
                ·
                  refine ⟨22507822462296050054411939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15005214974864033369607959 22507822462296050054411939)
                  ·
                    refine ⟨33761733693444075081617909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22507822462296050054411939 33761733693444075081617909)
                    ·
                      refine ⟨3165162533760382038901679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33761733693444075081617909 3165162533760382038901679)
                      ·
                        rfl

theorem cell23_6164132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_6164132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164132 prefixEnd_6164132 := by exact prefixLift 6164132
  have htrace : WordTrace (prefixWord ++ tailWord_6164132) baseStart_6164132 baseEnd_6164132 := by
    simpa [prefixWord, tailWord_6164132, baseEnd_6164132] using wordTrace_append hprefix tailTrace_6164132
  have hstable : (prefixWord ++ tailWord_6164132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164132).length < 2 ^ (prefixWord ++ tailWord_6164132).sum := by decide
  have hdescent : baseEnd_6164132 < baseStart_6164132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164166 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6164166 : Nat := 118140960795 + 6164166 * 2 ^ 59
def prefixEnd_6164166 : Nat := 4983230072969 + 3 ^ 40 * 6164166 * 2
def baseEnd_6164166 : Nat := 3165179992102634905876523

theorem tailTrace_6164166 : CollatzResearch.WordTrace tailWord_6164166 prefixEnd_6164166 3165179992102634905876523 := by
  unfold tailWord_6164166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025800130821462893242011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149883736124191208389162901 7025800130821462893242011)
  ·
    refine ⟨10538700196232194339863017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025800130821462893242011 10538700196232194339863017)
    ·
      refine ⟨7904025147174145754897263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538700196232194339863017 7904025147174145754897263)
      ·
        refine ⟨11856037720761218632345895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904025147174145754897263 11856037720761218632345895)
        ·
          refine ⟨17784056581141827948518843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856037720761218632345895 17784056581141827948518843)
          ·
            refine ⟨26676084871712741922778265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17784056581141827948518843 26676084871712741922778265)
            ·
              refine ⟨20007063653784556442083699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26676084871712741922778265 20007063653784556442083699)
              ·
                refine ⟨30010595480676834663125549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007063653784556442083699 30010595480676834663125549)
                ·
                  refine ⟨11253973305253812998672081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30010595480676834663125549 11253973305253812998672081)
                  ·
                    refine ⟨8440479978940359749004061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11253973305253812998672081 8440479978940359749004061)
                    ·
                      refine ⟨3165179992102634905876523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440479978940359749004061 3165179992102634905876523)
                      ·
                        rfl

theorem cell23_6164166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6164166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164166 prefixEnd_6164166 := by exact prefixLift 6164166
  have htrace : WordTrace (prefixWord ++ tailWord_6164166) baseStart_6164166 baseEnd_6164166 := by
    simpa [prefixWord, tailWord_6164166, baseEnd_6164166] using wordTrace_append hprefix tailTrace_6164166
  have hstable : (prefixWord ++ tailWord_6164166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164166).length < 2 ^ (prefixWord ++ tailWord_6164166).sum := by decide
  have hdescent : baseEnd_6164166 < baseStart_6164166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164202 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_6164202 : Nat := 118140960795 + 6164202 * 2 ^ 59
def prefixEnd_6164202 : Nat := 4983230072969 + 3 ^ 40 * 6164202 * 2
def baseEnd_6164202 : Nat := 3165198477406196765026357

theorem tailTrace_6164202 : CollatzResearch.WordTrace tailWord_6164202 prefixEnd_6164202 3165198477406196765026357 := by
  unfold tailWord_6164202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56206729303539097683013715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149884611476104260488036573 56206729303539097683013715)
  ·
    refine ⟨84310093955308646524520573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56206729303539097683013715 84310093955308646524520573)
    ·
      refine ⟨31616285233240742446695215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84310093955308646524520573 31616285233240742446695215)
      ·
        refine ⟨47424427849861113670042823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31616285233240742446695215 47424427849861113670042823)
        ·
          refine ⟨71136641774791670505064235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47424427849861113670042823 71136641774791670505064235)
          ·
            refine ⟨106704962662187505757596353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71136641774791670505064235 106704962662187505757596353)
            ·
              refine ⟨80028721996640629318197265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106704962662187505757596353 80028721996640629318197265)
              ·
                refine ⟨60021541497480471988647949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80028721996640629318197265 60021541497480471988647949)
                ·
                  refine ⟨22508078061555176995742981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60021541497480471988647949 22508078061555176995742981)
                  ·
                    refine ⟨4220264636541595686701809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22508078061555176995742981 4220264636541595686701809)
                    ·
                      refine ⟨3165198477406196765026357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220264636541595686701809 3165198477406196765026357)
                      ·
                        rfl

theorem cell23_6164202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_6164202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164202 prefixEnd_6164202 := by exact prefixLift 6164202
  have htrace : WordTrace (prefixWord ++ tailWord_6164202) baseStart_6164202 baseEnd_6164202 := by
    simpa [prefixWord, tailWord_6164202, baseEnd_6164202] using wordTrace_append hprefix tailTrace_6164202
  have hstable : (prefixWord ++ tailWord_6164202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164202).length < 2 ^ (prefixWord ++ tailWord_6164202).sum := by decide
  have hdescent : baseEnd_6164202 < baseStart_6164202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164215 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_6164215 : Nat := 118140960795 + 6164215 * 2 ^ 59
def prefixEnd_6164215 : Nat := 4983230072969 + 3 ^ 40 * 6164215 * 2
def baseEnd_6164215 : Nat := 3165205152654705214163797

theorem tailTrace_6164215 : CollatzResearch.WordTrace tailWord_6164215 prefixEnd_6164215 3165205152654705214163797 := by
  unfold tailWord_6164215
  simp only [CollatzResearch.WordTrace]
  refine ⟨224827391363109293952278099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149884927575406195968185399 224827391363109293952278099)
  ·
    refine ⟨337241087044663940928417149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224827391363109293952278099 337241087044663940928417149)
    ·
      refine ⟨126465407641748977848156431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337241087044663940928417149 126465407641748977848156431)
      ·
        refine ⟨189698111462623466772234647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126465407641748977848156431 189698111462623466772234647)
        ·
          refine ⟨284547167193935200158351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189698111462623466772234647 284547167193935200158351971)
          ·
            refine ⟨426820750790902800237527957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284547167193935200158351971 426820750790902800237527957)
            ·
              refine ⟨20007222693323568761134123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 426820750790902800237527957 20007222693323568761134123)
              ·
                refine ⟨30010834039985353141701185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007222693323568761134123 30010834039985353141701185)
                ·
                  refine ⟨22508125529989014856275889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30010834039985353141701185 22508125529989014856275889)
                  ·
                    refine ⟨16881094147491761142206917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22508125529989014856275889 16881094147491761142206917)
                    ·
                      refine ⟨3165205152654705214163797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16881094147491761142206917 3165205152654705214163797)
                      ·
                        rfl

theorem cell23_6164215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_6164215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164215 prefixEnd_6164215 := by exact prefixLift 6164215
  have htrace : WordTrace (prefixWord ++ tailWord_6164215) baseStart_6164215 baseEnd_6164215 := by
    simpa [prefixWord, tailWord_6164215, baseEnd_6164215] using wordTrace_append hprefix tailTrace_6164215
  have hstable : (prefixWord ++ tailWord_6164215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164215).length < 2 ^ (prefixWord ++ tailWord_6164215).sum := by decide
  have hdescent : baseEnd_6164215 < baseStart_6164215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164225 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 7]
def baseStart_6164225 : Nat := 118140960795 + 6164225 * 2 ^ 59
def prefixEnd_6164225 : Nat := 4983230072969 + 3 ^ 40 * 6164225 * 2
def baseEnd_6164225 : Nat := 351690031940138908337639

theorem tailTrace_6164225 : CollatzResearch.WordTrace tailWord_6164225 prefixEnd_6164225 351690031940138908337639 := by
  unfold tailWord_6164225
  simp only [CollatzResearch.WordTrace]
  refine ⟨224827756093073065660142129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149885170728715377106761419 224827756093073065660142129)
  ·
    refine ⟨168620817069804799245106597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224827756093073065660142129 168620817069804799245106597)
    ·
      refine ⟨31616403200588399858457487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168620817069804799245106597 31616403200588399858457487)
      ·
        refine ⟨47424604800882599787686231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31616403200588399858457487 47424604800882599787686231)
        ·
          refine ⟨71136907201323899681529347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47424604800882599787686231 71136907201323899681529347)
          ·
            refine ⟨106705360801985849522294021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71136907201323899681529347 106705360801985849522294021)
            ·
              refine ⟨20007255150372346785430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106705360801985849522294021 20007255150372346785430129)
              ·
                refine ⟨15005441362779260089072597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20007255150372346785430129 15005441362779260089072597)
                ·
                  refine ⟨351690031940138908337639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15005441362779260089072597 351690031940138908337639)
                  ·
                    rfl

theorem cell23_6164225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_6164225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164225 prefixEnd_6164225 := by exact prefixLift 6164225
  have htrace : WordTrace (prefixWord ++ tailWord_6164225) baseStart_6164225 baseEnd_6164225 := by
    simpa [prefixWord, tailWord_6164225, baseEnd_6164225] using wordTrace_append hprefix tailTrace_6164225
  have hstable : (prefixWord ++ tailWord_6164225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164225).length < 2 ^ (prefixWord ++ tailWord_6164225).sum := by decide
  have hdescent : baseEnd_6164225 < baseStart_6164225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164235 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3]
def baseStart_6164235 : Nat := 118140960795 + 6164235 * 2 ^ 59
def prefixEnd_6164235 : Nat := 4983230072969 + 3 ^ 40 * 6164235 * 2
def baseEnd_6164235 : Nat := 3165215422267795135913705

theorem tailTrace_6164235 : CollatzResearch.WordTrace tailWord_6164235 prefixEnd_6164235 3165215422267795135913705 := by
  unfold tailWord_6164235
  simp only [CollatzResearch.WordTrace]
  refine ⟨224828120823036837368006159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149885413882024558245337439 224828120823036837368006159)
  ·
    refine ⟨337242181234555256052009239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224828120823036837368006159 337242181234555256052009239)
    ·
      refine ⟨505863271851832884078013859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337242181234555256052009239 505863271851832884078013859)
      ·
        refine ⟨758794907777749326117020789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505863271851832884078013859 758794907777749326117020789)
        ·
          refine ⟨71137022604163999323470699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 758794907777749326117020789 71137022604163999323470699)
          ·
            refine ⟨106705533906245998985206049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71137022604163999323470699 106705533906245998985206049)
            ·
              refine ⟨80029150429684499238904537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106705533906245998985206049 80029150429684499238904537)
              ·
                refine ⟨60021862822263374429178403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80029150429684499238904537 60021862822263374429178403)
                ·
                  refine ⟨90032794233395061643767605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60021862822263374429178403 90032794233395061643767605)
                  ·
                    refine ⟨8440574459380787029103213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90032794233395061643767605 8440574459380787029103213)
                    ·
                      refine ⟨3165215422267795135913705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440574459380787029103213 3165215422267795135913705)
                      ·
                        rfl

theorem cell23_6164235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 3].length) (baseStart_6164235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164235 prefixEnd_6164235 := by exact prefixLift 6164235
  have htrace : WordTrace (prefixWord ++ tailWord_6164235) baseStart_6164235 baseEnd_6164235 := by
    simpa [prefixWord, tailWord_6164235, baseEnd_6164235] using wordTrace_append hprefix tailTrace_6164235
  have hstable : (prefixWord ++ tailWord_6164235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164235).length < 2 ^ (prefixWord ++ tailWord_6164235).sum := by decide
  have hdescent : baseEnd_6164235 < baseStart_6164235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164332 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 6]
def baseStart_6164332 : Nat := 118140960795 + 6164332 * 2 ^ 59
def prefixEnd_6164332 : Nat := 4983230072969 + 3 ^ 40 * 6164332 * 2
def baseEnd_6164332 : Nat := 351696136654586806266751

theorem tailTrace_6164332 : CollatzResearch.WordTrace tailWord_6164332 prefixEnd_6164332 351696136654586806266751 := by
  unfold tailWord_6164332
  simp only [CollatzResearch.WordTrace]
  refine ⟨112415829351842711467143625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149887772469123615289524833 112415829351842711467143625)
  ·
    refine ⟨84311872013882033600357719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112415829351842711467143625 84311872013882033600357719)
    ·
      refine ⟨126467808020823050400536579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84311872013882033600357719 126467808020823050400536579)
      ·
        refine ⟨189701712031234575600804869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126467808020823050400536579 189701712031234575600804869)
        ·
          refine ⟨35569071005856482925150913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189701712031234575600804869 35569071005856482925150913)
          ·
            refine ⟨26676803254392362193863185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35569071005856482925150913 26676803254392362193863185)
            ·
              refine ⟨20007602440794271645397389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26676803254392362193863185 20007602440794271645397389)
              ·
                refine ⟨7502850915297851867024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20007602440794271645397389 7502850915297851867024021)
                ·
                  refine ⟨351696136654586806266751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7502850915297851867024021 351696136654586806266751)
                  ·
                    rfl

theorem cell23_6164332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_6164332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164332 prefixEnd_6164332 := by exact prefixLift 6164332
  have htrace : WordTrace (prefixWord ++ tailWord_6164332) baseStart_6164332 baseEnd_6164332 := by
    simpa [prefixWord, tailWord_6164332, baseEnd_6164332] using wordTrace_append hprefix tailTrace_6164332
  have hstable : (prefixWord ++ tailWord_6164332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164332).length < 2 ^ (prefixWord ++ tailWord_6164332).sum := by decide
  have hdescent : baseEnd_6164332 < baseStart_6164332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164369 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_6164369 : Nat := 118140960795 + 6164369 * 2 ^ 59
def prefixEnd_6164369 : Nat := 4983230072969 + 3 ^ 40 * 6164369 * 2
def baseEnd_6164369 : Nat := 3165284228675497611638089

theorem tailTrace_6164369 : CollatzResearch.WordTrace tailWord_6164369 prefixEnd_6164369 3165284228675497611638089 := by
  unfold tailWord_6164369
  simp only [CollatzResearch.WordTrace]
  refine ⟨224833008204551378253384161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149888672136367585502256107 224833008204551378253384161)
  ·
    refine ⟨168624756153413533690038121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224833008204551378253384161 168624756153413533690038121)
    ·
      refine ⟨126468567115060150267528591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168624756153413533690038121 126468567115060150267528591)
      ·
        refine ⟨189702850672590225401292887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126468567115060150267528591 189702850672590225401292887)
        ·
          refine ⟨284554276008885338101939331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189702850672590225401292887 284554276008885338101939331)
          ·
            refine ⟨426831414013328007152908997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284554276008885338101939331 426831414013328007152908997)
            ·
              refine ⟨80030890127499001341170437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 426831414013328007152908997 80030890127499001341170437)
              ·
                refine ⟨15005791898906062751469457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80030890127499001341170437 15005791898906062751469457)
                ·
                  refine ⟨11254343924179547063602093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15005791898906062751469457 11254343924179547063602093)
                  ·
                    refine ⟨4220378971567330148850785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11254343924179547063602093 4220378971567330148850785)
                    ·
                      refine ⟨3165284228675497611638089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220378971567330148850785 3165284228675497611638089)
                      ·
                        rfl

theorem cell23_6164369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_6164369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164369 prefixEnd_6164369 := by exact prefixLift 6164369
  have htrace : WordTrace (prefixWord ++ tailWord_6164369) baseStart_6164369 baseEnd_6164369 := by
    simpa [prefixWord, tailWord_6164369, baseEnd_6164369] using wordTrace_append hprefix tailTrace_6164369
  have hstable : (prefixWord ++ tailWord_6164369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164369).length < 2 ^ (prefixWord ++ tailWord_6164369).sum := by decide
  have hdescent : baseEnd_6164369 < baseStart_6164369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164399 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 4]
def baseStart_6164399 : Nat := 118140960795 + 6164399 * 2 ^ 59
def prefixEnd_6164399 : Nat := 4983230072969 + 3 ^ 40 * 6164399 * 2
def baseEnd_6164399 : Nat := 3165299633095132494262951

theorem tailTrace_6164399 : CollatzResearch.WordTrace tailWord_6164399 prefixEnd_6164399 3165299633095132494262951 := by
  unfold tailWord_6164399
  simp only [CollatzResearch.WordTrace]
  refine ⟨224834102394442693376976251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149889401596295128917984167 224834102394442693376976251)
  ·
    refine ⟨337251153591664040065464377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224834102394442693376976251 337251153591664040065464377)
    ·
      refine ⟨252938365193748030049098283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337251153591664040065464377 252938365193748030049098283)
      ·
        refine ⟨379407547790622045073647425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252938365193748030049098283 379407547790622045073647425)
        ·
          refine ⟨284555660842966533805235569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379407547790622045073647425 284555660842966533805235569)
          ·
            refine ⟨213416745632224900353926677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284555660842966533805235569 213416745632224900353926677)
            ·
              refine ⟨10003909951510542204090313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213416745632224900353926677 10003909951510542204090313)
              ·
                refine ⟨7502932463632906653067735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10003909951510542204090313 7502932463632906653067735)
                ·
                  refine ⟨11254398695449359979601603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502932463632906653067735 11254398695449359979601603)
                  ·
                    refine ⟨16881598043174039969402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11254398695449359979601603 16881598043174039969402405)
                    ·
                      refine ⟨3165299633095132494262951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16881598043174039969402405 3165299633095132494262951)
                      ·
                        rfl

theorem cell23_6164399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_6164399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164399 prefixEnd_6164399 := by exact prefixLift 6164399
  have htrace : WordTrace (prefixWord ++ tailWord_6164399) baseStart_6164399 baseEnd_6164399 := by
    simpa [prefixWord, tailWord_6164399, baseEnd_6164399] using wordTrace_append hprefix tailTrace_6164399
  have hstable : (prefixWord ++ tailWord_6164399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164399).length < 2 ^ (prefixWord ++ tailWord_6164399).sum := by decide
  have hdescent : baseEnd_6164399 < baseStart_6164399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164402 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_6164402 : Nat := 118140960795 + 6164402 * 2 ^ 59
def prefixEnd_6164402 : Nat := 4983230072969 + 3 ^ 40 * 6164402 * 2
def baseEnd_6164402 : Nat := 3165301173537095982525437

theorem tailTrace_6164402 : CollatzResearch.WordTrace tailWord_6164402 prefixEnd_6164402 3165301173537095982525437 := by
  unfold tailWord_6164402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56208552953357956222333865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149889474542287883259556973 56208552953357956222333865)
  ·
    refine ⟨42156414715018467166750399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56208552953357956222333865 42156414715018467166750399)
    ·
      refine ⟨63234622072527700750125599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42156414715018467166750399 63234622072527700750125599)
      ·
        refine ⟨94851933108791551125188399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63234622072527700750125599 94851933108791551125188399)
        ·
          refine ⟨142277899663187326687782599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94851933108791551125188399 142277899663187326687782599)
          ·
            refine ⟨213416849494780990031673899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142277899663187326687782599 213416849494780990031673899)
            ·
              refine ⟨320125274242171485047510849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213416849494780990031673899 320125274242171485047510849)
              ·
                refine ⟨240093955681628613785633137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320125274242171485047510849 240093955681628613785633137)
                ·
                  refine ⟨180070466761221460339224853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240093955681628613785633137 180070466761221460339224853)
                  ·
                    refine ⟨8440803129432255953401165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 180070466761221460339224853 8440803129432255953401165)
                    ·
                      refine ⟨3165301173537095982525437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440803129432255953401165 3165301173537095982525437)
                      ·
                        rfl

theorem cell23_6164402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_6164402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164402 prefixEnd_6164402 := by exact prefixLift 6164402
  have htrace : WordTrace (prefixWord ++ tailWord_6164402) baseStart_6164402 baseEnd_6164402 := by
    simpa [prefixWord, tailWord_6164402, baseEnd_6164402] using wordTrace_append hprefix tailTrace_6164402
  have hstable : (prefixWord ++ tailWord_6164402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164402).length < 2 ^ (prefixWord ++ tailWord_6164402).sum := by decide
  have hdescent : baseEnd_6164402 < baseStart_6164402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164450 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6164450 : Nat := 118140960795 + 6164450 * 2 ^ 59
def prefixEnd_6164450 : Nat := 4983230072969 + 3 ^ 40 * 6164450 * 2
def baseEnd_6164450 : Nat := 3165325820608511794725217

theorem tailTrace_6164450 : CollatzResearch.WordTrace tailWord_6164450 prefixEnd_6164450 3165325820608511794725217 := by
  unfold tailWord_6164450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56208990629314482271770701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149890641678171952724721869 56208990629314482271770701)
  ·
    refine ⟨21078371485992930851914013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56208990629314482271770701 21078371485992930851914013)
    ·
      refine ⟨7904389307247349069467755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21078371485992930851914013 7904389307247349069467755)
      ·
        refine ⟨11856583960871023604201633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904389307247349069467755 11856583960871023604201633)
        ·
          refine ⟨8892437970653267703151225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856583960871023604201633 8892437970653267703151225)
          ·
            refine ⟨6669328477989950777363419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8892437970653267703151225 6669328477989950777363419)
            ·
              refine ⟨10003992716984926166045129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669328477989950777363419 10003992716984926166045129)
              ·
                refine ⟨7502994537738694624533847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10003992716984926166045129 7502994537738694624533847)
                ·
                  refine ⟨11254491806608041936800771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502994537738694624533847 11254491806608041936800771)
                  ·
                    refine ⟨16881737709912062905201157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11254491806608041936800771 16881737709912062905201157)
                    ·
                      refine ⟨3165325820608511794725217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16881737709912062905201157 3165325820608511794725217)
                      ·
                        rfl

theorem cell23_6164450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6164450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164450 prefixEnd_6164450 := by exact prefixLift 6164450
  have htrace : WordTrace (prefixWord ++ tailWord_6164450) baseStart_6164450 baseEnd_6164450 := by
    simpa [prefixWord, tailWord_6164450, baseEnd_6164450] using wordTrace_append hprefix tailTrace_6164450
  have hstable : (prefixWord ++ tailWord_6164450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164450).length < 2 ^ (prefixWord ++ tailWord_6164450).sum := by decide
  have hdescent : baseEnd_6164450 < baseStart_6164450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164470 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6164470 : Nat := 118140960795 + 6164470 * 2 ^ 59
def prefixEnd_6164470 : Nat := 4983230072969 + 3 ^ 40 * 6164470 * 2
def baseEnd_6164470 : Nat := 3165336090221601716475125

theorem tailTrace_6164470 : CollatzResearch.WordTrace tailWord_6164470 prefixEnd_6164470 3165336090221601716475125 := by
  unfold tailWord_6164470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052293248574092031425679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149891127984790315001873909 14052293248574092031425679)
  ·
    refine ⟨21078439872861138047138519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14052293248574092031425679 21078439872861138047138519)
    ·
      refine ⟨31617659809291707070707779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21078439872861138047138519 31617659809291707070707779)
      ·
        refine ⟨47426489713937560606061669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31617659809291707070707779 47426489713937560606061669)
        ·
          refine ⟨8892466821363292613636563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47426489713937560606061669 8892466821363292613636563)
          ·
            refine ⟨13338700232044938920454845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892466821363292613636563 13338700232044938920454845)
            ·
              refine ⟨5002012587016852095170567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13338700232044938920454845 5002012587016852095170567)
              ·
                refine ⟨7503018880525278142755851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002012587016852095170567 7503018880525278142755851)
                ·
                  refine ⟨11254528320787917214133777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7503018880525278142755851 11254528320787917214133777)
                  ·
                    refine ⟨8440896240590937910600333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11254528320787917214133777 8440896240590937910600333)
                    ·
                      refine ⟨3165336090221601716475125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440896240590937910600333 3165336090221601716475125)
                      ·
                        rfl

theorem cell23_6164470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6164470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164470 prefixEnd_6164470 := by exact prefixLift 6164470
  have htrace : WordTrace (prefixWord ++ tailWord_6164470) baseStart_6164470 baseEnd_6164470 := by
    simpa [prefixWord, tailWord_6164470, baseEnd_6164470] using wordTrace_append hprefix tailTrace_6164470
  have hstable : (prefixWord ++ tailWord_6164470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164470).length < 2 ^ (prefixWord ++ tailWord_6164470).sum := by decide
  have hdescent : baseEnd_6164470 < baseStart_6164470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164500 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6164500 : Nat := 118140960795 + 6164500 * 2 ^ 59
def prefixEnd_6164500 : Nat := 4983230072969 + 3 ^ 40 * 6164500 * 2
def baseEnd_6164500 : Nat := 3165351494641236599099987

theorem tailTrace_6164500 : CollatzResearch.WordTrace tailWord_6164500 prefixEnd_6164500 3165351494641236599099987 := by
  unfold tailWord_6164500
  simp only [CollatzResearch.WordTrace]
  refine ⟨112418893083538393813201477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149891857444717858417601969 112418893083538393813201477)
  ·
    refine ⟨21078542453163448839975277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112418893083538393813201477 21078542453163448839975277)
    ·
      refine ⟨7904453419936293314990729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21078542453163448839975277 7904453419936293314990729)
      ·
        refine ⟨5928340064952219986243047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904453419936293314990729 5928340064952219986243047)
        ·
          refine ⟨8892510097428329979364571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928340064952219986243047 8892510097428329979364571)
          ·
            refine ⟨13338765146142494969046857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892510097428329979364571 13338765146142494969046857)
            ·
              refine ⟨10004073859606871226785143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13338765146142494969046857 10004073859606871226785143)
              ·
                refine ⟨15006110789410306840177715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004073859606871226785143 15006110789410306840177715)
                ·
                  refine ⟨22509166184115460260266573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15006110789410306840177715 22509166184115460260266573)
                  ·
                    refine ⟨8440937319043297597599965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22509166184115460260266573 8440937319043297597599965)
                    ·
                      refine ⟨3165351494641236599099987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8440937319043297597599965 3165351494641236599099987)
                      ·
                        rfl

theorem cell23_6164500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6164500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164500 prefixEnd_6164500 := by exact prefixLift 6164500
  have htrace : WordTrace (prefixWord ++ tailWord_6164500) baseStart_6164500 baseEnd_6164500 := by
    simpa [prefixWord, tailWord_6164500, baseEnd_6164500] using wordTrace_append hprefix tailTrace_6164500
  have hstable : (prefixWord ++ tailWord_6164500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164500).length < 2 ^ (prefixWord ++ tailWord_6164500).sum := by decide
  have hdescent : baseEnd_6164500 < baseStart_6164500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164506 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_6164506 : Nat := 118140960795 + 6164506 * 2 ^ 59
def prefixEnd_6164506 : Nat := 4983230072969 + 3 ^ 40 * 6164506 * 2
def baseEnd_6164506 : Nat := 3165354575525163575624959

theorem tailTrace_6164506 : CollatzResearch.WordTrace tailWord_6164506 prefixEnd_6164506 3165354575525163575624959 := by
  unfold tailWord_6164506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56209501251263762662780343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149892003336703367100747581 56209501251263762662780343)
  ·
    refine ⟨84314251876895643994170515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56209501251263762662780343 84314251876895643994170515)
    ·
      refine ⟨126471377815343465991255773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84314251876895643994170515 126471377815343465991255773)
      ·
        refine ⟨47426766680753799746720915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126471377815343465991255773 47426766680753799746720915)
        ·
          refine ⟨71140150021130699620081373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47426766680753799746720915 71140150021130699620081373)
          ·
            refine ⟨26677556257924012357530515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71140150021130699620081373 26677556257924012357530515)
            ·
              refine ⟨40016334386886018536295773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26677556257924012357530515 40016334386886018536295773)
              ·
                refine ⟨15006125395082256951110915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40016334386886018536295773 15006125395082256951110915)
                ·
                  refine ⟨22509188092623385426666373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15006125395082256951110915 22509188092623385426666373)
                  ·
                    refine ⟨4220472767366884767499945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22509188092623385426666373 4220472767366884767499945)
                    ·
                      refine ⟨3165354575525163575624959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220472767366884767499945 3165354575525163575624959)
                      ·
                        rfl

theorem cell23_6164506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_6164506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164506 prefixEnd_6164506 := by exact prefixLift 6164506
  have htrace : WordTrace (prefixWord ++ tailWord_6164506) baseStart_6164506 baseEnd_6164506 := by
    simpa [prefixWord, tailWord_6164506, baseEnd_6164506] using wordTrace_append hprefix tailTrace_6164506
  have hstable : (prefixWord ++ tailWord_6164506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164506).length < 2 ^ (prefixWord ++ tailWord_6164506).sum := by decide
  have hdescent : baseEnd_6164506 < baseStart_6164506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164557 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6164557 : Nat := 118140960795 + 6164557 * 2 ^ 59
def prefixEnd_6164557 : Nat := 4983230072969 + 3 ^ 40 * 6164557 * 2
def baseEnd_6164557 : Nat := 3165380763038542876087225

theorem tailTrace_6164557 : CollatzResearch.WordTrace tailWord_6164557 prefixEnd_6164557 3165380763038542876087225 := by
  unfold tailWord_6164557
  simp only [CollatzResearch.WordTrace]
  refine ⟨224839865127870286361227925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149893243418580190907485283 224839865127870286361227925)
  ·
    refine ⟨10539368677868919673182559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224839865127870286361227925 10539368677868919673182559)
    ·
      refine ⟨15809053016803379509773839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10539368677868919673182559 15809053016803379509773839)
      ·
        refine ⟨23713579525205069264660759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15809053016803379509773839 23713579525205069264660759)
        ·
          refine ⟨35570369287807603896991139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23713579525205069264660759 35570369287807603896991139)
          ·
            refine ⟨53355553931711405845486709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35570369287807603896991139 53355553931711405845486709)
            ·
              refine ⟨5002083181097944298014379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53355553931711405845486709 5002083181097944298014379)
              ·
                refine ⟨7503124771646916447021569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002083181097944298014379 7503124771646916447021569)
                ·
                  refine ⟨5627343578735187335266177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503124771646916447021569 5627343578735187335266177)
                  ·
                    refine ⟨4220507684051390501449633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5627343578735187335266177 4220507684051390501449633)
                    ·
                      refine ⟨3165380763038542876087225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220507684051390501449633 3165380763038542876087225)
                      ·
                        rfl

theorem cell23_6164557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6164557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164557 prefixEnd_6164557 := by exact prefixLift 6164557
  have htrace : WordTrace (prefixWord ++ tailWord_6164557) baseStart_6164557 baseEnd_6164557 := by
    simpa [prefixWord, tailWord_6164557, baseEnd_6164557] using wordTrace_append hprefix tailTrace_6164557
  have hstable : (prefixWord ++ tailWord_6164557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164557).length < 2 ^ (prefixWord ++ tailWord_6164557).sum := by decide
  have hdescent : baseEnd_6164557 < baseStart_6164557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164579 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6164579 : Nat := 118140960795 + 6164579 * 2 ^ 59
def prefixEnd_6164579 : Nat := 4983230072969 + 3 ^ 40 * 6164579 * 2
def baseEnd_6164579 : Nat := 3165392059612941790012123

theorem tailTrace_6164579 : CollatzResearch.WordTrace tailWord_6164579 prefixEnd_6164579 3165392059612941790012123 := by
  unfold tailWord_6164579
  simp only [CollatzResearch.WordTrace]
  refine ⟨224840667533790584118528791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149893778355860389412352527 224840667533790584118528791)
  ·
    refine ⟨337261001300685876177793187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224840667533790584118528791 337261001300685876177793187)
    ·
      refine ⟨505891501951028814266689781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337261001300685876177793187 505891501951028814266689781)
      ·
        refine ⟨47427328307908951337502167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 505891501951028814266689781 47427328307908951337502167)
        ·
          refine ⟨71140992461863427006253251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47427328307908951337502167 71140992461863427006253251)
          ·
            refine ⟨106711488692795140509379877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71140992461863427006253251 106711488692795140509379877)
            ·
              refine ⟨20008404129899088845508727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106711488692795140509379877 20008404129899088845508727)
              ·
                refine ⟨30012606194848633268263091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20008404129899088845508727 30012606194848633268263091)
                ·
                  refine ⟨45018909292272949902394637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30012606194848633268263091 45018909292272949902394637)
                  ·
                    refine ⟨16882090984602356213397989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45018909292272949902394637 16882090984602356213397989)
                    ·
                      refine ⟨3165392059612941790012123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16882090984602356213397989 3165392059612941790012123)
                      ·
                        rfl

theorem cell23_6164579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6164579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164579 prefixEnd_6164579 := by exact prefixLift 6164579
  have htrace : WordTrace (prefixWord ++ tailWord_6164579) baseStart_6164579 baseEnd_6164579 := by
    simpa [prefixWord, tailWord_6164579, baseEnd_6164579] using wordTrace_append hprefix tailTrace_6164579
  have hstable : (prefixWord ++ tailWord_6164579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164579).length < 2 ^ (prefixWord ++ tailWord_6164579).sum := by decide
  have hdescent : baseEnd_6164579 < baseStart_6164579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164653 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6164653 : Nat := 118140960795 + 6164653 * 2 ^ 59
def prefixEnd_6164653 : Nat := 4983230072969 + 3 ^ 40 * 6164653 * 2
def baseEnd_6164653 : Nat := 351714450797930500054087

theorem tailTrace_6164653 : CollatzResearch.WordTrace tailWord_6164653 prefixEnd_6164653 351714450797930500054087 := by
  unfold tailWord_6164653
  simp only [CollatzResearch.WordTrace]
  refine ⟨224843366535522494756722613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149895577690348329837815075 224843366535522494756722613)
  ·
    refine ⟨21079065612705233883442745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224843366535522494756722613 21079065612705233883442745)
    ·
      refine ⟨15809299209528925412582059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21079065612705233883442745 15809299209528925412582059)
      ·
        refine ⟨23713948814293388118873089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15809299209528925412582059 23713948814293388118873089)
        ·
          refine ⟨17785461610720041089154817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23713948814293388118873089 17785461610720041089154817)
          ·
            refine ⟨13339096208040030816866113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17785461610720041089154817 13339096208040030816866113)
            ·
              refine ⟨10004322156030023112649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13339096208040030816866113 10004322156030023112649585)
              ·
                refine ⟨7503241617022517334487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10004322156030023112649585 7503241617022517334487189)
                ·
                  refine ⟨351714450797930500054087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7503241617022517334487189 351714450797930500054087)
                  ·
                    rfl

theorem cell23_6164653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6164653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164653 prefixEnd_6164653 := by exact prefixLift 6164653
  have htrace : WordTrace (prefixWord ++ tailWord_6164653) baseStart_6164653 baseEnd_6164653 := by
    simpa [prefixWord, tailWord_6164653, baseEnd_6164653] using wordTrace_append hprefix tailTrace_6164653
  have hstable : (prefixWord ++ tailWord_6164653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164653).length < 2 ^ (prefixWord ++ tailWord_6164653).sum := by decide
  have hdescent : baseEnd_6164653 < baseStart_6164653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164690 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6164690 : Nat := 118140960795 + 6164690 * 2 ^ 59
def prefixEnd_6164690 : Nat := 4983230072969 + 3 ^ 40 * 6164690 * 2
def baseEnd_6164690 : Nat := 3165449055965590855724113

theorem tailTrace_6164690 : CollatzResearch.WordTrace tailWord_6164690 prefixEnd_6164690 3165449055965590855724113 := by
  unfold tailWord_6164690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211179009097112518954881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149896477357592300050546349 56211179009097112518954881)
  ·
    refine ⟨42158384256822834389216161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56211179009097112518954881 42158384256822834389216161)
    ·
      refine ⟨31618788192617125791912121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42158384256822834389216161 31618788192617125791912121)
      ·
        refine ⟨23714091144462844343934091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31618788192617125791912121 23714091144462844343934091)
        ·
          refine ⟨35571136716694266515901137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23714091144462844343934091 35571136716694266515901137)
          ·
            refine ⟨26678352537520699886925853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35571136716694266515901137 26678352537520699886925853)
            ·
              refine ⟨10004382201570262457597195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26678352537520699886925853 10004382201570262457597195)
              ·
                refine ⟨15006573302355393686395793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004382201570262457597195 15006573302355393686395793)
                ·
                  refine ⟨11254929976766545264796845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15006573302355393686395793 11254929976766545264796845)
                  ·
                    refine ⟨4220598741287454474298817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11254929976766545264796845 4220598741287454474298817)
                    ·
                      refine ⟨3165449055965590855724113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220598741287454474298817 3165449055965590855724113)
                      ·
                        rfl

theorem cell23_6164690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6164690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164690 prefixEnd_6164690 := by exact prefixLift 6164690
  have htrace : WordTrace (prefixWord ++ tailWord_6164690) baseStart_6164690 baseEnd_6164690 := by
    simpa [prefixWord, tailWord_6164690, baseEnd_6164690] using wordTrace_append hprefix tailTrace_6164690
  have hstable : (prefixWord ++ tailWord_6164690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164690).length < 2 ^ (prefixWord ++ tailWord_6164690).sum := by decide
  have hdescent : baseEnd_6164690 < baseStart_6164690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164696 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_6164696 : Nat := 118140960795 + 6164696 * 2 ^ 59
def prefixEnd_6164696 : Nat := 4983230072969 + 3 ^ 40 * 6164696 * 2
def baseEnd_6164696 : Nat := 1055150712283172610749695

theorem tailTrace_6164696 : CollatzResearch.WordTrace tailWord_6164696 prefixEnd_6164696 1055150712283172610749695 := by
  unfold tailWord_6164696
  simp only [CollatzResearch.WordTrace]
  refine ⟨112422467437183356550268971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149896623249577808733691961 112422467437183356550268971)
  ·
    refine ⟨168633701155775034825403457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112422467437183356550268971 168633701155775034825403457)
    ·
      refine ⟨126475275866831276119052593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168633701155775034825403457 126475275866831276119052593)
      ·
        refine ⟨94856456900123457089289445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126475275866831276119052593 94856456900123457089289445)
        ·
          refine ⟨17785585668773148204241771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94856456900123457089289445 17785585668773148204241771)
          ·
            refine ⟨26678378503159722306362657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785585668773148204241771 26678378503159722306362657)
            ·
              refine ⟨20008783877369791729771993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26678378503159722306362657 20008783877369791729771993)
              ·
                refine ⟨15006587908027343797328995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20008783877369791729771993 15006587908027343797328995)
                ·
                  refine ⟨22509881862041015695993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15006587908027343797328995 22509881862041015695993493)
                  ·
                    refine ⟨1055150712283172610749695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22509881862041015695993493 1055150712283172610749695)
                    ·
                      rfl

theorem cell23_6164696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_6164696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164696 prefixEnd_6164696 := by exact prefixLift 6164696
  have htrace : WordTrace (prefixWord ++ tailWord_6164696) baseStart_6164696 baseEnd_6164696 := by
    simpa [prefixWord, tailWord_6164696, baseEnd_6164696] using wordTrace_append hprefix tailTrace_6164696
  have hstable : (prefixWord ++ tailWord_6164696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164696).length < 2 ^ (prefixWord ++ tailWord_6164696).sum := by decide
  have hdescent : baseEnd_6164696 < baseStart_6164696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164703 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 7, 2, 2]
def baseStart_6164703 : Nat := 118140960795 + 6164703 * 2 ^ 59
def prefixEnd_6164703 : Nat := 4983230072969 + 3 ^ 40 * 6164703 * 2
def baseEnd_6164703 : Nat := 3165455731214099304861553

theorem tailTrace_6164703 : CollatzResearch.WordTrace tailWord_6164703 prefixEnd_6164703 3165455731214099304861553 := by
  unfold tailWord_6164703
  simp only [CollatzResearch.WordTrace]
  refine ⟨224845190185341353296042763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149896793456894235530695175 224845190185341353296042763)
  ·
    refine ⟨337267785278012029944064145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224845190185341353296042763 337267785278012029944064145)
    ·
      refine ⟨252950838958509022458048109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337267785278012029944064145 252950838958509022458048109)
      ·
        refine ⟨94856564609440883421768041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252950838958509022458048109 94856564609440883421768041)
        ·
          refine ⟨71142423457080662566326031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94856564609440883421768041 71142423457080662566326031)
          ·
            refine ⟨106713635185620993849489047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71142423457080662566326031 106713635185620993849489047)
            ·
              refine ⟨160070452778431490774233571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106713635185620993849489047 160070452778431490774233571)
              ·
                refine ⟨240105679167647236161350357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160070452778431490774233571 240105679167647236161350357)
                ·
                  refine ⟨5627476855491732097531649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 240105679167647236161350357 5627476855491732097531649)
                  ·
                    refine ⟨4220607641618799073148737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5627476855491732097531649 4220607641618799073148737)
                    ·
                      refine ⟨3165455731214099304861553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220607641618799073148737 3165455731214099304861553)
                      ·
                        rfl

theorem cell23_6164703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_6164703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164703 prefixEnd_6164703 := by exact prefixLift 6164703
  have htrace : WordTrace (prefixWord ++ tailWord_6164703) baseStart_6164703 baseEnd_6164703 := by
    simpa [prefixWord, tailWord_6164703, baseEnd_6164703] using wordTrace_append hprefix tailTrace_6164703
  have hstable : (prefixWord ++ tailWord_6164703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164703).length < 2 ^ (prefixWord ++ tailWord_6164703).sum := by decide
  have hdescent : baseEnd_6164703 < baseStart_6164703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6164729 : Nat := 118140960795 + 6164729 * 2 ^ 59
def prefixEnd_6164729 : Nat := 4983230072969 + 3 ^ 40 * 6164729 * 2
def baseEnd_6164729 : Nat := 3165469081711116203136433

theorem tailTrace_6164729 : CollatzResearch.WordTrace tailWord_6164729 prefixEnd_6164729 3165469081711116203136433 := by
  unfold tailWord_6164729
  simp only [CollatzResearch.WordTrace]
  refine ⟨224846138483247159736489241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149897425655498106490992827 224846138483247159736489241)
  ·
    refine ⟨168634603862435369802366931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224846138483247159736489241 168634603862435369802366931)
    ·
      refine ⟨252951905793653054703550397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168634603862435369802366931 252951905793653054703550397)
      ·
        refine ⟨94856964672619895513831399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252951905793653054703550397 94856964672619895513831399)
        ·
          refine ⟨142285447008929843270747099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94856964672619895513831399 142285447008929843270747099)
          ·
            refine ⟨213428170513394764906120649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142285447008929843270747099 213428170513394764906120649)
            ·
              refine ⟨160071127885046073679590487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213428170513394764906120649 160071127885046073679590487)
              ·
                refine ⟨240106691827569110519385731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160071127885046073679590487 240106691827569110519385731)
                ·
                  refine ⟨360160037741353665779078597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240106691827569110519385731 360160037741353665779078597)
                  ·
                    refine ⟨67530007076503812333577237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360160037741353665779078597 67530007076503812333577237)
                    ·
                      refine ⟨3165469081711116203136433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67530007076503812333577237 3165469081711116203136433)
                      ·
                        rfl

theorem cell23_6164729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6164729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164729 prefixEnd_6164729 := by exact prefixLift 6164729
  have htrace : WordTrace (prefixWord ++ tailWord_6164729) baseStart_6164729 baseEnd_6164729 := by
    simpa [prefixWord, tailWord_6164729, baseEnd_6164729] using wordTrace_append hprefix tailTrace_6164729
  have hstable : (prefixWord ++ tailWord_6164729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164729).length < 2 ^ (prefixWord ++ tailWord_6164729).sum := by decide
  have hdescent : baseEnd_6164729 < baseStart_6164729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164730 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_6164730 : Nat := 118140960795 + 6164730 * 2 ^ 59
def prefixEnd_6164730 : Nat := 4983230072969 + 3 ^ 40 * 6164730 * 2
def baseEnd_6164730 : Nat := 1055156531730590233074643

theorem tailTrace_6164730 : CollatzResearch.WordTrace tailWord_6164730 prefixEnd_6164730 1055156531730590233074643 := by
  unfold tailWord_6164730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211543739060884226818911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149897449970829024604850429 56211543739060884226818911)
  ·
    refine ⟨84317315608591326340228367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56211543739060884226818911 84317315608591326340228367)
    ·
      refine ⟨126475973412886989510342551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84317315608591326340228367 126475973412886989510342551)
      ·
        refine ⟨189713960119330484265513827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126475973412886989510342551 189713960119330484265513827)
        ·
          refine ⟨284570940178995726398270741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189713960119330484265513827 284570940178995726398270741)
          ·
            refine ⟨13339262820890424674918941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 284570940178995726398270741 13339262820890424674918941)
            ·
              refine ⟨5002223557833909253094603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13339262820890424674918941 5002223557833909253094603)
              ·
                refine ⟨7503335336750863879641905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002223557833909253094603 7503335336750863879641905)
                ·
                  refine ⟨5627501502563147909731429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503335336750863879641905 5627501502563147909731429)
                  ·
                    refine ⟨1055156531730590233074643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5627501502563147909731429 1055156531730590233074643)
                    ·
                      rfl

theorem cell23_6164730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_6164730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164730 prefixEnd_6164730 := by exact prefixLift 6164730
  have htrace : WordTrace (prefixWord ++ tailWord_6164730) baseStart_6164730 baseEnd_6164730 := by
    simpa [prefixWord, tailWord_6164730, baseEnd_6164730] using wordTrace_append hprefix tailTrace_6164730
  have hstable : (prefixWord ++ tailWord_6164730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164730).length < 2 ^ (prefixWord ++ tailWord_6164730).sum := by decide
  have hdescent : baseEnd_6164730 < baseStart_6164730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164743 : List Nat := [1, 1, 4, 5, 1, 1, 1, 9]
def baseStart_6164743 : Nat := 118140960795 + 6164743 * 2 ^ 59
def prefixEnd_6164743 : Nat := 4983230072969 + 3 ^ 40 * 6164743 * 2
def baseEnd_6164743 : Nat := 117239861868158486976347

theorem tailTrace_6164743 : CollatzResearch.WordTrace tailWord_6164743 prefixEnd_6164743 117239861868158486976347 := by
  unfold tailWord_6164743
  simp only [CollatzResearch.WordTrace]
  refine ⟨224846649105196440127498883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149897766070130960084999255 224846649105196440127498883)
  ·
    refine ⟨337269973657794660191248325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224846649105196440127498883 337269973657794660191248325)
    ·
      refine ⟨63238120060836498785859061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337269973657794660191248325 63238120060836498785859061)
      ·
        refine ⟨5928573755703421761174287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63238120060836498785859061 5928573755703421761174287)
        ·
          refine ⟨8892860633555132641761431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928573755703421761174287 8892860633555132641761431)
          ·
            refine ⟨13339290950332698962642147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892860633555132641761431 13339290950332698962642147)
            ·
              refine ⟨20008936425499048443963221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13339290950332698962642147 20008936425499048443963221)
              ·
                refine ⟨117239861868158486976347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20008936425499048443963221 117239861868158486976347)
                ·
                  rfl

theorem cell23_6164743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 9].length) (baseStart_6164743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164743 prefixEnd_6164743 := by exact prefixLift 6164743
  have htrace : WordTrace (prefixWord ++ tailWord_6164743) baseStart_6164743 baseEnd_6164743 := by
    simpa [prefixWord, tailWord_6164743, baseEnd_6164743] using wordTrace_append hprefix tailTrace_6164743
  have hstable : (prefixWord ++ tailWord_6164743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164743).length < 2 ^ (prefixWord ++ tailWord_6164743).sum := by decide
  have hdescent : baseEnd_6164743 < baseStart_6164743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164753 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_6164753 : Nat := 118140960795 + 6164753 * 2 ^ 59
def prefixEnd_6164753 : Nat := 4983230072969 + 3 ^ 40 * 6164753 * 2
def baseEnd_6164753 : Nat := 3165481405246824109236323

theorem tailTrace_6164753 : CollatzResearch.WordTrace tailWord_6164753 prefixEnd_6164753 3165481405246824109236323 := by
  unfold tailWord_6164753
  simp only [CollatzResearch.WordTrace]
  refine ⟨224847013835160211835362913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149898009223440141223575275 224847013835160211835362913)
  ·
    refine ⟨168635260376370158876522185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224847013835160211835362913 168635260376370158876522185)
    ·
      refine ⟨126476445282277619157391639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168635260376370158876522185 126476445282277619157391639)
      ·
        refine ⟨189714667923416428736087459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126476445282277619157391639 189714667923416428736087459)
        ·
          refine ⟨284572001885124643104131189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189714667923416428736087459 284572001885124643104131189)
          ·
            refine ⟨26678625176730435291012299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284572001885124643104131189 26678625176730435291012299)
            ·
              refine ⟨40017937765095652936518449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26678625176730435291012299 40017937765095652936518449)
              ·
                refine ⟨30013453323821739702388837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40017937765095652936518449 30013453323821739702388837)
                ·
                  refine ⟨5627522498216576194197907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30013453323821739702388837 5627522498216576194197907)
                  ·
                    refine ⟨8441283747324864291296861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5627522498216576194197907 8441283747324864291296861)
                    ·
                      refine ⟨3165481405246824109236323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8441283747324864291296861 3165481405246824109236323)
                      ·
                        rfl

theorem cell23_6164753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_6164753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164753 prefixEnd_6164753 := by exact prefixLift 6164753
  have htrace : WordTrace (prefixWord ++ tailWord_6164753) baseStart_6164753 baseEnd_6164753 := by
    simpa [prefixWord, tailWord_6164753, baseEnd_6164753] using wordTrace_append hprefix tailTrace_6164753
  have hstable : (prefixWord ++ tailWord_6164753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164753).length < 2 ^ (prefixWord ++ tailWord_6164753).sum := by decide
  have hdescent : baseEnd_6164753 < baseStart_6164753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164770 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_6164770 : Nat := 118140960795 + 6164770 * 2 ^ 59
def prefixEnd_6164770 : Nat := 4983230072969 + 3 ^ 40 * 6164770 * 2
def baseEnd_6164770 : Nat := 3165490134417950542723745

theorem tailTrace_6164770 : CollatzResearch.WordTrace tailWord_6164770 prefixEnd_6164770 3165490134417950542723745 := by
  unfold tailWord_6164770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211908469024655934682941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149898422584065749159154509 56211908469024655934682941)
  ·
    refine ⟨21079465675884245975506103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56211908469024655934682941 21079465675884245975506103)
    ·
      refine ⟨31619198513826368963259155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21079465675884245975506103 31619198513826368963259155)
      ·
        refine ⟨47428797770739553444888733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31619198513826368963259155 47428797770739553444888733)
        ·
          refine ⟨17785799164027332541833275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47428797770739553444888733 17785799164027332541833275)
          ·
            refine ⟨26678698746040998812749913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785799164027332541833275 26678698746040998812749913)
            ·
              refine ⟨20009024059530749109562435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26678698746040998812749913 20009024059530749109562435)
              ·
                refine ⟨30013536089296123664343653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20009024059530749109562435 30013536089296123664343653)
                ·
                  refine ⟨5627538016743023187064435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30013536089296123664343653 5627538016743023187064435)
                  ·
                    refine ⟨8441307025114534780596653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5627538016743023187064435 8441307025114534780596653)
                    ·
                      refine ⟨3165490134417950542723745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8441307025114534780596653 3165490134417950542723745)
                      ·
                        rfl

theorem cell23_6164770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_6164770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164770 prefixEnd_6164770 := by exact prefixLift 6164770
  have htrace : WordTrace (prefixWord ++ tailWord_6164770) baseStart_6164770 baseEnd_6164770 := by
    simpa [prefixWord, tailWord_6164770, baseEnd_6164770] using wordTrace_append hprefix tailTrace_6164770
  have hstable : (prefixWord ++ tailWord_6164770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164770).length < 2 ^ (prefixWord ++ tailWord_6164770).sum := by decide
  have hdescent : baseEnd_6164770 < baseStart_6164770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164781 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6164781 : Nat := 118140960795 + 6164781 * 2 ^ 59
def prefixEnd_6164781 : Nat := 4983230072969 + 3 ^ 40 * 6164781 * 2
def baseEnd_6164781 : Nat := 1055165260901716666562065

theorem tailTrace_6164781 : CollatzResearch.WordTrace tailWord_6164781 prefixEnd_6164781 1055165260901716666562065 := by
  unfold tailWord_6164781
  simp only [CollatzResearch.WordTrace]
  refine ⟨224848035079058772617382197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149898690052705848411588131 224848035079058772617382197)
  ·
    refine ⟨21079503288661759932879581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224848035079058772617382197 21079503288661759932879581)
    ·
      refine ⟨7904813733248159974829843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21079503288661759932879581 7904813733248159974829843)
      ·
        refine ⟨11857220599872239962244765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904813733248159974829843 11857220599872239962244765)
        ·
          refine ⟨4446457724952089985841787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11857220599872239962244765 4446457724952089985841787)
          ·
            refine ⟨6669686587428134978762681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446457724952089985841787 6669686587428134978762681)
            ·
              refine ⟨5002264940571101234072011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669686587428134978762681 5002264940571101234072011)
              ·
                refine ⟨7503397410856651851108017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002264940571101234072011 7503397410856651851108017)
                ·
                  refine ⟨5627548058142488888331013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503397410856651851108017 5627548058142488888331013)
                  ·
                    refine ⟨1055165260901716666562065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5627548058142488888331013 1055165260901716666562065)
                    ·
                      rfl

theorem cell23_6164781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6164781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164781 prefixEnd_6164781 := by exact prefixLift 6164781
  have htrace : WordTrace (prefixWord ++ tailWord_6164781) baseStart_6164781 baseEnd_6164781 := by
    simpa [prefixWord, tailWord_6164781, baseEnd_6164781] using wordTrace_append hprefix tailTrace_6164781
  have hstable : (prefixWord ++ tailWord_6164781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164781).length < 2 ^ (prefixWord ++ tailWord_6164781).sum := by decide
  have hdescent : baseEnd_6164781 < baseStart_6164781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164796 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_6164796 : Nat := 118140960795 + 6164796 * 2 ^ 59
def prefixEnd_6164796 : Nat := 4983230072969 + 3 ^ 40 * 6164796 * 2
def baseEnd_6164796 : Nat := 3165503484914967440998625

theorem tailTrace_6164796 : CollatzResearch.WordTrace tailWord_6164796 prefixEnd_6164796 3165503484914967440998625 := by
  unfold tailWord_6164796
  simp only [CollatzResearch.WordTrace]
  refine ⟨112424291087002215089589121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149899054782669620119452161 112424291087002215089589121)
  ·
    refine ⟨84318218315251661317191841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112424291087002215089589121 84318218315251661317191841)
    ·
      refine ⟨63238663736438745987893881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84318218315251661317191841 63238663736438745987893881)
      ·
        refine ⟨47428997802329059490920411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63238663736438745987893881 47428997802329059490920411)
        ·
          refine ⟨71143496703493589236380617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47428997802329059490920411 71143496703493589236380617)
          ·
            refine ⟨53357622527620191927285463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71143496703493589236380617 53357622527620191927285463)
            ·
              refine ⟨80036433791430287890928195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53357622527620191927285463 80036433791430287890928195)
              ·
                refine ⟨120054650687145431836392293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80036433791430287890928195 120054650687145431836392293)
                ·
                  refine ⟨22510247003839768469323555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120054650687145431836392293 22510247003839768469323555)
                  ·
                    refine ⟨33765370505759652703985333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22510247003839768469323555 33765370505759652703985333)
                    ·
                      refine ⟨3165503484914967440998625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33765370505759652703985333 3165503484914967440998625)
                      ·
                        rfl

theorem cell23_6164796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_6164796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164796 prefixEnd_6164796 := by exact prefixLift 6164796
  have htrace : WordTrace (prefixWord ++ tailWord_6164796) baseStart_6164796 baseEnd_6164796 := by
    simpa [prefixWord, tailWord_6164796, baseEnd_6164796] using wordTrace_append hprefix tailTrace_6164796
  have hstable : (prefixWord ++ tailWord_6164796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164796).length < 2 ^ (prefixWord ++ tailWord_6164796).sum := by decide
  have hdescent : baseEnd_6164796 < baseStart_6164796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164900 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_6164900 : Nat := 118140960795 + 6164900 * 2 ^ 59
def prefixEnd_6164900 : Nat := 4983230072969 + 3 ^ 40 * 6164900 * 2
def baseEnd_6164900 : Nat := 3165556886903035034098147

theorem tailTrace_6164900 : CollatzResearch.WordTrace tailWord_6164900 prefixEnd_6164900 3165556886903035034098147 := by
  unfold tailWord_6164900
  simp only [CollatzResearch.WordTrace]
  refine ⟨112426187682813827970482077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149901583577085103960642769 112426187682813827970482077)
  ·
    refine ⟨42159820381055185488930779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112426187682813827970482077 42159820381055185488930779)
    ·
      refine ⟨63239730571582778233396169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42159820381055185488930779 63239730571582778233396169)
      ·
        refine ⟨47429797928687083675047127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63239730571582778233396169 47429797928687083675047127)
        ·
          refine ⟨71144696893030625512570691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47429797928687083675047127 71144696893030625512570691)
          ·
            refine ⟨106717045339545938268856037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71144696893030625512570691 106717045339545938268856037)
            ·
              refine ⟨20009446001164863425410507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106717045339545938268856037 20009446001164863425410507)
              ·
                refine ⟨30014169001747295138115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20009446001164863425410507 30014169001747295138115761)
                ·
                  refine ⟨22510626751310471353586821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30014169001747295138115761 22510626751310471353586821)
                  ·
                    refine ⟨4220742515870713378797529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22510626751310471353586821 4220742515870713378797529)
                    ·
                      refine ⟨3165556886903035034098147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220742515870713378797529 3165556886903035034098147)
                      ·
                        rfl

theorem cell23_6164900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_6164900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164900 prefixEnd_6164900 := by exact prefixLift 6164900
  have htrace : WordTrace (prefixWord ++ tailWord_6164900) baseStart_6164900 baseEnd_6164900 := by
    simpa [prefixWord, tailWord_6164900, baseEnd_6164900] using wordTrace_append hprefix tailTrace_6164900
  have hstable : (prefixWord ++ tailWord_6164900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164900).length < 2 ^ (prefixWord ++ tailWord_6164900).sum := by decide
  have hdescent : baseEnd_6164900 < baseStart_6164900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164953 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_6164953 : Nat := 118140960795 + 6164953 * 2 ^ 59
def prefixEnd_6164953 : Nat := 4983230072969 + 3 ^ 40 * 6164953 * 2
def baseEnd_6164953 : Nat := 1055194700459241108911801

theorem tailTrace_6164953 : CollatzResearch.WordTrace tailWord_6164953 prefixEnd_6164953 1055194700459241108911801 := by
  unfold tailWord_6164953
  simp only [CollatzResearch.WordTrace]
  refine ⟨224854308434435645992643513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149902872289623763995095675 224854308434435645992643513)
  ·
    refine ⟨168640731325826734494482635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224854308434435645992643513 168640731325826734494482635)
    ·
      refine ⟨252961096988740101741723953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168640731325826734494482635 252961096988740101741723953)
      ·
        refine ⟨189720822741555076306292965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252961096988740101741723953 189720822741555076306292965)
        ·
          refine ⟨35572654264041576807429931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189720822741555076306292965 35572654264041576807429931)
          ·
            refine ⟨53358981396062365211144897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35572654264041576807429931 53358981396062365211144897)
            ·
              refine ⟨40019236047046773908358673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53358981396062365211144897 40019236047046773908358673)
              ·
                refine ⟨30014427035285080431269005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40019236047046773908358673 30014427035285080431269005)
                ·
                  refine ⟨11255410138231905161725877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30014427035285080431269005 11255410138231905161725877)
                  ·
                    refine ⟨1055194700459241108911801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11255410138231905161725877 1055194700459241108911801)
                    ·
                      rfl

theorem cell23_6164953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_6164953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164953 prefixEnd_6164953 := by exact prefixLift 6164953
  have htrace : WordTrace (prefixWord ++ tailWord_6164953) baseStart_6164953 baseEnd_6164953 := by
    simpa [prefixWord, tailWord_6164953, baseEnd_6164953] using wordTrace_append hprefix tailTrace_6164953
  have hstable : (prefixWord ++ tailWord_6164953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164953).length < 2 ^ (prefixWord ++ tailWord_6164953).sum := by decide
  have hdescent : baseEnd_6164953 < baseStart_6164953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164960 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2]
def baseStart_6164960 : Nat := 118140960795 + 6164960 * 2 ^ 59
def prefixEnd_6164960 : Nat := 4983230072969 + 3 ^ 40 * 6164960 * 2
def baseEnd_6164960 : Nat := 3165587695742304799347871

theorem tailTrace_6164960 : CollatzResearch.WordTrace tailWord_6164960 prefixEnd_6164960 3165587695742304799347871 := by
  unfold tailWord_6164960
  simp only [CollatzResearch.WordTrace]
  refine ⟨112427281872705143094074167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149903042496940190792098889 112427281872705143094074167)
  ·
    refine ⟨168640922809057714641111251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112427281872705143094074167 168640922809057714641111251)
    ·
      refine ⟨252961384213586571961666877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168640922809057714641111251 252961384213586571961666877)
      ·
        refine ⟨94860519080094964485625079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252961384213586571961666877 94860519080094964485625079)
        ·
          refine ⟨142290778620142446728437619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94860519080094964485625079 142290778620142446728437619)
          ·
            refine ⟨213436167930213670092656429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142290778620142446728437619 213436167930213670092656429)
            ·
              refine ⟨80038562973830126284746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213436167930213670092656429 80038562973830126284746161)
              ·
                refine ⟨60028922230372594713559621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80038562973830126284746161 60028922230372594713559621)
                ·
                  refine ⟨11255422918194861508792429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60028922230372594713559621 11255422918194861508792429)
                  ·
                    refine ⟨4220783594323073065797161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11255422918194861508792429 4220783594323073065797161)
                    ·
                      refine ⟨3165587695742304799347871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220783594323073065797161 3165587695742304799347871)
                      ·
                        rfl

theorem cell23_6164960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_6164960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164960 prefixEnd_6164960 := by exact prefixLift 6164960
  have htrace : WordTrace (prefixWord ++ tailWord_6164960) baseStart_6164960 baseEnd_6164960 := by
    simpa [prefixWord, tailWord_6164960, baseEnd_6164960] using wordTrace_append hprefix tailTrace_6164960
  have hstable : (prefixWord ++ tailWord_6164960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164960).length < 2 ^ (prefixWord ++ tailWord_6164960).sum := by decide
  have hdescent : baseEnd_6164960 < baseStart_6164960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164970 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_6164970 : Nat := 118140960795 + 6164970 * 2 ^ 59
def prefixEnd_6164970 : Nat := 4983230072969 + 3 ^ 40 * 6164970 * 2
def baseEnd_6164970 : Nat := 1055197610182949920074275

theorem tailTrace_6164970 : CollatzResearch.WordTrace tailWord_6164970 prefixEnd_6164970 1055197610182949920074275 := by
  unfold tailWord_6164970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56213732118843514474003091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149903285650249371930674909 56213732118843514474003091)
  ·
    refine ⟨84320598178265271711004637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56213732118843514474003091 84320598178265271711004637)
    ·
      refine ⟨31620224316849476891626739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84320598178265271711004637 31620224316849476891626739)
      ·
        refine ⟨47430336475274215337440109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31620224316849476891626739 47430336475274215337440109)
        ·
          refine ⟨17786376178227830751540041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47430336475274215337440109 17786376178227830751540041)
          ·
            refine ⟨13339782133670873063655031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17786376178227830751540041 13339782133670873063655031)
            ·
              refine ⟨20009673200506309595482547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13339782133670873063655031 20009673200506309595482547)
              ·
                refine ⟨30014509800759464393223821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20009673200506309595482547 30014509800759464393223821)
                ·
                  refine ⟨11255441175284799147458933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30014509800759464393223821 11255441175284799147458933)
                  ·
                    refine ⟨1055197610182949920074275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11255441175284799147458933 1055197610182949920074275)
                    ·
                      rfl

theorem cell23_6164970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_6164970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164970 prefixEnd_6164970 := by exact prefixLift 6164970
  have htrace : WordTrace (prefixWord ++ tailWord_6164970) baseStart_6164970 baseEnd_6164970 := by
    simpa [prefixWord, tailWord_6164970, baseEnd_6164970] using wordTrace_append hprefix tailTrace_6164970
  have hstable : (prefixWord ++ tailWord_6164970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164970).length < 2 ^ (prefixWord ++ tailWord_6164970).sum := by decide
  have hdescent : baseEnd_6164970 < baseStart_6164970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6164977 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_6164977 : Nat := 118140960795 + 6164977 * 2 ^ 59
def prefixEnd_6164977 : Nat := 4983230072969 + 3 ^ 40 * 6164977 * 2
def baseEnd_6164977 : Nat := 3165596424913431232835293

theorem tailTrace_6164977 : CollatzResearch.WordTrace tailWord_6164977 prefixEnd_6164977 3165596424913431232835293 := by
  unfold tailWord_6164977
  simp only [CollatzResearch.WordTrace]
  refine ⟨224855183786348698091517185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149903455857565798727678123 224855183786348698091517185)
  ·
    refine ⟨168641387839761523568637889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224855183786348698091517185 168641387839761523568637889)
    ·
      refine ⟨126481040879821142676478417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168641387839761523568637889 126481040879821142676478417)
      ·
        refine ⟨94860780659865857007358813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126481040879821142676478417 94860780659865857007358813)
        ·
          refine ⟨35572792747449696377759555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94860780659865857007358813 35572792747449696377759555)
          ·
            refine ⟨53359189121174544566639333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35572792747449696377759555 53359189121174544566639333)
            ·
              refine ⟨10004847960220227106244875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53359189121174544566639333 10004847960220227106244875)
              ·
                refine ⟨15007271940330340659367313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004847960220227106244875 15007271940330340659367313)
                ·
                  refine ⟨11255453955247755494525485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15007271940330340659367313 11255453955247755494525485)
                  ·
                    refine ⟨4220795233217908310447057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11255453955247755494525485 4220795233217908310447057)
                    ·
                      refine ⟨3165596424913431232835293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220795233217908310447057 3165596424913431232835293)
                      ·
                        rfl

theorem cell23_6164977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_6164977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6164977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6164977 prefixEnd_6164977 := by exact prefixLift 6164977
  have htrace : WordTrace (prefixWord ++ tailWord_6164977) baseStart_6164977 baseEnd_6164977 := by
    simpa [prefixWord, tailWord_6164977, baseEnd_6164977] using wordTrace_append hprefix tailTrace_6164977
  have hstable : (prefixWord ++ tailWord_6164977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6164977).length < 2 ^ (prefixWord ++ tailWord_6164977).sum := by decide
  have hdescent : baseEnd_6164977 < baseStart_6164977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6164977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165020 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6165020 : Nat := 118140960795 + 6165020 * 2 ^ 59
def prefixEnd_6165020 : Nat := 4983230072969 + 3 ^ 40 * 6165020 * 2
def baseEnd_6165020 : Nat := 3165618504581574564597595

theorem tailTrace_6165020 : CollatzResearch.WordTrace tailWord_6165020 prefixEnd_6165020 3165618504581574564597595 := by
  unfold tailWord_6165020
  simp only [CollatzResearch.WordTrace]
  refine ⟨112428376062596458217666257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149904501416795277623555009 112428376062596458217666257)
  ·
    refine ⟨84321282046947343663249693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112428376062596458217666257 84321282046947343663249693)
    ·
      refine ⟨31620480767605253873718635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84321282046947343663249693 31620480767605253873718635)
      ·
        refine ⟨47430721151407880810577953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31620480767605253873718635 47430721151407880810577953)
        ·
          refine ⟨35573040863555910607933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47430721151407880810577953 35573040863555910607933465)
          ·
            refine ⟨26679780647666932955950099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35573040863555910607933465 26679780647666932955950099)
            ·
              refine ⟨40019670971500399433925149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26679780647666932955950099 40019670971500399433925149)
              ·
                refine ⟨15007376614312649787721931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40019670971500399433925149 15007376614312649787721931)
                ·
                  refine ⟨22511064921468974681582897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15007376614312649787721931 22511064921468974681582897)
                  ·
                    refine ⟨16883298691101731011187173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22511064921468974681582897 16883298691101731011187173)
                    ·
                      refine ⟨3165618504581574564597595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16883298691101731011187173 3165618504581574564597595)
                      ·
                        rfl

theorem cell23_6165020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6165020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165020 prefixEnd_6165020 := by exact prefixLift 6165020
  have htrace : WordTrace (prefixWord ++ tailWord_6165020) baseStart_6165020 baseEnd_6165020 := by
    simpa [prefixWord, tailWord_6165020, baseEnd_6165020] using wordTrace_append hprefix tailTrace_6165020
  have hstable : (prefixWord ++ tailWord_6165020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165020).length < 2 ^ (prefixWord ++ tailWord_6165020).sum := by decide
  have hdescent : baseEnd_6165020 < baseStart_6165020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165028 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6165028 : Nat := 118140960795 + 6165028 * 2 ^ 59
def prefixEnd_6165028 : Nat := 4983230072969 + 3 ^ 40 * 6165028 * 2
def baseEnd_6165028 : Nat := 3165622612426810533297559

theorem tailTrace_6165028 : CollatzResearch.WordTrace tailWord_6165028 prefixEnd_6165028 3165622612426810533297559 := by
  unfold tailWord_6165028
  simp only [CollatzResearch.WordTrace]
  refine ⟨112428521954581966900811869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149904695939442622534415825 112428521954581966900811869)
  ·
    refine ⟨42160695732968237587804451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112428521954581966900811869 42160695732968237587804451)
    ·
      refine ⟨63241043599452356381706677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42160695732968237587804451 63241043599452356381706677)
      ·
        refine ⟨5928847837448658410785001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63241043599452356381706677 5928847837448658410785001)
        ·
          refine ⟨4446635878086493808088751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928847837448658410785001 4446635878086493808088751)
          ·
            refine ⟨6669953817129740712133127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446635878086493808088751 6669953817129740712133127)
            ·
              refine ⟨10004930725694611068199691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669953817129740712133127 10004930725694611068199691)
              ·
                refine ⟨15007396088541916602299537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004930725694611068199691 15007396088541916602299537)
                ·
                  refine ⟨11255547066406437451724653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15007396088541916602299537 11255547066406437451724653)
                  ·
                    refine ⟨4220830149902414044396745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11255547066406437451724653 4220830149902414044396745)
                    ·
                      refine ⟨3165622612426810533297559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4220830149902414044396745 3165622612426810533297559)
                      ·
                        rfl

theorem cell23_6165028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6165028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165028 prefixEnd_6165028 := by exact prefixLift 6165028
  have htrace : WordTrace (prefixWord ++ tailWord_6165028) baseStart_6165028 baseEnd_6165028 := by
    simpa [prefixWord, tailWord_6165028, baseEnd_6165028] using wordTrace_append hprefix tailTrace_6165028
  have hstable : (prefixWord ++ tailWord_6165028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165028).length < 2 ^ (prefixWord ++ tailWord_6165028).sum := by decide
  have hdescent : baseEnd_6165028 < baseStart_6165028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165040 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_6165040 : Nat := 118140960795 + 6165040 * 2 ^ 59
def prefixEnd_6165040 : Nat := 4983230072969 + 3 ^ 40 * 6165040 * 2
def baseEnd_6165040 : Nat := 3165628774194664486347503

theorem tailTrace_6165040 : CollatzResearch.WordTrace tailWord_6165040 prefixEnd_6165040 3165628774194664486347503 := by
  unfold tailWord_6165040
  simp only [CollatzResearch.WordTrace]
  refine ⟨112428740792560229925530287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149904987723413639900707049 112428740792560229925530287)
  ·
    refine ⟨168643111188840344888295431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112428740792560229925530287 168643111188840344888295431)
    ·
      refine ⟨252964666783260517332443147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168643111188840344888295431 252964666783260517332443147)
      ·
        refine ⟨379447000174890775998664721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252964666783260517332443147 379447000174890775998664721)
        ·
          refine ⟨284585250131168081998998541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379447000174890775998664721 284585250131168081998998541)
          ·
            refine ⟨106719468799188030749624453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284585250131168081998998541 106719468799188030749624453)
            ·
              refine ⟨20009900399847755765554585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106719468799188030749624453 20009900399847755765554585)
              ·
                refine ⟨15007425299885816824165939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20009900399847755765554585 15007425299885816824165939)
                ·
                  refine ⟨22511137949828725236248909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15007425299885816824165939 22511137949828725236248909)
                  ·
                    refine ⟨8441676731185771963593341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22511137949828725236248909 8441676731185771963593341)
                    ·
                      refine ⟨3165628774194664486347503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8441676731185771963593341 3165628774194664486347503)
                      ·
                        rfl

theorem cell23_6165040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_6165040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165040 prefixEnd_6165040 := by exact prefixLift 6165040
  have htrace : WordTrace (prefixWord ++ tailWord_6165040) baseStart_6165040 baseEnd_6165040 := by
    simpa [prefixWord, tailWord_6165040, baseEnd_6165040] using wordTrace_append hprefix tailTrace_6165040
  have hstable : (prefixWord ++ tailWord_6165040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165040).length < 2 ^ (prefixWord ++ tailWord_6165040).sum := by decide
  have hdescent : baseEnd_6165040 < baseStart_6165040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165103 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 9]
def baseStart_6165103 : Nat := 118140960795 + 6165103 * 2 ^ 59
def prefixEnd_6165103 : Nat := 4983230072969 + 3 ^ 40 * 6165103 * 2
def baseEnd_6165103 : Nat := 351740124830655304428857

theorem tailTrace_6165103 : CollatzResearch.WordTrace tailWord_6165103 prefixEnd_6165103 351740124830655304428857 := by
  unfold tailWord_6165103
  simp only [CollatzResearch.WordTrace]
  refine ⟨224859779383892221610603963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149906519589261481073735975 224859779383892221610603963)
  ·
    refine ⟨337289669075838332415905945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224859779383892221610603963 337289669075838332415905945)
    ·
      refine ⟨252967251806878749311929459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337289669075838332415905945 252967251806878749311929459)
      ·
        refine ⟨379450877710318123967894189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252967251806878749311929459 379450877710318123967894189)
        ·
          refine ⟨142294079141369296487960321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379450877710318123967894189 142294079141369296487960321)
          ·
            refine ⟨106720559356026972365970241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142294079141369296487960321 106720559356026972365970241)
            ·
              refine ⟨80040419517020229274477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106720559356026972365970241 80040419517020229274477681)
              ·
                refine ⟨60030314637765171955858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80040419517020229274477681 60030314637765171955858261)
                ·
                  refine ⟨351740124830655304428857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60030314637765171955858261 351740124830655304428857)
                  ·
                    rfl

theorem cell23_6165103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 9].length) (baseStart_6165103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165103 prefixEnd_6165103 := by exact prefixLift 6165103
  have htrace : WordTrace (prefixWord ++ tailWord_6165103) baseStart_6165103 baseEnd_6165103 := by
    simpa [prefixWord, tailWord_6165103, baseEnd_6165103] using wordTrace_append hprefix tailTrace_6165103
  have hstable : (prefixWord ++ tailWord_6165103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165103).length < 2 ^ (prefixWord ++ tailWord_6165103).sum := by decide
  have hdescent : baseEnd_6165103 < baseStart_6165103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165120 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 7]
def baseStart_6165120 : Nat := 118140960795 + 6165120 * 2 ^ 59
def prefixEnd_6165120 : Nat := 4983230072969 + 3 ^ 40 * 6165120 * 2
def baseEnd_6165120 : Nat := 351741094738558241483015

theorem tailTrace_6165120 : CollatzResearch.WordTrace tailWord_6165120 prefixEnd_6165120 351741094738558241483015 := by
  unfold tailWord_6165120
  simp only [CollatzResearch.WordTrace]
  refine ⟨112430199712415316756986407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149906932949887089009315209 112430199712415316756986407)
  ·
    refine ⟨168645299568622975135479611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112430199712415316756986407 168645299568622975135479611)
    ·
      refine ⟨252967949352934462703219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168645299568622975135479611 252967949352934462703219417)
      ·
        refine ⟨189725962014700847027414563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252967949352934462703219417 189725962014700847027414563)
        ·
          refine ⟨284588943022051270541121845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189725962014700847027414563 284588943022051270541121845)
          ·
            refine ⟨26680213408317306613230173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284588943022051270541121845 26680213408317306613230173)
            ·
              refine ⟨10005080028118989979961315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26680213408317306613230173 10005080028118989979961315)
              ·
                refine ⟨15007620042178484969941973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10005080028118989979961315 15007620042178484969941973)
                ·
                  refine ⟨351741094738558241483015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15007620042178484969941973 351741094738558241483015)
                  ·
                    rfl

theorem cell23_6165120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_6165120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165120 prefixEnd_6165120 := by exact prefixLift 6165120
  have htrace : WordTrace (prefixWord ++ tailWord_6165120) baseStart_6165120 baseEnd_6165120 := by
    simpa [prefixWord, tailWord_6165120, baseEnd_6165120] using wordTrace_append hprefix tailTrace_6165120
  have hstable : (prefixWord ++ tailWord_6165120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165120).length < 2 ^ (prefixWord ++ tailWord_6165120).sum := by decide
  have hdescent : baseEnd_6165120 < baseStart_6165120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165170 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6165170 : Nat := 118140960795 + 6165170 * 2 ^ 59
def prefixEnd_6165170 : Nat := 4983230072969 + 3 ^ 40 * 6165170 * 2
def baseEnd_6165170 : Nat := 3165695526679748977721905

theorem tailTrace_6165170 : CollatzResearch.WordTrace tailWord_6165170 prefixEnd_6165170 3165695526679748977721905 := by
  unfold tailWord_6165170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56215555768662373013323241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149908148716432994702195309 56215555768662373013323241)
  ·
    refine ⟨42161666826496779759992431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56215555768662373013323241 42161666826496779759992431)
    ·
      refine ⟨63242500239745169639988647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42161666826496779759992431 63242500239745169639988647)
      ·
        refine ⟨94863750359617754459982971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63242500239745169639988647 94863750359617754459982971)
        ·
          refine ⟨142295625539426631689974457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94863750359617754459982971 142295625539426631689974457)
          ·
            refine ⟨106721719154569973767480843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142295625539426631689974457 106721719154569973767480843)
            ·
              refine ⟨160082578731854960651221265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106721719154569973767480843 160082578731854960651221265)
              ·
                refine ⟨120061934048891220488415949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160082578731854960651221265 120061934048891220488415949)
                ·
                  refine ⟨45023225268334207683155981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120061934048891220488415949 45023225268334207683155981)
                  ·
                    refine ⟨16883709475625327881183493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45023225268334207683155981 16883709475625327881183493)
                    ·
                      refine ⟨3165695526679748977721905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16883709475625327881183493 3165695526679748977721905)
                      ·
                        rfl

theorem cell23_6165170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6165170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165170 prefixEnd_6165170 := by exact prefixLift 6165170
  have htrace : WordTrace (prefixWord ++ tailWord_6165170) baseStart_6165170 baseEnd_6165170 := by
    simpa [prefixWord, tailWord_6165170, baseEnd_6165170] using wordTrace_append hprefix tailTrace_6165170
  have hstable : (prefixWord ++ tailWord_6165170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165170).length < 2 ^ (prefixWord ++ tailWord_6165170).sum := by decide
  have hdescent : baseEnd_6165170 < baseStart_6165170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165204 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6165204 : Nat := 118140960795 + 6165204 * 2 ^ 59
def prefixEnd_6165204 : Nat := 4983230072969 + 3 ^ 40 * 6165204 * 2
def baseEnd_6165204 : Nat := 3165712985022001844696749

theorem tailTrace_6165204 : CollatzResearch.WordTrace tailWord_6165204 prefixEnd_6165204 3165712985022001844696749 := by
  unfold tailWord_6165204
  simp only [CollatzResearch.WordTrace]
  refine ⟨112431731578263157930015333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149908975437684210573353777 112431731578263157930015333)
  ·
    refine ⟨21080949670924342111877875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112431731578263157930015333 21080949670924342111877875)
    ·
      refine ⟨31621424506386513167816813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21080949670924342111877875 31621424506386513167816813)
      ·
        refine ⟨11858034189894942437931305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31621424506386513167816813 11858034189894942437931305)
        ·
          refine ⟨8893525642421206828448479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11858034189894942437931305 8893525642421206828448479)
          ·
            refine ⟨13340288463631810242672719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893525642421206828448479 13340288463631810242672719)
            ·
              refine ⟨20010432695447715364009079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340288463631810242672719 20010432695447715364009079)
              ·
                refine ⟨30015649043171573046013619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20010432695447715364009079 30015649043171573046013619)
                ·
                  refine ⟨45023473564757359569020429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30015649043171573046013619 45023473564757359569020429)
                  ·
                    refine ⟨16883802586784009838382661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45023473564757359569020429 16883802586784009838382661)
                    ·
                      refine ⟨3165712985022001844696749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16883802586784009838382661 3165712985022001844696749)
                      ·
                        rfl

theorem cell23_6165204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6165204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165204 prefixEnd_6165204 := by exact prefixLift 6165204
  have htrace : WordTrace (prefixWord ++ tailWord_6165204) baseStart_6165204 baseEnd_6165204 := by
    simpa [prefixWord, tailWord_6165204, baseEnd_6165204] using wordTrace_append hprefix tailTrace_6165204
  have hstable : (prefixWord ++ tailWord_6165204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165204).length < 2 ^ (prefixWord ++ tailWord_6165204).sum := by decide
  have hdescent : baseEnd_6165204 < baseStart_6165204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165207 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_6165207 : Nat := 118140960795 + 6165207 * 2 ^ 59
def prefixEnd_6165207 : Nat := 4983230072969 + 3 ^ 40 * 6165207 * 2
def baseEnd_6165207 : Nat := 3165714525463965332959235

theorem tailTrace_6165207 : CollatzResearch.WordTrace tailWord_6165207 prefixEnd_6165207 3165714525463965332959235 := by
  unfold tailWord_6165207
  simp only [CollatzResearch.WordTrace]
  refine ⟨224863572575515447372389875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149909048383676964914926583 224863572575515447372389875)
  ·
    refine ⟨337295358863273171058584813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224863572575515447372389875 337295358863273171058584813)
    ·
      refine ⟨126485759573727439146969305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337295358863273171058584813 126485759573727439146969305)
      ·
        refine ⟨94864319680295579360226979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126485759573727439146969305 94864319680295579360226979)
        ·
          refine ⟨142296479520443369040340469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94864319680295579360226979 142296479520443369040340469)
          ·
            refine ⟨13340294955041565847531919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142296479520443369040340469 13340294955041565847531919)
            ·
              refine ⟨20010442432562348771297879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340294955041565847531919 20010442432562348771297879)
              ·
                refine ⟨30015663648843523156946819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20010442432562348771297879 30015663648843523156946819)
                ·
                  refine ⟨45023495473265284735420229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30015663648843523156946819 45023495473265284735420229)
                  ·
                    refine ⟨8441905401237240887891293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45023495473265284735420229 8441905401237240887891293)
                    ·
                      refine ⟨3165714525463965332959235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8441905401237240887891293 3165714525463965332959235)
                      ·
                        rfl

theorem cell23_6165207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_6165207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165207 prefixEnd_6165207 := by exact prefixLift 6165207
  have htrace : WordTrace (prefixWord ++ tailWord_6165207) baseStart_6165207 baseEnd_6165207 := by
    simpa [prefixWord, tailWord_6165207, baseEnd_6165207] using wordTrace_append hprefix tailTrace_6165207
  have hstable : (prefixWord ++ tailWord_6165207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165207).length < 2 ^ (prefixWord ++ tailWord_6165207).sum := by decide
  have hdescent : baseEnd_6165207 < baseStart_6165207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165210 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_6165210 : Nat := 118140960795 + 6165210 * 2 ^ 59
def prefixEnd_6165210 : Nat := 4983230072969 + 3 ^ 40 * 6165210 * 2
def baseEnd_6165210 : Nat := 351746229545103202357969

theorem tailTrace_6165210 : CollatzResearch.WordTrace tailWord_6165210 prefixEnd_6165210 351746229545103202357969 := by
  unfold tailWord_6165210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56215920498626144721187271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149909121329669719256499389 56215920498626144721187271)
  ·
    refine ⟨84323880747939217081780907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56215920498626144721187271 84323880747939217081780907)
    ·
      refine ⟨126485821121908825622671361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84323880747939217081780907 126485821121908825622671361)
      ·
        refine ⟨94864365841431619217003521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126485821121908825622671361 94864365841431619217003521)
        ·
          refine ⟨71148274381073714412752641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94864365841431619217003521 71148274381073714412752641)
          ·
            refine ⟨53361205785805285809564481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71148274381073714412752641 53361205785805285809564481)
            ·
              refine ⟨40020904339353964357173361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53361205785805285809564481 40020904339353964357173361)
              ·
                refine ⟨30015678254515473267880021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40020904339353964357173361 30015678254515473267880021)
                ·
                  refine ⟨351746229545103202357969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30015678254515473267880021 351746229545103202357969)
                  ·
                    rfl

theorem cell23_6165210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_6165210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165210 prefixEnd_6165210 := by exact prefixLift 6165210
  have htrace : WordTrace (prefixWord ++ tailWord_6165210) baseStart_6165210 baseEnd_6165210 := by
    simpa [prefixWord, tailWord_6165210, baseEnd_6165210] using wordTrace_append hprefix tailTrace_6165210
  have hstable : (prefixWord ++ tailWord_6165210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165210).length < 2 ^ (prefixWord ++ tailWord_6165210).sum := by decide
  have hdescent : baseEnd_6165210 < baseStart_6165210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165244 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 6]
def baseStart_6165244 : Nat := 118140960795 + 6165244 * 2 ^ 59
def prefixEnd_6165244 : Nat := 4983230072969 + 3 ^ 40 * 6165244 * 2
def baseEnd_6165244 : Nat := 351748169360909076466285

theorem tailTrace_6165244 : CollatzResearch.WordTrace tailWord_6165244 prefixEnd_6165244 351748169360909076466285 := by
  unfold tailWord_6165244
  simp only [CollatzResearch.WordTrace]
  refine ⟨112432461038190701345743393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149909948050920935127657857 112432461038190701345743393)
  ·
    refine ⟨84324345778643026009307545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112432461038190701345743393 84324345778643026009307545)
    ·
      refine ⟨63243259333982269506980659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84324345778643026009307545 63243259333982269506980659)
      ·
        refine ⟨94864889000973404260470989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63243259333982269506980659 94864889000973404260470989)
        ·
          refine ⟨35574333375365026597676621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94864889000973404260470989 35574333375365026597676621)
          ·
            refine ⟨13340375015761884974128733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35574333375365026597676621 13340375015761884974128733)
            ·
              refine ⟨5002640630910706865298275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13340375015761884974128733 5002640630910706865298275)
              ·
                refine ⟨7503960946366060297947413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002640630910706865298275 7503960946366060297947413)
                ·
                  refine ⟨351748169360909076466285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7503960946366060297947413 351748169360909076466285)
                  ·
                    rfl

theorem cell23_6165244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_6165244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165244 prefixEnd_6165244 := by exact prefixLift 6165244
  have htrace : WordTrace (prefixWord ++ tailWord_6165244) baseStart_6165244 baseEnd_6165244 := by
    simpa [prefixWord, tailWord_6165244, baseEnd_6165244] using wordTrace_append hprefix tailTrace_6165244
  have hstable : (prefixWord ++ tailWord_6165244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165244).length < 2 ^ (prefixWord ++ tailWord_6165244).sum := by decide
  have hdescent : baseEnd_6165244 < baseStart_6165244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165257 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_6165257 : Nat := 118140960795 + 6165257 * 2 ^ 59
def prefixEnd_6165257 : Nat := 4983230072969 + 3 ^ 40 * 6165257 * 2
def baseEnd_6165257 : Nat := 1055246733165563379111335

theorem tailTrace_6165257 : CollatzResearch.WordTrace tailWord_6165257 prefixEnd_6165257 1055246733165563379111335 := by
  unfold tailWord_6165257
  simp only [CollatzResearch.WordTrace]
  refine ⟨224865396225334305911710025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149910264150222870607806683 224865396225334305911710025)
  ·
    refine ⟨168649047169000729433782519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224865396225334305911710025 168649047169000729433782519)
    ·
      refine ⟨252973570753501094150673779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168649047169000729433782519 252973570753501094150673779)
      ·
        refine ⟨379460356130251641226010669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252973570753501094150673779 379460356130251641226010669)
        ·
          refine ⟨142297633548844365459754001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379460356130251641226010669 142297633548844365459754001)
          ·
            refine ⟨106723225161633274094815501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142297633548844365459754001 106723225161633274094815501)
            ·
              refine ⟨40021209435612477785555813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106723225161633274094815501 40021209435612477785555813)
              ·
                refine ⟨7503976769177339584791715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40021209435612477785555813 7503976769177339584791715)
                ·
                  refine ⟨11255965153766009377187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7503976769177339584791715 11255965153766009377187573)
                  ·
                    refine ⟨1055246733165563379111335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11255965153766009377187573 1055246733165563379111335)
                    ·
                      rfl

theorem cell23_6165257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_6165257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165257 prefixEnd_6165257 := by exact prefixLift 6165257
  have htrace : WordTrace (prefixWord ++ tailWord_6165257) baseStart_6165257 baseEnd_6165257 := by
    simpa [prefixWord, tailWord_6165257, baseEnd_6165257] using wordTrace_append hprefix tailTrace_6165257
  have hstable : (prefixWord ++ tailWord_6165257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165257).length < 2 ^ (prefixWord ++ tailWord_6165257).sum := by decide
  have hdescent : baseEnd_6165257 < baseStart_6165257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165297 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6165297 : Nat := 118140960795 + 6165297 * 2 ^ 59
def prefixEnd_6165297 : Nat := 4983230072969 + 3 ^ 40 * 6165297 * 2
def baseEnd_6165297 : Nat := 3165760738722869980833821

theorem tailTrace_6165297 : CollatzResearch.WordTrace tailWord_6165297 prefixEnd_6165297 3165760738722869980833821 := by
  unfold tailWord_6165297
  simp only [CollatzResearch.WordTrace]
  refine ⟨224866855145189392743166145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149911236763459595162110763 224866855145189392743166145)
  ·
    refine ⟨168650141358892044557374609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224866855145189392743166145 168650141358892044557374609)
    ·
      refine ⟨126487606019169033418030957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168650141358892044557374609 126487606019169033418030957)
      ·
        refine ⟨47432852257188387531761609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126487606019169033418030957 47432852257188387531761609)
        ·
          refine ⟨35574639192891290648821207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47432852257188387531761609 35574639192891290648821207)
          ·
            refine ⟨53361958789336935973231811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35574639192891290648821207 53361958789336935973231811)
            ·
              refine ⟨80042938184005403959847717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53361958789336935973231811 80042938184005403959847717)
              ·
                refine ⟨15008050909501013242471447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80042938184005403959847717 15008050909501013242471447)
                ·
                  refine ⟨22512076364251519863707171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15008050909501013242471447 22512076364251519863707171)
                  ·
                    refine ⟨33768114546377279795560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22512076364251519863707171 33768114546377279795560757)
                    ·
                      refine ⟨3165760738722869980833821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33768114546377279795560757 3165760738722869980833821)
                      ·
                        rfl

theorem cell23_6165297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6165297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165297 prefixEnd_6165297 := by exact prefixLift 6165297
  have htrace : WordTrace (prefixWord ++ tailWord_6165297) baseStart_6165297 baseEnd_6165297 := by
    simpa [prefixWord, tailWord_6165297, baseEnd_6165297] using wordTrace_append hprefix tailTrace_6165297
  have hstable : (prefixWord ++ tailWord_6165297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165297).length < 2 ^ (prefixWord ++ tailWord_6165297).sum := by decide
  have hdescent : baseEnd_6165297 < baseStart_6165297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165304 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_6165304 : Nat := 118140960795 + 6165304 * 2 ^ 59
def prefixEnd_6165304 : Nat := 4983230072969 + 3 ^ 40 * 6165304 * 2
def baseEnd_6165304 : Nat := 1055254777695817151148763

theorem tailTrace_6165304 : CollatzResearch.WordTrace tailWord_6165304 prefixEnd_6165304 1055254777695817151148763 := by
  unfold tailWord_6165304
  simp only [CollatzResearch.WordTrace]
  refine ⟨112433555228082016469335483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149911406970776021959113977 112433555228082016469335483)
  ·
    refine ⟨168650332842123024704003225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112433555228082016469335483 168650332842123024704003225)
    ·
      refine ⟨126487749631592268528002419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168650332842123024704003225 126487749631592268528002419)
      ·
        refine ⟨189731624447388402792003629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126487749631592268528002419 189731624447388402792003629)
        ·
          refine ⟨71149359167770651047001361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189731624447388402792003629 71149359167770651047001361)
          ·
            refine ⟨53362019375827988285251021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71149359167770651047001361 53362019375827988285251021)
            ·
              refine ⟨20010757265935495606969133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53362019375827988285251021 20010757265935495606969133)
              ·
                refine ⟨7504033974725810852613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20010757265935495606969133 7504033974725810852613425)
                ·
                  refine ⟨5628025481044358139460069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7504033974725810852613425 5628025481044358139460069)
                  ·
                    refine ⟨1055254777695817151148763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628025481044358139460069 1055254777695817151148763)
                    ·
                      rfl

theorem cell23_6165304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_6165304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165304 prefixEnd_6165304 := by exact prefixLift 6165304
  have htrace : WordTrace (prefixWord ++ tailWord_6165304) baseStart_6165304 baseEnd_6165304 := by
    simpa [prefixWord, tailWord_6165304, baseEnd_6165304] using wordTrace_append hprefix tailTrace_6165304
  have hstable : (prefixWord ++ tailWord_6165304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165304).length < 2 ^ (prefixWord ++ tailWord_6165304).sum := by decide
  have hdescent : baseEnd_6165304 < baseStart_6165304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165311 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 4]
def baseStart_6165311 : Nat := 118140960795 + 6165311 * 2 ^ 59
def prefixEnd_6165311 : Nat := 4983230072969 + 3 ^ 40 * 6165311 * 2
def baseEnd_6165311 : Nat := 3165767927452032926058757

theorem tailTrace_6165311 : CollatzResearch.WordTrace tailWord_6165311 prefixEnd_6165311 3165767927452032926058757 := by
  unfold tailWord_6165311
  simp only [CollatzResearch.WordTrace]
  refine ⟨224867365767138673134175787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149911577178092448756117191 224867365767138673134175787)
  ·
    refine ⟨337301048650708009701263681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224867365767138673134175787 337301048650708009701263681)
    ·
      refine ⟨252975786488031007275947761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337301048650708009701263681 252975786488031007275947761)
      ·
        refine ⟨189731839866023255456960821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252975786488031007275947761 189731839866023255456960821)
        ·
          refine ⟨17787359987439680199090077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189731839866023255456960821 17787359987439680199090077)
          ·
            refine ⟨6670259995289880074658779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17787359987439680199090077 6670259995289880074658779)
            ·
              refine ⟨10005389992934820111988169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670259995289880074658779 10005389992934820111988169)
              ·
                refine ⟨7504042494701115083991127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10005389992934820111988169 7504042494701115083991127)
                ·
                  refine ⟨11256063742051672625986691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504042494701115083991127 11256063742051672625986691)
                  ·
                    refine ⟨16884095613077508938980037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11256063742051672625986691 16884095613077508938980037)
                    ·
                      refine ⟨3165767927452032926058757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16884095613077508938980037 3165767927452032926058757)
                      ·
                        rfl

theorem cell23_6165311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_6165311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165311 prefixEnd_6165311 := by exact prefixLift 6165311
  have htrace : WordTrace (prefixWord ++ tailWord_6165311) baseStart_6165311 baseEnd_6165311 := by
    simpa [prefixWord, tailWord_6165311, baseEnd_6165311] using wordTrace_append hprefix tailTrace_6165311
  have hstable : (prefixWord ++ tailWord_6165311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165311).length < 2 ^ (prefixWord ++ tailWord_6165311).sum := by decide
  have hdescent : baseEnd_6165311 < baseStart_6165311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165324 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6165324 : Nat := 118140960795 + 6165324 * 2 ^ 59
def prefixEnd_6165324 : Nat := 4983230072969 + 3 ^ 40 * 6165324 * 2
def baseEnd_6165324 : Nat := 3165774602700541375196197

theorem tailTrace_6165324 : CollatzResearch.WordTrace tailWord_6165324 prefixEnd_6165324 3165774602700541375196197 := by
  unfold tailWord_6165324
  simp only [CollatzResearch.WordTrace]
  refine ⟨112433919958045788177199513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149911893277394384236266017 112433919958045788177199513)
  ·
    refine ⟨84325439968534341132899635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112433919958045788177199513 84325439968534341132899635)
    ·
      refine ⟨126488159952801511699349453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84325439968534341132899635 126488159952801511699349453)
      ·
        refine ⟨47433059982300566887256045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126488159952801511699349453 47433059982300566887256045)
        ·
          refine ⟨17787397493362712582721017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47433059982300566887256045 17787397493362712582721017)
          ·
            refine ⟨13340548120022034437040763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17787397493362712582721017 13340548120022034437040763)
            ·
              refine ⟨20010822180033051655561145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340548120022034437040763 20010822180033051655561145)
              ·
                refine ⟨15008116635024788741670859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20010822180033051655561145 15008116635024788741670859)
                ·
                  refine ⟨22512174952537183112506289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15008116635024788741670859 22512174952537183112506289)
                  ·
                    refine ⟨16884131214402887334379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22512174952537183112506289 16884131214402887334379717)
                    ·
                      refine ⟨3165774602700541375196197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16884131214402887334379717 3165774602700541375196197)
                      ·
                        rfl

theorem cell23_6165324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6165324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165324 prefixEnd_6165324 := by exact prefixLift 6165324
  have htrace : WordTrace (prefixWord ++ tailWord_6165324) baseStart_6165324 baseEnd_6165324 := by
    simpa [prefixWord, tailWord_6165324, baseEnd_6165324] using wordTrace_append hprefix tailTrace_6165324
  have hstable : (prefixWord ++ tailWord_6165324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165324).length < 2 ^ (prefixWord ++ tailWord_6165324).sum := by decide
  have hdescent : baseEnd_6165324 < baseStart_6165324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165347 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 7]
def baseStart_6165347 : Nat := 118140960795 + 6165347 * 2 ^ 59
def prefixEnd_6165347 : Nat := 4983230072969 + 3 ^ 40 * 6165347 * 2
def baseEnd_6165347 : Nat := 1055262137585198261736197

theorem tailTrace_6165347 : CollatzResearch.WordTrace tailWord_6165347 prefixEnd_6165347 1055262137585198261736197 := by
  unfold tailWord_6165347
  simp only [CollatzResearch.WordTrace]
  refine ⟨224868678795008251282486295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149912452530005500854990863 224868678795008251282486295)
  ·
    refine ⟨337303018192512376923729443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224868678795008251282486295 337303018192512376923729443)
    ·
      refine ⟨505954527288768565385594165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337303018192512376923729443 505954527288768565385594165)
      ·
        refine ⟨47433236933322053004899453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 505954527288768565385594165 47433236933322053004899453)
        ·
          refine ⟨17787463849995769876837295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47433236933322053004899453 17787463849995769876837295)
          ·
            refine ⟨26681195774993654815255943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17787463849995769876837295 26681195774993654815255943)
            ·
              refine ⟨40021793662490482222883915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26681195774993654815255943 40021793662490482222883915)
              ·
                refine ⟨60032690493735723334325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40021793662490482222883915 60032690493735723334325873)
                ·
                  refine ⟨45024517870301792500744405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60032690493735723334325873 45024517870301792500744405)
                  ·
                    refine ⟨1055262137585198261736197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45024517870301792500744405 1055262137585198261736197)
                    ·
                      rfl

theorem cell23_6165347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_6165347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165347 prefixEnd_6165347 := by exact prefixLift 6165347
  have htrace : WordTrace (prefixWord ++ tailWord_6165347) baseStart_6165347 baseEnd_6165347 := by
    simpa [prefixWord, tailWord_6165347, baseEnd_6165347] using wordTrace_append hprefix tailTrace_6165347
  have hstable : (prefixWord ++ tailWord_6165347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165347).length < 2 ^ (prefixWord ++ tailWord_6165347).sum := by decide
  have hdescent : baseEnd_6165347 < baseStart_6165347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165357 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6165357 : Nat := 118140960795 + 6165357 * 2 ^ 59
def prefixEnd_6165357 : Nat := 4983230072969 + 3 ^ 40 * 6165357 * 2
def baseEnd_6165357 : Nat := 3165791547562139746083545

theorem tailTrace_6165357 : CollatzResearch.WordTrace tailWord_6165357 prefixEnd_6165357 3165791547562139746083545 := by
  unfold tailWord_6165357
  simp only [CollatzResearch.WordTrace]
  refine ⟨224869043524972022990350325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149912695683314681993566883 224869043524972022990350325)
  ·
    refine ⟨21081472830466127155345343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224869043524972022990350325 21081472830466127155345343)
    ·
      refine ⟨31622209245699190733018015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21081472830466127155345343 31622209245699190733018015)
      ·
        refine ⟨47433313868548786099527023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31622209245699190733018015 47433313868548786099527023)
        ·
          refine ⟨71149970802823179149290535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47433313868548786099527023 71149970802823179149290535)
          ·
            refine ⟨106724956204234768723935803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71149970802823179149290535 106724956204234768723935803)
            ·
              refine ⟨160087434306352153085903705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106724956204234768723935803 160087434306352153085903705)
              ·
                refine ⟨120065575729764114814427779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160087434306352153085903705 120065575729764114814427779)
                ·
                  refine ⟨180098363594646172221641669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120065575729764114814427779 180098363594646172221641669)
                  ·
                    refine ⟨33768443173996157291557813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180098363594646172221641669 33768443173996157291557813)
                    ·
                      refine ⟨3165791547562139746083545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33768443173996157291557813 3165791547562139746083545)
                      ·
                        rfl

theorem cell23_6165357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6165357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165357 prefixEnd_6165357 := by exact prefixLift 6165357
  have htrace : WordTrace (prefixWord ++ tailWord_6165357) baseStart_6165357 baseEnd_6165357 := by
    simpa [prefixWord, tailWord_6165357, baseEnd_6165357] using wordTrace_append hprefix tailTrace_6165357
  have hstable : (prefixWord ++ tailWord_6165357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165357).length < 2 ^ (prefixWord ++ tailWord_6165357).sum := by decide
  have hdescent : baseEnd_6165357 < baseStart_6165357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165361 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_6165361 : Nat := 118140960795 + 6165361 * 2 ^ 59
def prefixEnd_6165361 : Nat := 4983230072969 + 3 ^ 40 * 6165361 * 2
def baseEnd_6165361 : Nat := 3165793601484757730433527

theorem tailTrace_6165361 : CollatzResearch.WordTrace tailWord_6165361 prefixEnd_6165361 3165793601484757730433527 := by
  unfold tailWord_6165361
  simp only [CollatzResearch.WordTrace]
  refine ⟨224869189416957531673495937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149912792944638354448997291 224869189416957531673495937)
  ·
    refine ⟨168651892062718148755121953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224869189416957531673495937 168651892062718148755121953)
    ·
      refine ⟨126488919047038611566341465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168651892062718148755121953 126488919047038611566341465)
      ·
        refine ⟨94866689285278958674756099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126488919047038611566341465 94866689285278958674756099)
        ·
          refine ⟨142300033927918438012134149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94866689285278958674756099 142300033927918438012134149)
          ·
            refine ⟨26681256361484707127275153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142300033927918438012134149 26681256361484707127275153)
            ·
              refine ⟨20010942271113530345456365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26681256361484707127275153 20010942271113530345456365)
              ·
                refine ⟨7504103351667573879546137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20010942271113530345456365 7504103351667573879546137)
                ·
                  refine ⟨5628077513750680409659603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7504103351667573879546137 5628077513750680409659603)
                  ·
                    refine ⟨8442116270626020614489405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628077513750680409659603 8442116270626020614489405)
                    ·
                      refine ⟨3165793601484757730433527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442116270626020614489405 3165793601484757730433527)
                      ·
                        rfl

theorem cell23_6165361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_6165361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165361 prefixEnd_6165361 := by exact prefixLift 6165361
  have htrace : WordTrace (prefixWord ++ tailWord_6165361) baseStart_6165361 baseEnd_6165361 := by
    simpa [prefixWord, tailWord_6165361, baseEnd_6165361] using wordTrace_append hprefix tailTrace_6165361
  have hstable : (prefixWord ++ tailWord_6165361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165361).length < 2 ^ (prefixWord ++ tailWord_6165361).sum := by decide
  have hdescent : baseEnd_6165361 < baseStart_6165361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165387 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5]
def baseStart_6165387 : Nat := 118140960795 + 6165387 * 2 ^ 59
def prefixEnd_6165387 : Nat := 4983230072969 + 3 ^ 40 * 6165387 * 2
def baseEnd_6165387 : Nat := 3165806951981774628708407

theorem tailTrace_6165387 : CollatzResearch.WordTrace tailWord_6165387 prefixEnd_6165387 3165806951981774628708407 := by
  unfold tailWord_6165387
  simp only [CollatzResearch.WordTrace]
  refine ⟨224870137714863338113942415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149913425143242225409294943 224870137714863338113942415)
  ·
    refine ⟨337305206572295007170913623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224870137714863338113942415 337305206572295007170913623)
    ·
      refine ⟨505957809858442510756370435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337305206572295007170913623 505957809858442510756370435)
      ·
        refine ⟨758936714787663766134555653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505957809858442510756370435 758936714787663766134555653)
        ·
          refine ⟨142300634022686956150229185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 758936714787663766134555653 142300634022686956150229185)
          ·
            refine ⟨106725475517015217112671889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142300634022686956150229185 106725475517015217112671889)
            ·
              refine ⟨80044106637761412834503917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106725475517015217112671889 80044106637761412834503917)
              ·
                refine ⟨30016539989160529812938969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80044106637761412834503917 30016539989160529812938969)
                ·
                  refine ⟨22512404991870397359704227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30016539989160529812938969 22512404991870397359704227)
                  ·
                    refine ⟨33768607487805596039556341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22512404991870397359704227 33768607487805596039556341)
                    ·
                      refine ⟨3165806951981774628708407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33768607487805596039556341 3165806951981774628708407)
                      ·
                        rfl

theorem cell23_6165387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 5].length) (baseStart_6165387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165387 prefixEnd_6165387 := by exact prefixLift 6165387
  have htrace : WordTrace (prefixWord ++ tailWord_6165387) baseStart_6165387 baseEnd_6165387 := by
    simpa [prefixWord, tailWord_6165387, baseEnd_6165387] using wordTrace_append hprefix tailTrace_6165387
  have hstable : (prefixWord ++ tailWord_6165387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165387).length < 2 ^ (prefixWord ++ tailWord_6165387).sum := by decide
  have hdescent : baseEnd_6165387 < baseStart_6165387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165388 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_6165388 : Nat := 118140960795 + 6165388 * 2 ^ 59
def prefixEnd_6165388 : Nat := 4983230072969 + 3 ^ 40 * 6165388 * 2
def baseEnd_6165388 : Nat := 3165807465462429124795903

theorem tailTrace_6165388 : CollatzResearch.WordTrace tailWord_6165388 prefixEnd_6165388 3165807465462429124795903 := by
  unfold tailWord_6165388
  simp only [CollatzResearch.WordTrace]
  refine ⟨112435087093929857642364409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149913449458573143523152545 112435087093929857642364409)
  ·
    refine ⟨84326315320447393231773307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112435087093929857642364409 84326315320447393231773307)
    ·
      refine ⟨126489472980671089847659961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84326315320447393231773307 126489472980671089847659961)
      ·
        refine ⟨94867104735503317385744971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126489472980671089847659961 94867104735503317385744971)
        ·
          refine ⟨142300657103254976078617457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94867104735503317385744971 142300657103254976078617457)
          ·
            refine ⟨106725492827441232058963093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142300657103254976078617457 106725492827441232058963093)
            ·
              refine ⟨5002757476286307752763895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106725492827441232058963093 5002757476286307752763895)
              ·
                refine ⟨7504136214429461629145843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5002757476286307752763895 7504136214429461629145843)
                ·
                  refine ⟨11256204321644192443718765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504136214429461629145843 11256204321644192443718765)
                  ·
                    refine ⟨4221076620616572166394537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11256204321644192443718765 4221076620616572166394537)
                    ·
                      refine ⟨3165807465462429124795903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221076620616572166394537 3165807465462429124795903)
                      ·
                        rfl

theorem cell23_6165388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_6165388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165388 prefixEnd_6165388 := by exact prefixLift 6165388
  have htrace : WordTrace (prefixWord ++ tailWord_6165388) baseStart_6165388 baseEnd_6165388 := by
    simpa [prefixWord, tailWord_6165388, baseEnd_6165388] using wordTrace_append hprefix tailTrace_6165388
  have hstable : (prefixWord ++ tailWord_6165388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165388).length < 2 ^ (prefixWord ++ tailWord_6165388).sum := by decide
  have hdescent : baseEnd_6165388 < baseStart_6165388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165454 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_6165454 : Nat := 118140960795 + 6165454 * 2 ^ 59
def prefixEnd_6165454 : Nat := 4983230072969 + 3 ^ 40 * 6165454 * 2
def baseEnd_6165454 : Nat := 1055280451728541955523533

theorem tailTrace_6165454 : CollatzResearch.WordTrace tailWord_6165454 prefixEnd_6165454 1055280451728541955523533 := by
  unfold tailWord_6165454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109072675702576069578927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149915054270413739037754277 28109072675702576069578927)
  ·
    refine ⟨42163609013553864104368391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109072675702576069578927 42163609013553864104368391)
    ·
      refine ⟨63245413520330796156552587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42163609013553864104368391 63245413520330796156552587)
      ·
        refine ⟨94868120280496194234828881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63245413520330796156552587 94868120280496194234828881)
        ·
          refine ⟨71151090210372145676121661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94868120280496194234828881 71151090210372145676121661)
          ·
            refine ⟨26681658828889554628545623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71151090210372145676121661 26681658828889554628545623)
            ·
              refine ⟨40022488243334331942818435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26681658828889554628545623 40022488243334331942818435)
              ·
                refine ⟨60033732365001497914227653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40022488243334331942818435 60033732365001497914227653)
                ·
                  refine ⟨11256324818437780858917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60033732365001497914227653 11256324818437780858917685)
                  ·
                    refine ⟨1055280451728541955523533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11256324818437780858917685 1055280451728541955523533)
                    ·
                      rfl

theorem cell23_6165454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_6165454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165454 prefixEnd_6165454 := by exact prefixLift 6165454
  have htrace : WordTrace (prefixWord ++ tailWord_6165454) baseStart_6165454 baseEnd_6165454 := by
    simpa [prefixWord, tailWord_6165454, baseEnd_6165454] using wordTrace_append hprefix tailTrace_6165454
  have hstable : (prefixWord ++ tailWord_6165454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165454).length < 2 ^ (prefixWord ++ tailWord_6165454).sum := by decide
  have hdescent : baseEnd_6165454 < baseStart_6165454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165464 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6165464 : Nat := 118140960795 + 6165464 * 2 ^ 59
def prefixEnd_6165464 : Nat := 4983230072969 + 3 ^ 40 * 6165464 * 2
def baseEnd_6165464 : Nat := 3165846489992170827445553

theorem tailTrace_6165464 : CollatzResearch.WordTrace tailWord_6165464 prefixEnd_6165464 3165846489992170827445553 := by
  unfold tailWord_6165464
  simp only [CollatzResearch.WordTrace]
  refine ⟨112436473067792190132247723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149915297423722920176330297 112436473067792190132247723)
  ·
    refine ⟨168654709601688285198371585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112436473067792190132247723 168654709601688285198371585)
    ·
      refine ⟨126491032201266213898778689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168654709601688285198371585 126491032201266213898778689)
      ·
        refine ⟨94868274150949660424084017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126491032201266213898778689 94868274150949660424084017)
        ·
          refine ⟨71151205613212245318063013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94868274150949660424084017 71151205613212245318063013)
          ·
            refine ⟨13340851052477295997136815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71151205613212245318063013 13340851052477295997136815)
            ·
              refine ⟨20011276578715943995705223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13340851052477295997136815 20011276578715943995705223)
              ·
                refine ⟨30016914868073915993557835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20011276578715943995705223 30016914868073915993557835)
                ·
                  refine ⟨45025372302110873990336753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30016914868073915993557835 45025372302110873990336753)
                  ·
                    refine ⟨33769029226583155492752565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45025372302110873990336753 33769029226583155492752565)
                    ·
                      refine ⟨3165846489992170827445553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33769029226583155492752565 3165846489992170827445553)
                      ·
                        rfl

theorem cell23_6165464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6165464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165464 prefixEnd_6165464 := by exact prefixLift 6165464
  have htrace : WordTrace (prefixWord ++ tailWord_6165464) baseStart_6165464 baseEnd_6165464 := by
    simpa [prefixWord, tailWord_6165464, baseEnd_6165464] using wordTrace_append hprefix tailTrace_6165464
  have hstable : (prefixWord ++ tailWord_6165464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165464).length < 2 ^ (prefixWord ++ tailWord_6165464).sum := by decide
  have hdescent : baseEnd_6165464 < baseStart_6165464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165511 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6165511 : Nat := 118140960795 + 6165511 * 2 ^ 59
def prefixEnd_6165511 : Nat := 4983230072969 + 3 ^ 40 * 6165511 * 2
def baseEnd_6165511 : Nat := 3165870623582932143557837

theorem tailTrace_6165511 : CollatzResearch.WordTrace tailWord_6165511 prefixEnd_6165511 3165870623582932143557837 := by
  unfold tailWord_6165511
  simp only [CollatzResearch.WordTrace]
  refine ⟨224874660366414107291456387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149916440244276071527637591 224874660366414107291456387)
  ·
    refine ⟨337311990549621160937184581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224874660366414107291456387 337311990549621160937184581)
    ·
      refine ⟨63245998228053967675722109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337311990549621160937184581 63245998228053967675722109)
      ·
        refine ⟨23717249335520237878395791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63245998228053967675722109 23717249335520237878395791)
        ·
          refine ⟨35575874003280356817593687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23717249335520237878395791 35575874003280356817593687)
          ·
            refine ⟨53363811004920535226390531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35575874003280356817593687 53363811004920535226390531)
            ·
              refine ⟨80045716507380802839585797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53363811004920535226390531 80045716507380802839585797)
              ·
                refine ⟨15008571845133900532422337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80045716507380802839585797 15008571845133900532422337)
                ·
                  refine ⟨11256428883850425399316753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15008571845133900532422337 11256428883850425399316753)
                  ·
                    refine ⟨8442321662887819049487565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11256428883850425399316753 8442321662887819049487565)
                    ·
                      refine ⟨3165870623582932143557837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442321662887819049487565 3165870623582932143557837)
                      ·
                        rfl

theorem cell23_6165511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6165511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165511 prefixEnd_6165511 := by exact prefixLift 6165511
  have htrace : WordTrace (prefixWord ++ tailWord_6165511) baseStart_6165511 baseEnd_6165511 := by
    simpa [prefixWord, tailWord_6165511, baseEnd_6165511] using wordTrace_append hprefix tailTrace_6165511
  have hstable : (prefixWord ++ tailWord_6165511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165511).length < 2 ^ (prefixWord ++ tailWord_6165511).sum := by decide
  have hdescent : baseEnd_6165511 < baseStart_6165511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165575 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_6165575 : Nat := 118140960795 + 6165575 * 2 ^ 59
def prefixEnd_6165575 : Nat := 4983230072969 + 3 ^ 40 * 6165575 * 2
def baseEnd_6165575 : Nat := 3165903486344819893157543

theorem tailTrace_6165575 : CollatzResearch.WordTrace tailWord_6165575 prefixEnd_6165575 3165903486344819893157543 := by
  unfold tailWord_6165575
  simp only [CollatzResearch.WordTrace]
  refine ⟨224876994638182246221786179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149917996425454830814524119 224876994638182246221786179)
  ·
    refine ⟨337315491957273369332679269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224876994638182246221786179 337315491957273369332679269)
    ·
      refine ⟨63246654741988756749877363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337315491957273369332679269 63246654741988756749877363)
      ·
        refine ⟨94869982112983135124816045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63246654741988756749877363 94869982112983135124816045)
        ·
          refine ⟨35576243292368675671806017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94869982112983135124816045 35576243292368675671806017)
          ·
            refine ⟨26682182469276506753854513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35576243292368675671806017 26682182469276506753854513)
            ·
              refine ⟨20011636851957380065390885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26682182469276506753854513 20011636851957380065390885)
              ·
                refine ⟨3752181909742008762260791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20011636851957380065390885 3752181909742008762260791)
                ·
                  refine ⟨5628272864613013143391187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752181909742008762260791 5628272864613013143391187)
                  ·
                    refine ⟨8442409296919519715086781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628272864613013143391187 8442409296919519715086781)
                    ·
                      refine ⟨3165903486344819893157543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442409296919519715086781 3165903486344819893157543)
                      ·
                        rfl

theorem cell23_6165575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_6165575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165575 prefixEnd_6165575 := by exact prefixLift 6165575
  have htrace : WordTrace (prefixWord ++ tailWord_6165575) baseStart_6165575 baseEnd_6165575 := by
    simpa [prefixWord, tailWord_6165575, baseEnd_6165575] using wordTrace_append hprefix tailTrace_6165575
  have hstable : (prefixWord ++ tailWord_6165575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165575).length < 2 ^ (prefixWord ++ tailWord_6165575).sum := by decide
  have hdescent : baseEnd_6165575 < baseStart_6165575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165601 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_6165601 : Nat := 118140960795 + 6165601 * 2 ^ 59
def prefixEnd_6165601 : Nat := 4983230072969 + 3 ^ 40 * 6165601 * 2
def baseEnd_6165601 : Nat := 3165916836841836791432423

theorem tailTrace_6165601 : CollatzResearch.WordTrace tailWord_6165601 prefixEnd_6165601 3165916836841836791432423 := by
  unfold tailWord_6165601
  simp only [CollatzResearch.WordTrace]
  refine ⟨224877942936088052662232657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149918628624058701774821771 224877942936088052662232657)
  ·
    refine ⟨168658457202066039496674493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224877942936088052662232657 168658457202066039496674493)
    ·
      refine ⟨63246921450774764811252935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168658457202066039496674493 63246921450774764811252935)
      ·
        refine ⟨94870382176162147216879403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63246921450774764811252935 94870382176162147216879403)
        ·
          refine ⟨142305573264243220825319105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94870382176162147216879403 142305573264243220825319105)
          ·
            refine ⟨106729179948182415618989329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142305573264243220825319105 106729179948182415618989329)
            ·
              refine ⟨80046884961136811714241997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106729179948182415618989329 80046884961136811714241997)
              ·
                refine ⟨30017581860426304392840749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80046884961136811714241997 30017581860426304392840749)
                ·
                  refine ⟨11256593197659864147315281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30017581860426304392840749 11256593197659864147315281)
                  ·
                    refine ⟨8442444898244898110486461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11256593197659864147315281 8442444898244898110486461)
                    ·
                      refine ⟨3165916836841836791432423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442444898244898110486461 3165916836841836791432423)
                      ·
                        rfl

theorem cell23_6165601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_6165601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165601 prefixEnd_6165601 := by exact prefixLift 6165601
  have htrace : WordTrace (prefixWord ++ tailWord_6165601) baseStart_6165601 baseEnd_6165601 := by
    simpa [prefixWord, tailWord_6165601, baseEnd_6165601] using wordTrace_append hprefix tailTrace_6165601
  have hstable : (prefixWord ++ tailWord_6165601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165601).length < 2 ^ (prefixWord ++ tailWord_6165601).sum := by decide
  have hdescent : baseEnd_6165601 < baseStart_6165601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165618 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6165618 : Nat := 118140960795 + 6165618 * 2 ^ 59
def prefixEnd_6165618 : Nat := 4983230072969 + 3 ^ 40 * 6165618 * 2
def baseEnd_6165618 : Nat := 3165925566012963224919845

theorem tailTrace_6165618 : CollatzResearch.WordTrace tailWord_6165618 prefixEnd_6165618 3165925566012963224919845 := by
  unfold tailWord_6165618
  simp only [CollatzResearch.WordTrace]
  refine ⟨56219640744256616141400377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149919041984684309710401005 56219640744256616141400377)
  ·
    refine ⟨42164730558192462106050283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56219640744256616141400377 42164730558192462106050283)
    ·
      refine ⟨63247095837288693159075425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42164730558192462106050283 63247095837288693159075425)
      ·
        refine ⟨47435321877966519869306569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63247095837288693159075425 47435321877966519869306569)
        ·
          refine ⟨35576491408474889901979927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47435321877966519869306569 35576491408474889901979927)
          ·
            refine ⟨53364737112712334852969891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35576491408474889901979927 53364737112712334852969891)
            ·
              refine ⟨80047105669068502279454837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53364737112712334852969891 80047105669068502279454837)
              ·
                refine ⟨7504416156475172088698891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80047105669068502279454837 7504416156475172088698891)
                ·
                  refine ⟨11256624234712758133048337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504416156475172088698891 11256624234712758133048337)
                  ·
                    refine ⟨8442468176034568599786253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11256624234712758133048337 8442468176034568599786253)
                    ·
                      refine ⟨3165925566012963224919845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442468176034568599786253 3165925566012963224919845)
                      ·
                        rfl

theorem cell23_6165618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6165618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165618 prefixEnd_6165618 := by exact prefixLift 6165618
  have htrace : WordTrace (prefixWord ++ tailWord_6165618) baseStart_6165618 baseEnd_6165618 := by
    simpa [prefixWord, tailWord_6165618, baseEnd_6165618] using wordTrace_append hprefix tailTrace_6165618
  have hstable : (prefixWord ++ tailWord_6165618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165618).length < 2 ^ (prefixWord ++ tailWord_6165618).sum := by decide
  have hdescent : baseEnd_6165618 < baseStart_6165618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165721 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_6165721 : Nat := 118140960795 + 6165721 * 2 ^ 59
def prefixEnd_6165721 : Nat := 4983230072969 + 3 ^ 40 * 6165721 * 2
def baseEnd_6165721 : Nat := 3165978454520376321931871

theorem tailTrace_6165721 : CollatzResearch.WordTrace tailWord_6165721 prefixEnd_6165721 3165978454520376321931871 := by
  unfold tailWord_6165721
  simp only [CollatzResearch.WordTrace]
  refine ⟨224882319695653313156601017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149921546463768875437734011 224882319695653313156601017)
  ·
    refine ⟨168661739771739984867450763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224882319695653313156601017 168661739771739984867450763)
    ·
      refine ⟨252992609657609977301176145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168661739771739984867450763 252992609657609977301176145)
      ·
        refine ⟨189744457243207482975882109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252992609657609977301176145 189744457243207482975882109)
        ·
          refine ⟨71154171466202806115955791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189744457243207482975882109 71154171466202806115955791)
          ·
            refine ⟨106731257199304209173933687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71154171466202806115955791 106731257199304209173933687)
            ·
              refine ⟨160096885798956313760900531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106731257199304209173933687 160096885798956313760900531)
              ·
                refine ⟨240145328698434470641350797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160096885798956313760900531 240145328698434470641350797)
                ·
                  refine ⟨90054498261912926490506549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240145328698434470641350797 90054498261912926490506549)
                  ·
                    refine ⟨8442609212054336858484989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90054498261912926490506549 8442609212054336858484989)
                    ·
                      refine ⟨3165978454520376321931871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442609212054336858484989 3165978454520376321931871)
                      ·
                        rfl

theorem cell23_6165721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_6165721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165721 prefixEnd_6165721 := by exact prefixLift 6165721
  have htrace : WordTrace (prefixWord ++ tailWord_6165721) baseStart_6165721 baseEnd_6165721 := by
    simpa [prefixWord, tailWord_6165721, baseEnd_6165721] using wordTrace_append hprefix tailTrace_6165721
  have hstable : (prefixWord ++ tailWord_6165721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165721).length < 2 ^ (prefixWord ++ tailWord_6165721).sum := by decide
  have hdescent : baseEnd_6165721 < baseStart_6165721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165728 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 5]
def baseStart_6165728 : Nat := 118140960795 + 6165728 * 2 ^ 59
def prefixEnd_6165728 : Nat := 4983230072969 + 3 ^ 40 * 6165728 * 2
def baseEnd_6165728 : Nat := 351775783209439754949371

theorem tailTrace_6165728 : CollatzResearch.WordTrace tailWord_6165728 prefixEnd_6165728 351775783209439754949371 := by
  unfold tailWord_6165728
  simp only [CollatzResearch.WordTrace]
  refine ⟨112441287503313976676052919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149921716671085302234737225 112441287503313976676052919)
  ·
    refine ⟨168661931254970965014079379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112441287503313976676052919 168661931254970965014079379)
    ·
      refine ⟨252992896882456447521119069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168661931254970965014079379 252992896882456447521119069)
      ·
        refine ⟨94872336330921167820419651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252992896882456447521119069 94872336330921167820419651)
        ·
          refine ⟨142308504496381751730629477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94872336330921167820419651 142308504496381751730629477)
          ·
            refine ⟨26682844593071578449493027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142308504496381751730629477 26682844593071578449493027)
            ·
              refine ⟨40024266889607367674239541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26682844593071578449493027 40024266889607367674239541)
              ·
                refine ⟨3752275020900690719459957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40024266889607367674239541 3752275020900690719459957)
                ·
                  refine ⟨351775783209439754949371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752275020900690719459957 351775783209439754949371)
                  ·
                    rfl

theorem cell23_6165728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 5].length) (baseStart_6165728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165728 prefixEnd_6165728 := by exact prefixLift 6165728
  have htrace : WordTrace (prefixWord ++ tailWord_6165728) baseStart_6165728 baseEnd_6165728 := by
    simpa [prefixWord, tailWord_6165728, baseEnd_6165728] using wordTrace_append hprefix tailTrace_6165728
  have hstable : (prefixWord ++ tailWord_6165728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165728).length < 2 ^ (prefixWord ++ tailWord_6165728).sum := by decide
  have hdescent : baseEnd_6165728 < baseStart_6165728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165738 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_6165738 : Nat := 118140960795 + 6165738 * 2 ^ 59
def prefixEnd_6165738 : Nat := 4983230072969 + 3 ^ 40 * 6165738 * 2
def baseEnd_6165738 : Nat := 3165987183691502755419293

theorem tailTrace_6165738 : CollatzResearch.WordTrace tailWord_6165738 prefixEnd_6165738 3165987183691502755419293 := by
  unfold tailWord_6165738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56220734934147931264992467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149921959824394483373313245 56220734934147931264992467)
  ·
    refine ⟨84331102401221896897488701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56220734934147931264992467 84331102401221896897488701)
    ·
      refine ⟨31624163400458211336558263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84331102401221896897488701 31624163400458211336558263)
      ·
        refine ⟨47436245100687317004837395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31624163400458211336558263 47436245100687317004837395)
        ·
          refine ⟨71154367651030975507256093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47436245100687317004837395 71154367651030975507256093)
          ·
            refine ⟨26682887869136615815221035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71154367651030975507256093 26682887869136615815221035)
            ·
              refine ⟨40024331803704923722831553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26682887869136615815221035 40024331803704923722831553)
              ·
                refine ⟨30018248852778692792123665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40024331803704923722831553 30018248852778692792123665)
                ·
                  refine ⟨22513686639584019594092749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30018248852778692792123665 22513686639584019594092749)
                  ·
                    refine ⟨8442632489844007347784781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22513686639584019594092749 8442632489844007347784781)
                    ·
                      refine ⟨3165987183691502755419293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442632489844007347784781 3165987183691502755419293)
                      ·
                        rfl

theorem cell23_6165738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_6165738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165738 prefixEnd_6165738 := by exact prefixLift 6165738
  have htrace : WordTrace (prefixWord ++ tailWord_6165738) baseStart_6165738 baseEnd_6165738 := by
    simpa [prefixWord, tailWord_6165738, baseEnd_6165738] using wordTrace_append hprefix tailTrace_6165738
  have hstable : (prefixWord ++ tailWord_6165738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165738).length < 2 ^ (prefixWord ++ tailWord_6165738).sum := by decide
  have hdescent : baseEnd_6165738 < baseStart_6165738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165758 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6165758 : Nat := 118140960795 + 6165758 * 2 ^ 59
def prefixEnd_6165758 : Nat := 4983230072969 + 3 ^ 40 * 6165758 * 2
def baseEnd_6165758 : Nat := 1055332484434864225723067

theorem tailTrace_6165758 : CollatzResearch.WordTrace tailWord_6165758 prefixEnd_6165758 1055332484434864225723067 := by
  unfold tailWord_6165758
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110458649564908559462241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149922446131012845650465285 28110458649564908559462241)
  ·
    refine ⟨21082843987173681419596681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28110458649564908559462241 21082843987173681419596681)
    ·
      refine ⟨15812132990380261064697511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21082843987173681419596681 15812132990380261064697511)
      ·
        refine ⟨23718199485570391597046267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15812132990380261064697511 23718199485570391597046267)
        ·
          refine ⟨35577299228355587395569401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23718199485570391597046267 35577299228355587395569401)
          ·
            refine ⟨26682974421266690546677051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35577299228355587395569401 26682974421266690546677051)
            ·
              refine ⟨40024461631900035820015577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26682974421266690546677051 40024461631900035820015577)
              ·
                refine ⟨30018346223925026865011683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40024461631900035820015577 30018346223925026865011683)
                ·
                  refine ⟨45027519335887540297517525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30018346223925026865011683 45027519335887540297517525)
                  ·
                    refine ⟨1055332484434864225723067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45027519335887540297517525 1055332484434864225723067)
                    ·
                      rfl

theorem cell23_6165758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6165758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165758 prefixEnd_6165758 := by exact prefixLift 6165758
  have htrace : WordTrace (prefixWord ++ tailWord_6165758) baseStart_6165758 baseEnd_6165758 := by
    simpa [prefixWord, tailWord_6165758, baseEnd_6165758] using wordTrace_append hprefix tailTrace_6165758
  have hstable : (prefixWord ++ tailWord_6165758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165758).length < 2 ^ (prefixWord ++ tailWord_6165758).sum := by decide
  have hdescent : baseEnd_6165758 < baseStart_6165758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165781 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6165781 : Nat := 118140960795 + 6165781 * 2 ^ 59
def prefixEnd_6165781 : Nat := 4983230072969 + 3 ^ 40 * 6165781 * 2
def baseEnd_6165781 : Nat := 3166009263359646087181595

theorem tailTrace_6165781 : CollatzResearch.WordTrace tailWord_6165781 prefixEnd_6165781 3166009263359646087181595 := by
  unfold tailWord_6165781
  simp only [CollatzResearch.WordTrace]
  refine ⟨224884508075435943403785197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149923005383623962269190131 224884508075435943403785197)
  ·
    refine ⟨84331690528288478776419449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224884508075435943403785197 84331690528288478776419449)
    ·
      refine ⟨63248767896216359082314587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84331690528288478776419449 63248767896216359082314587)
      ·
        refine ⟨94873151844324538623471881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63248767896216359082314587 94873151844324538623471881)
        ·
          refine ⟨71154863883243403967603911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94873151844324538623471881 71154863883243403967603911)
          ·
            refine ⟨106732295824865105951405867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71154863883243403967603911 106732295824865105951405867)
            ·
              refine ⟨160098443737297658927108801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106732295824865105951405867 160098443737297658927108801)
              ·
                refine ⟨120073832802973244195331601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160098443737297658927108801 120073832802973244195331601)
                ·
                  refine ⟨90055374602229933146498701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120073832802973244195331601 90055374602229933146498701)
                  ·
                    refine ⟨33770765475836224929937013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90055374602229933146498701 33770765475836224929937013)
                    ·
                      refine ⟨3166009263359646087181595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33770765475836224929937013 3166009263359646087181595)
                      ·
                        rfl

theorem cell23_6165781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6165781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165781 prefixEnd_6165781 := by exact prefixLift 6165781
  have htrace : WordTrace (prefixWord ++ tailWord_6165781) baseStart_6165781 baseEnd_6165781 := by
    simpa [prefixWord, tailWord_6165781, baseEnd_6165781] using wordTrace_append hprefix tailTrace_6165781
  have hstable : (prefixWord ++ tailWord_6165781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165781).length < 2 ^ (prefixWord ++ tailWord_6165781).sum := by decide
  have hdescent : baseEnd_6165781 < baseStart_6165781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165788 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_6165788 : Nat := 118140960795 + 6165788 * 2 ^ 59
def prefixEnd_6165788 : Nat := 4983230072969 + 3 ^ 40 * 6165788 * 2
def baseEnd_6165788 : Nat := 1055337619241409186598021

theorem tailTrace_6165788 : CollatzResearch.WordTrace tailWord_6165788 prefixEnd_6165788 1055337619241409186598021 := by
  unfold tailWord_6165788
  simp only [CollatzResearch.WordTrace]
  refine ⟨112442381693205291799645009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149923175590940389066193345 112442381693205291799645009)
  ·
    refine ⟨84331786269903968849733757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112442381693205291799645009 84331786269903968849733757)
    ·
      refine ⟨31624419851213988318650159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84331786269903968849733757 31624419851213988318650159)
      ·
        refine ⟨47436629776820982477975239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31624419851213988318650159 47436629776820982477975239)
        ·
          refine ⟨71154944665231473716962859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47436629776820982477975239 71154944665231473716962859)
          ·
            refine ⟨106732416997847210575444289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71154944665231473716962859 106732416997847210575444289)
            ·
              refine ⟨80049312748385407931583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106732416997847210575444289 80049312748385407931583217)
              ·
                refine ⟨60036984561289055948687413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80049312748385407931583217 60036984561289055948687413)
                ·
                  refine ⟨5628467302620848995189445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60036984561289055948687413 5628467302620848995189445)
                  ·
                    refine ⟨1055337619241409186598021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628467302620848995189445 1055337619241409186598021)
                    ·
                      rfl

theorem cell23_6165788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_6165788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165788 prefixEnd_6165788 := by exact prefixLift 6165788
  have htrace : WordTrace (prefixWord ++ tailWord_6165788) baseStart_6165788 baseEnd_6165788 := by
    simpa [prefixWord, tailWord_6165788, baseEnd_6165788] using wordTrace_append hprefix tailTrace_6165788
  have hstable : (prefixWord ++ tailWord_6165788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165788).length < 2 ^ (prefixWord ++ tailWord_6165788).sum := by decide
  have hdescent : baseEnd_6165788 < baseStart_6165788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165818 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_6165818 : Nat := 118140960795 + 6165818 * 2 ^ 59
def prefixEnd_6165818 : Nat := 4983230072969 + 3 ^ 40 * 6165818 * 2
def baseEnd_6165818 : Nat := 351780918015984715824325

theorem tailTrace_6165818 : CollatzResearch.WordTrace tailWord_6165818 prefixEnd_6165818 351780918015984715824325 := by
  unfold tailWord_6165818
  simp only [CollatzResearch.WordTrace]
  refine ⟨56221464394075474680720527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149923905050867932481921405 56221464394075474680720527)
  ·
    refine ⟨84332196591113212021080791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56221464394075474680720527 84332196591113212021080791)
    ·
      refine ⟨126498294886669818031621187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84332196591113212021080791 126498294886669818031621187)
      ·
        refine ⟨189747442330004727047431781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126498294886669818031621187 189747442330004727047431781)
        ·
          refine ⟨35577645436875886321393459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189747442330004727047431781 35577645436875886321393459)
          ·
            refine ⟨53366468155313829482090189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35577645436875886321393459 53366468155313829482090189)
            ·
              refine ⟨20012425558242686055783821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53366468155313829482090189 20012425558242686055783821)
              ·
                refine ⟨7504659584341007270918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20012425558242686055783821 7504659584341007270918933)
                ·
                  refine ⟨351780918015984715824325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7504659584341007270918933 351780918015984715824325)
                  ·
                    rfl

theorem cell23_6165818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_6165818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165818 prefixEnd_6165818 := by exact prefixLift 6165818
  have htrace : WordTrace (prefixWord ++ tailWord_6165818) baseStart_6165818 baseEnd_6165818 := by
    simpa [prefixWord, tailWord_6165818, baseEnd_6165818] using wordTrace_append hprefix tailTrace_6165818
  have hstable : (prefixWord ++ tailWord_6165818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165818).length < 2 ^ (prefixWord ++ tailWord_6165818).sum := by decide
  have hdescent : baseEnd_6165818 < baseStart_6165818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165885 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_6165885 : Nat := 118140960795 + 6165885 * 2 ^ 59
def prefixEnd_6165885 : Nat := 4983230072969 + 3 ^ 40 * 6165885 * 2
def baseEnd_6165885 : Nat := 3166062665347713680281117

theorem tailTrace_6165885 : CollatzResearch.WordTrace tailWord_6165885 prefixEnd_6165885 3166062665347713680281117 := by
  unfold tailWord_6165885
  simp only [CollatzResearch.WordTrace]
  refine ⟨224888301267059169165571109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149925534178039446110380739 224888301267059169165571109)
  ·
    refine ⟨42166556487573594218544583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224888301267059169165571109 42166556487573594218544583)
    ·
      refine ⟨63249834731360391327816875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42166556487573594218544583 63249834731360391327816875)
      ·
        refine ⟨94874752097040586991725313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63249834731360391327816875 94874752097040586991725313)
        ·
          refine ⟨71156064072780440243793985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94874752097040586991725313 71156064072780440243793985)
          ·
            refine ⟨53367048054585330182845489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71156064072780440243793985 53367048054585330182845489)
            ·
              refine ⟨40025286040938997637134117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53367048054585330182845489 40025286040938997637134117)
              ·
                refine ⟨7504741132676062056962647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40025286040938997637134117 7504741132676062056962647)
                ·
                  refine ⟨11257111699014093085443971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504741132676062056962647 11257111699014093085443971)
                  ·
                    refine ⟨16885667548521139628165957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11257111699014093085443971 16885667548521139628165957)
                    ·
                      refine ⟨3166062665347713680281117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16885667548521139628165957 3166062665347713680281117)
                      ·
                        rfl

theorem cell23_6165885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_6165885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165885 prefixEnd_6165885 := by exact prefixLift 6165885
  have htrace : WordTrace (prefixWord ++ tailWord_6165885) baseStart_6165885 baseEnd_6165885 := by
    simpa [prefixWord, tailWord_6165885, baseEnd_6165885] using wordTrace_append hprefix tailTrace_6165885
  have hstable : (prefixWord ++ tailWord_6165885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165885).length < 2 ^ (prefixWord ++ tailWord_6165885).sum := by decide
  have hdescent : baseEnd_6165885 < baseStart_6165885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165905 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_6165905 : Nat := 118140960795 + 6165905 * 2 ^ 59
def prefixEnd_6165905 : Nat := 4983230072969 + 3 ^ 40 * 6165905 * 2
def baseEnd_6165905 : Nat := 3166072934960803602031025

theorem tailTrace_6165905 : CollatzResearch.WordTrace tailWord_6165905 prefixEnd_6165905 3166072934960803602031025 := by
  unfold tailWord_6165905
  simp only [CollatzResearch.WordTrace]
  refine ⟨224889030726986712581299169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149926020484657808387532779 224889030726986712581299169)
  ·
    refine ⟨168666773045240034435974377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224889030726986712581299169 168666773045240034435974377)
    ·
      refine ⟨126500079783930025826980783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168666773045240034435974377 126500079783930025826980783)
      ·
        refine ⟨189750119675895038740471175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126500079783930025826980783 189750119675895038740471175)
        ·
          refine ⟨284625179513842558110706763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189750119675895038740471175 284625179513842558110706763)
          ·
            refine ⟨426937769270763837166060145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284625179513842558110706763 426937769270763837166060145)
            ·
              refine ⟨320203326953072877874545109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426937769270763837166060145 320203326953072877874545109)
              ·
                refine ⟨7504765475462645575184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 320203326953072877874545109 7504765475462645575184651)
                ·
                  refine ⟨11257148213193968362776977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7504765475462645575184651 11257148213193968362776977)
                  ·
                    refine ⟨8442861159895476272082733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11257148213193968362776977 8442861159895476272082733)
                    ·
                      refine ⟨3166072934960803602031025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8442861159895476272082733 3166072934960803602031025)
                      ·
                        rfl

theorem cell23_6165905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_6165905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165905 prefixEnd_6165905 := by exact prefixLift 6165905
  have htrace : WordTrace (prefixWord ++ tailWord_6165905) baseStart_6165905 baseEnd_6165905 := by
    simpa [prefixWord, tailWord_6165905, baseEnd_6165905] using wordTrace_append hprefix tailTrace_6165905
  have hstable : (prefixWord ++ tailWord_6165905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165905).length < 2 ^ (prefixWord ++ tailWord_6165905).sum := by decide
  have hdescent : baseEnd_6165905 < baseStart_6165905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165912 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_6165912 : Nat := 118140960795 + 6165912 * 2 ^ 59
def prefixEnd_6165912 : Nat := 4983230072969 + 3 ^ 40 * 6165912 * 2
def baseEnd_6165912 : Nat := 1055358843108461691547831

theorem tailTrace_6165912 : CollatzResearch.WordTrace tailWord_6165912 prefixEnd_6165912 1055358843108461691547831 := by
  unfold tailWord_6165912
  simp only [CollatzResearch.WordTrace]
  refine ⟨112444643018980676388401995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149926190691974235184535993 112444643018980676388401995)
  ·
    refine ⟨168666964528471014582602993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112444643018980676388401995 168666964528471014582602993)
    ·
      refine ⟨126500223396353260936952245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168666964528471014582602993 126500223396353260936952245)
      ·
        refine ⟨11859395943408118212839273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126500223396353260936952245 11859395943408118212839273)
        ·
          refine ⟨8894546957556088659629455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11859395943408118212839273 8894546957556088659629455)
          ·
            refine ⟨13341820436334132989444183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8894546957556088659629455 13341820436334132989444183)
            ·
              refine ⟨20012730654501199484166275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13341820436334132989444183 20012730654501199484166275)
              ·
                refine ⟨30019095981751799226249413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20012730654501199484166275 30019095981751799226249413)
                ·
                  refine ⟨5628580496578462354921765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30019095981751799226249413 5628580496578462354921765)
                  ·
                    refine ⟨1055358843108461691547831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628580496578462354921765 1055358843108461691547831)
                    ·
                      rfl

theorem cell23_6165912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_6165912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165912 prefixEnd_6165912 := by exact prefixLift 6165912
  have htrace : WordTrace (prefixWord ++ tailWord_6165912) baseStart_6165912 baseEnd_6165912 := by
    simpa [prefixWord, tailWord_6165912, baseEnd_6165912] using wordTrace_append hprefix tailTrace_6165912
  have hstable : (prefixWord ++ tailWord_6165912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165912).length < 2 ^ (prefixWord ++ tailWord_6165912).sum := by decide
  have hdescent : baseEnd_6165912 < baseStart_6165912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165919 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6165919 : Nat := 118140960795 + 6165919 * 2 ^ 59
def prefixEnd_6165919 : Nat := 4983230072969 + 3 ^ 40 * 6165919 * 2
def baseEnd_6165919 : Nat := 3166080123689966547255961

theorem tailTrace_6165919 : CollatzResearch.WordTrace tailWord_6165919 prefixEnd_6165919 3166080123689966547255961 := by
  unfold tailWord_6165919
  simp only [CollatzResearch.WordTrace]
  refine ⟨224889541348935992972308811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149926360899290661981539207 224889541348935992972308811)
  ·
    refine ⟨337334312023403989458463217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224889541348935992972308811 337334312023403989458463217)
    ·
      refine ⟨253000734017552992093847413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337334312023403989458463217 253000734017552992093847413)
      ·
        refine ⟨23718818814145593008798195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253000734017552992093847413 23718818814145593008798195)
        ·
          refine ⟨35578228221218389513197293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23718818814145593008798195 35578228221218389513197293)
          ·
            refine ⟨13341835582956896067448985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35578228221218389513197293 13341835582956896067448985)
            ·
              refine ⟨10006376687217672050586739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13341835582956896067448985 10006376687217672050586739)
              ·
                refine ⟨15009565030826508075880109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006376687217672050586739 15009565030826508075880109)
                ·
                  refine ⟨5628586886559940528455041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15009565030826508075880109 5628586886559940528455041)
                  ·
                    refine ⟨4221440164919955396341281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628586886559940528455041 4221440164919955396341281)
                    ·
                      refine ⟨3166080123689966547255961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221440164919955396341281 3166080123689966547255961)
                      ·
                        rfl

theorem cell23_6165919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6165919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165919 prefixEnd_6165919 := by exact prefixLift 6165919
  have htrace : WordTrace (prefixWord ++ tailWord_6165919) baseStart_6165919 baseEnd_6165919 := by
    simpa [prefixWord, tailWord_6165919, baseEnd_6165919] using wordTrace_append hprefix tailTrace_6165919
  have hstable : (prefixWord ++ tailWord_6165919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165919).length < 2 ^ (prefixWord ++ tailWord_6165919).sum := by decide
  have hdescent : baseEnd_6165919 < baseStart_6165919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165988 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_6165988 : Nat := 118140960795 + 6165988 * 2 ^ 59
def prefixEnd_6165988 : Nat := 4983230072969 + 3 ^ 40 * 6165988 * 2
def baseEnd_6165988 : Nat := 3166115553855126777293143

theorem tailTrace_6165988 : CollatzResearch.WordTrace tailWord_6165988 prefixEnd_6165988 3166115553855126777293143 := by
  unfold tailWord_6165988
  simp only [CollatzResearch.WordTrace]
  refine ⟨112446028992843008878285309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149928038657124011837713745 112446028992843008878285309)
  ·
    refine ⟨42167260872316128329356991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112446028992843008878285309 42167260872316128329356991)
    ·
      refine ⟨63250891308474192494035487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42167260872316128329356991 63250891308474192494035487)
      ·
        refine ⟨94876336962711288741053231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63250891308474192494035487 94876336962711288741053231)
        ·
          refine ⟨142314505444066933111579847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94876336962711288741053231 142314505444066933111579847)
          ·
            refine ⟨213471758166100399667369771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142314505444066933111579847 213471758166100399667369771)
            ·
              refine ⟨320207637249150599501054657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213471758166100399667369771 320207637249150599501054657)
              ·
                refine ⟨240155727936862949625790993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320207637249150599501054657 240155727936862949625790993)
                ·
                  refine ⟨180116795952647212219343245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240155727936862949625790993 180116795952647212219343245)
                  ·
                    refine ⟨67543798482242704582253717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180116795952647212219343245 67543798482242704582253717)
                    ·
                      refine ⟨3166115553855126777293143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67543798482242704582253717 3166115553855126777293143)
                      ·
                        rfl

theorem cell23_6165988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_6165988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165988 prefixEnd_6165988 := by exact prefixLift 6165988
  have htrace : WordTrace (prefixWord ++ tailWord_6165988) baseStart_6165988 baseEnd_6165988 := by
    simpa [prefixWord, tailWord_6165988, baseEnd_6165988] using wordTrace_append hprefix tailTrace_6165988
  have hstable : (prefixWord ++ tailWord_6165988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165988).length < 2 ^ (prefixWord ++ tailWord_6165988).sum := by decide
  have hdescent : baseEnd_6165988 < baseStart_6165988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6165992 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6165992 : Nat := 118140960795 + 6165992 * 2 ^ 59
def prefixEnd_6165992 : Nat := 4983230072969 + 3 ^ 40 * 6165992 * 2
def baseEnd_6165992 : Nat := 3166117607777744761643125

theorem tailTrace_6165992 : CollatzResearch.WordTrace tailWord_6165992 prefixEnd_6165992 3166117607777744761643125 := by
  unfold tailWord_6165992
  simp only [CollatzResearch.WordTrace]
  refine ⟨112446101938835763219858115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149928135918447684293144153 112446101938835763219858115)
  ·
    refine ⟨168669152908253644829787173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112446101938835763219858115 168669152908253644829787173)
    ·
      refine ⟨31625466170297558405585095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168669152908253644829787173 31625466170297558405585095)
      ·
        refine ⟨47438199255446337608377643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31625466170297558405585095 47438199255446337608377643)
        ·
          refine ⟨71157298883169506412566465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47438199255446337608377643 71157298883169506412566465)
          ·
            refine ⟨53367974162377129809424849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71157298883169506412566465 53367974162377129809424849)
            ·
              refine ⟨40025980621782847357068637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53367974162377129809424849 40025980621782847357068637)
              ·
                refine ⟨15009742733168567758900739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40025980621782847357068637 15009742733168567758900739)
                ·
                  refine ⟨22514614099752851638351109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15009742733168567758900739 22514614099752851638351109)
                  ·
                    refine ⟨4221490143703659682190833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22514614099752851638351109 4221490143703659682190833)
                    ·
                      refine ⟨3166117607777744761643125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221490143703659682190833 3166117607777744761643125)
                      ·
                        rfl

theorem cell23_6165992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6165992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6165992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6165992 prefixEnd_6165992 := by exact prefixLift 6165992
  have htrace : WordTrace (prefixWord ++ tailWord_6165992) baseStart_6165992 baseEnd_6165992 := by
    simpa [prefixWord, tailWord_6165992, baseEnd_6165992] using wordTrace_append hprefix tailTrace_6165992
  have hstable : (prefixWord ++ tailWord_6165992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6165992).length < 2 ^ (prefixWord ++ tailWord_6165992).sum := by decide
  have hdescent : baseEnd_6165992 < baseStart_6165992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6165992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166025 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_6166025 : Nat := 118140960795 + 6166025 * 2 ^ 59
def prefixEnd_6166025 : Nat := 4983230072969 + 3 ^ 40 * 6166025 * 2
def baseEnd_6166025 : Nat := 3166134552639343132530473

theorem tailTrace_6166025 : CollatzResearch.WordTrace tailWord_6166025 prefixEnd_6166025 3166134552639343132530473 := by
  unfold tailWord_6166025
  simp only [CollatzResearch.WordTrace]
  refine ⟨224893407486551973075667529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149928938324367982050445019 224893407486551973075667529)
  ·
    refine ⟨168670055614913979806750647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224893407486551973075667529 168670055614913979806750647)
    ·
      refine ⟨253005083422370969710125971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168670055614913979806750647 253005083422370969710125971)
      ·
        refine ⟨379507625133556454565188957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253005083422370969710125971 379507625133556454565188957)
        ·
          refine ⟨142315359425083670461945859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379507625133556454565188957 142315359425083670461945859)
          ·
            refine ⟨213473039137625505692918789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142315359425083670461945859 213473039137625505692918789)
            ·
              refine ⟨40026194838304782317422273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213473039137625505692918789 40026194838304782317422273)
              ·
                refine ⟨30019646128728586738066705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40026194838304782317422273 30019646128728586738066705)
                ·
                  refine ⟨22514734596546440053550029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30019646128728586738066705 22514734596546440053550029)
                  ·
                    refine ⟨8443025473704915020081261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22514734596546440053550029 8443025473704915020081261)
                    ·
                      refine ⟨3166134552639343132530473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8443025473704915020081261 3166134552639343132530473)
                      ·
                        rfl

theorem cell23_6166025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_6166025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166025 prefixEnd_6166025 := by exact prefixLift 6166025
  have htrace : WordTrace (prefixWord ++ tailWord_6166025) baseStart_6166025 baseEnd_6166025 := by
    simpa [prefixWord, tailWord_6166025, baseEnd_6166025] using wordTrace_append hprefix tailTrace_6166025
  have hstable : (prefixWord ++ tailWord_6166025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166025).length < 2 ^ (prefixWord ++ tailWord_6166025).sum := by decide
  have hdescent : baseEnd_6166025 < baseStart_6166025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166026 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_6166026 : Nat := 118140960795 + 6166026 * 2 ^ 59
def prefixEnd_6166026 : Nat := 4983230072969 + 3 ^ 40 * 6166026 * 2
def baseEnd_6166026 : Nat := 3166135066119997628617969

theorem tailTrace_6166026 : CollatzResearch.WordTrace tailWord_6166026 prefixEnd_6166026 3166135066119997628617969 := by
  unfold tailWord_6166026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56223360989887087561613483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149928962639698900164302621 56223360989887087561613483)
  ·
    refine ⟨84335041484830631342420225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56223360989887087561613483 84335041484830631342420225)
    ·
      refine ⟨63251281113622973506815169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84335041484830631342420225 63251281113622973506815169)
      ·
        refine ⟨47438460835217230130111377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63251281113622973506815169 47438460835217230130111377)
        ·
          refine ⟨35578845626412922597583533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47438460835217230130111377 35578845626412922597583533)
          ·
            refine ⟨13342067109904845974093825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35578845626412922597583533 13342067109904845974093825)
            ·
              refine ⟨10006550332428634480570369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13342067109904845974093825 10006550332428634480570369)
              ·
                refine ⟨7504912749321475860427777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10006550332428634480570369 7504912749321475860427777)
                ·
                  refine ⟨5628684561991106895320833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7504912749321475860427777 5628684561991106895320833)
                  ·
                    refine ⟨4221513421493330171490625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628684561991106895320833 4221513421493330171490625)
                    ·
                      refine ⟨3166135066119997628617969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221513421493330171490625 3166135066119997628617969)
                      ·
                        rfl

theorem cell23_6166026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_6166026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166026 prefixEnd_6166026 := by exact prefixLift 6166026
  have htrace : WordTrace (prefixWord ++ tailWord_6166026) baseStart_6166026 baseEnd_6166026 := by
    simpa [prefixWord, tailWord_6166026, baseEnd_6166026] using wordTrace_append hprefix tailTrace_6166026
  have hstable : (prefixWord ++ tailWord_6166026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166026).length < 2 ^ (prefixWord ++ tailWord_6166026).sum := by decide
  have hdescent : baseEnd_6166026 < baseStart_6166026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166045 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_6166045 : Nat := 118140960795 + 6166045 * 2 ^ 59
def prefixEnd_6166045 : Nat := 4983230072969 + 3 ^ 40 * 6166045 * 2
def baseEnd_6166045 : Nat := 1055381607417477684760127

theorem tailTrace_6166045 : CollatzResearch.WordTrace tailWord_6166045 prefixEnd_6166045 1055381607417477684760127 := by
  unfold tailWord_6166045
  simp only [CollatzResearch.WordTrace]
  refine ⟨224894136946479516491395589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149929424630986344327597059 224894136946479516491395589)
  ·
    refine ⟨42167650677464909342136673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224894136946479516491395589 42167650677464909342136673)
    ·
      refine ⟨31625738008098682006602505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42167650677464909342136673 31625738008098682006602505)
      ·
        refine ⟨23719303506074011504951879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31625738008098682006602505 23719303506074011504951879)
        ·
          refine ⟨35578955259111017257427819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23719303506074011504951879 35578955259111017257427819)
          ·
            refine ⟨53368432888666525886141729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35578955259111017257427819 53368432888666525886141729)
            ·
              refine ⟨40026324666499894414606297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53368432888666525886141729 40026324666499894414606297)
              ·
                refine ⟨30019743499874920810954723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40026324666499894414606297 30019743499874920810954723)
                ·
                  refine ⟨45029615249812381216432085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30019743499874920810954723 45029615249812381216432085)
                  ·
                    refine ⟨1055381607417477684760127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45029615249812381216432085 1055381607417477684760127)
                    ·
                      rfl

theorem cell23_6166045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_6166045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166045 prefixEnd_6166045 := by exact prefixLift 6166045
  have htrace : WordTrace (prefixWord ++ tailWord_6166045) baseStart_6166045 baseEnd_6166045 := by
    simpa [prefixWord, tailWord_6166045, baseEnd_6166045] using wordTrace_append hprefix tailTrace_6166045
  have hstable : (prefixWord ++ tailWord_6166045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166045).length < 2 ^ (prefixWord ++ tailWord_6166045).sum := by decide
  have hdescent : baseEnd_6166045 < baseStart_6166045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166062 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6166062 : Nat := 118140960795 + 6166062 * 2 ^ 59
def prefixEnd_6166062 : Nat := 4983230072969 + 3 ^ 40 * 6166062 * 2
def baseEnd_6166062 : Nat := 1055384517141186495922601

theorem tailTrace_6166062 : CollatzResearch.WordTrace tailWord_6166062 prefixEnd_6166062 1055384517141186495922601 := by
  unfold tailWord_6166062
  simp only [CollatzResearch.WordTrace]
  refine ⟨28111844623427241049345555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149929837991611952263176293 28111844623427241049345555)
  ·
    refine ⟨42167766935140861574018333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28111844623427241049345555 42167766935140861574018333)
    ·
      refine ⟨15812912600677823090256875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42167766935140861574018333 15812912600677823090256875)
      ·
        refine ⟨23719368901016734635385313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15812912600677823090256875 23719368901016734635385313)
        ·
          refine ⟨17789526675762550976538985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23719368901016734635385313 17789526675762550976538985)
          ·
            refine ⟨13342145006821913232404239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17789526675762550976538985 13342145006821913232404239)
            ·
              refine ⟨20013217510232869848606359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13342145006821913232404239 20013217510232869848606359)
              ·
                refine ⟨30019826265349304772909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20013217510232869848606359 30019826265349304772909539)
                ·
                  refine ⟨45029739398023957159364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30019826265349304772909539 45029739398023957159364309)
                  ·
                    refine ⟨1055384517141186495922601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45029739398023957159364309 1055384517141186495922601)
                    ·
                      rfl

theorem cell23_6166062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6166062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166062 prefixEnd_6166062 := by exact prefixLift 6166062
  have htrace : WordTrace (prefixWord ++ tailWord_6166062) baseStart_6166062 baseEnd_6166062 := by
    simpa [prefixWord, tailWord_6166062, baseEnd_6166062] using wordTrace_append hprefix tailTrace_6166062
  have hstable : (prefixWord ++ tailWord_6166062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166062).length < 2 ^ (prefixWord ++ tailWord_6166062).sum := by decide
  have hdescent : baseEnd_6166062 < baseStart_6166062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166092 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_6166092 : Nat := 118140960795 + 6166092 * 2 ^ 59
def prefixEnd_6166092 : Nat := 4983230072969 + 3 ^ 40 * 6166092 * 2
def baseEnd_6166092 : Nat := 1055389651947731456797555

theorem tailTrace_6166092 : CollatzResearch.WordTrace tailWord_6166092 prefixEnd_6166092 1055389651947731456797555 := by
  unfold tailWord_6166092
  simp only [CollatzResearch.WordTrace]
  refine ⟨112447925588654621759178265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149930567451539495678904353 112447925588654621759178265)
  ·
    refine ⟨84335944191490966319383699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112447925588654621759178265 84335944191490966319383699)
    ·
      refine ⟨126503916287236449479075549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84335944191490966319383699 126503916287236449479075549)
      ·
        refine ⟨47438968607713668554653331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126503916287236449479075549 47438968607713668554653331)
        ·
          refine ⟨71158452911570502831979997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47438968607713668554653331 71158452911570502831979997)
          ·
            refine ⟨26684419841838938561992499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71158452911570502831979997 26684419841838938561992499)
            ·
              refine ⟨40026629762758407842988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26684419841838938561992499 40026629762758407842988749)
              ·
                refine ⟨15009986161034402941120781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40026629762758407842988749 15009986161034402941120781)
                ·
                  refine ⟨5628744810387901102920293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15009986161034402941120781 5628744810387901102920293)
                  ·
                    refine ⟨1055389651947731456797555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628744810387901102920293 1055389651947731456797555)
                    ·
                      rfl

theorem cell23_6166092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_6166092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166092 prefixEnd_6166092 := by exact prefixLift 6166092
  have htrace : WordTrace (prefixWord ++ tailWord_6166092) baseStart_6166092 baseEnd_6166092 := by
    simpa [prefixWord, tailWord_6166092, baseEnd_6166092] using wordTrace_append hprefix tailTrace_6166092
  have hstable : (prefixWord ++ tailWord_6166092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166092).length < 2 ^ (prefixWord ++ tailWord_6166092).sum := by decide
  have hdescent : baseEnd_6166092 < baseStart_6166092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166105 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 6]
def baseStart_6166105 : Nat := 118140960795 + 6166105 * 2 ^ 59
def prefixEnd_6166105 : Nat := 4983230072969 + 3 ^ 40 * 6166105 * 2
def baseEnd_6166105 : Nat := 351797292343522535503345

theorem tailTrace_6166105 : CollatzResearch.WordTrace tailWord_6166105 prefixEnd_6166105 351797292343522535503345 := by
  unfold tailWord_6166105
  simp only [CollatzResearch.WordTrace]
  refine ⟨224896325326262146738579769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149930883550841431159053179 224896325326262146738579769)
  ·
    refine ⟨168672243994696610053934827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224896325326262146738579769 168672243994696610053934827)
    ·
      refine ⟨253008365992044915080902241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168672243994696610053934827 253008365992044915080902241)
      ·
        refine ⟨189756274494033686310676681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253008365992044915080902241 189756274494033686310676681)
        ·
          refine ⟨142317205870525264733007511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189756274494033686310676681 142317205870525264733007511)
          ·
            refine ⟨213475808805787897099511267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142317205870525264733007511 213475808805787897099511267)
            ·
              refine ⟨320213713208681845649266901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213475808805787897099511267 320213713208681845649266901)
              ·
                refine ⟨7505008903328480757404693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 320213713208681845649266901 7505008903328480757404693)
                ·
                  refine ⟨351797292343522535503345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7505008903328480757404693 351797292343522535503345)
                  ·
                    rfl

theorem cell23_6166105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_6166105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166105 prefixEnd_6166105 := by exact prefixLift 6166105
  have htrace : WordTrace (prefixWord ++ tailWord_6166105) baseStart_6166105 baseEnd_6166105 := by
    simpa [prefixWord, tailWord_6166105, baseEnd_6166105] using wordTrace_append hprefix tailTrace_6166105
  have hstable : (prefixWord ++ tailWord_6166105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166105).length < 2 ^ (prefixWord ++ tailWord_6166105).sum := by decide
  have hdescent : baseEnd_6166105 < baseStart_6166105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166135 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 5, 5]
def baseStart_6166135 : Nat := 118140960795 + 6166135 * 2 ^ 59
def prefixEnd_6166135 : Nat := 4983230072969 + 3 ^ 40 * 6166135 * 2
def baseEnd_6166135 : Nat := 1055397011837112567384989

theorem tailTrace_6166135 : CollatzResearch.WordTrace tailWord_6166135 prefixEnd_6166135 1055397011837112567384989 := by
  unfold tailWord_6166135
  simp only [CollatzResearch.WordTrace]
  refine ⟨224897419516153461862171859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149931613010768974574781239 224897419516153461862171859)
  ·
    refine ⟨337346129274230192793257789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224897419516153461862171859 337346129274230192793257789)
    ·
      refine ⟨126504798477836322297471671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337346129274230192793257789 126504798477836322297471671)
      ·
        refine ⟨189757197716754483446207507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126504798477836322297471671 189757197716754483446207507)
        ·
          refine ⟨284635796575131725169311261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189757197716754483446207507 284635796575131725169311261)
          ·
            refine ⟨106738423715674396938491723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284635796575131725169311261 106738423715674396938491723)
            ·
              refine ⟨160107635573511595407737585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106738423715674396938491723 160107635573511595407737585)
              ·
                refine ⟨120080726680133696555803189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160107635573511595407737585 120080726680133696555803189)
                ·
                  refine ⟨11257568126262534052106549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120080726680133696555803189 11257568126262534052106549)
                  ·
                    refine ⟨1055397011837112567384989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11257568126262534052106549 1055397011837112567384989)
                    ·
                      rfl

theorem cell23_6166135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_6166135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166135 prefixEnd_6166135 := by exact prefixLift 6166135
  have htrace : WordTrace (prefixWord ++ tailWord_6166135) baseStart_6166135 baseEnd_6166135 := by
    simpa [prefixWord, tailWord_6166135, baseEnd_6166135] using wordTrace_append hprefix tailTrace_6166135
  have hstable : (prefixWord ++ tailWord_6166135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166135).length < 2 ^ (prefixWord ++ tailWord_6166135).sum := by decide
  have hdescent : baseEnd_6166135 < baseStart_6166135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166165 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_6166165 : Nat := 118140960795 + 6166165 * 2 ^ 59
def prefixEnd_6166165 : Nat := 4983230072969 + 3 ^ 40 * 6166165 * 2
def baseEnd_6166165 : Nat := 1055402146643657528259943

theorem tailTrace_6166165 : CollatzResearch.WordTrace tailWord_6166165 prefixEnd_6166165 1055402146643657528259943 := by
  unfold tailWord_6166165
  simp only [CollatzResearch.WordTrace]
  refine ⟨224898513706044776985763949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149932342470696517990509299 224898513706044776985763949)
  ·
    refine ⟨84336942639766791369661481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224898513706044776985763949 84336942639766791369661481)
    ·
      refine ⟨63252706979825093527246111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84336942639766791369661481 63252706979825093527246111)
      ·
        refine ⟨94879060469737640290869167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63252706979825093527246111 94879060469737640290869167)
        ·
          refine ⟨142318590704606460436303751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94879060469737640290869167 142318590704606460436303751)
          ·
            refine ⟨213477886056909690654455627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142318590704606460436303751 213477886056909690654455627)
            ·
              refine ⟨320216829085364535981683441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213477886056909690654455627 320216829085364535981683441)
              ·
                refine ⟨240162621814023401986262581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320216829085364535981683441 240162621814023401986262581)
                ·
                  refine ⟨22515245795064693936212117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240162621814023401986262581 22515245795064693936212117)
                  ·
                    refine ⟨1055402146643657528259943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22515245795064693936212117 1055402146643657528259943)
                    ·
                      rfl

theorem cell23_6166165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_6166165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166165 prefixEnd_6166165 := by exact prefixLift 6166165
  have htrace : WordTrace (prefixWord ++ tailWord_6166165) baseStart_6166165 baseEnd_6166165 := by
    simpa [prefixWord, tailWord_6166165, baseEnd_6166165] using wordTrace_append hprefix tailTrace_6166165
  have hstable : (prefixWord ++ tailWord_6166165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166165).length < 2 ^ (prefixWord ++ tailWord_6166165).sum := by decide
  have hdescent : baseEnd_6166165 < baseStart_6166165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166176 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2]
def baseStart_6166176 : Nat := 118140960795 + 6166176 * 2 ^ 59
def prefixEnd_6166176 : Nat := 4983230072969 + 3 ^ 40 * 6166176 * 2
def baseEnd_6166176 : Nat := 3166212088218172041742279

theorem tailTrace_6166176 : CollatzResearch.WordTrace tailWord_6166176 prefixEnd_6166176 3166212088218172041742279 := by
  unfold tailWord_6166176
  simp only [CollatzResearch.WordTrace]
  refine ⟨112449457454502462932207191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149932609939336617242942921 112449457454502462932207191)
  ·
    refine ⟨168674186181753694398310787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112449457454502462932207191 168674186181753694398310787)
    ·
      refine ⟨253011279272630541597466181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168674186181753694398310787 253011279272630541597466181)
      ·
        refine ⟨47439614863618226549524909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253011279272630541597466181 47439614863618226549524909)
        ·
          refine ⟨17789855573856834956071841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47439614863618226549524909 17789855573856834956071841)
          ·
            refine ⟨13342391680392626217053881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17789855573856834956071841 13342391680392626217053881)
            ·
              refine ⟨10006793760294469662790411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13342391680392626217053881 10006793760294469662790411)
              ·
                refine ⟨15010190640441704494185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006793760294469662790411 15010190640441704494185617)
                ·
                  refine ⟨11257642980331278370639213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15010190640441704494185617 11257642980331278370639213)
                  ·
                    refine ⟨4221616117624229388989705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11257642980331278370639213 4221616117624229388989705)
                    ·
                      refine ⟨3166212088218172041742279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221616117624229388989705 3166212088218172041742279)
                      ·
                        rfl

theorem cell23_6166176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_6166176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166176 prefixEnd_6166176 := by exact prefixLift 6166176
  have htrace : WordTrace (prefixWord ++ tailWord_6166176) baseStart_6166176 baseEnd_6166176 := by
    simpa [prefixWord, tailWord_6166176, baseEnd_6166176] using wordTrace_append hprefix tailTrace_6166176
  have hstable : (prefixWord ++ tailWord_6166176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166176).length < 2 ^ (prefixWord ++ tailWord_6166176).sum := by decide
  have hdescent : baseEnd_6166176 < baseStart_6166176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166185 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_6166185 : Nat := 118140960795 + 6166185 * 2 ^ 59
def prefixEnd_6166185 : Nat := 4983230072969 + 3 ^ 40 * 6166185 * 2
def baseEnd_6166185 : Nat := 3166216709544062506529737

theorem tailTrace_6166185 : CollatzResearch.WordTrace tailWord_6166185 prefixEnd_6166185 3166216709544062506529737 := by
  unfold tailWord_6166185
  simp only [CollatzResearch.WordTrace]
  refine ⟨224899243165972320401492009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149932828777314880267661339 224899243165972320401492009)
  ·
    refine ⟨168674432374479240301119007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224899243165972320401492009 168674432374479240301119007)
    ·
      refine ⟨253011648561718860451678511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168674432374479240301119007 253011648561718860451678511)
      ·
        refine ⟨379517472842578290677517767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253011648561718860451678511 379517472842578290677517767)
        ·
          refine ⟨569276209263867436016276651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379517472842578290677517767 569276209263867436016276651)
          ·
            refine ⟨853914313895801154024414977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569276209263867436016276651 853914313895801154024414977)
            ·
              refine ⟨640435735421850865518311233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853914313895801154024414977 640435735421850865518311233)
              ·
                refine ⟨480326801566388149138733425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640435735421850865518311233 480326801566388149138733425)
                ·
                  refine ⟨360245101174791111854050069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480326801566388149138733425 360245101174791111854050069)
                  ·
                    refine ⟨16886489117568333368158597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360245101174791111854050069 16886489117568333368158597)
                    ·
                      refine ⟨3166216709544062506529737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16886489117568333368158597 3166216709544062506529737)
                      ·
                        rfl

theorem cell23_6166185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_6166185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166185 prefixEnd_6166185 := by exact prefixLift 6166185
  have htrace : WordTrace (prefixWord ++ tailWord_6166185) baseStart_6166185 baseEnd_6166185 := by
    simpa [prefixWord, tailWord_6166185, baseEnd_6166185] using wordTrace_append hprefix tailTrace_6166185
  have hstable : (prefixWord ++ tailWord_6166185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166185).length < 2 ^ (prefixWord ++ tailWord_6166185).sum := by decide
  have hdescent : baseEnd_6166185 < baseStart_6166185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166192 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_6166192 : Nat := 118140960795 + 6166192 * 2 ^ 59
def prefixEnd_6166192 : Nat := 4983230072969 + 3 ^ 40 * 6166192 * 2
def baseEnd_6166192 : Nat := 3166220303908643979142205

theorem tailTrace_6166192 : CollatzResearch.WordTrace tailWord_6166192 prefixEnd_6166192 3166220303908643979142205 := by
  unfold tailWord_6166192
  simp only [CollatzResearch.WordTrace]
  refine ⟨112449749238473480298498415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149932998984631307064664553 112449749238473480298498415)
  ·
    refine ⟨168674623857710220447747623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112449749238473480298498415 168674623857710220447747623)
    ·
      refine ⟨253011935786565330671621435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168674623857710220447747623 253011935786565330671621435)
      ·
        refine ⟨379517903679847996007432153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253011935786565330671621435 379517903679847996007432153)
        ·
          refine ⟨284638427759885997005574115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379517903679847996007432153 284638427759885997005574115)
          ·
            refine ⟨426957641639828995508361173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284638427759885997005574115 426957641639828995508361173)
            ·
              refine ⟨10006819725933492082227215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 426957641639828995508361173 10006819725933492082227215)
              ·
                refine ⟨15010229588900238123340823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006819725933492082227215 15010229588900238123340823)
                ·
                  refine ⟨22515344383350357185011235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15010229588900238123340823 22515344383350357185011235)
                  ·
                    refine ⟨33773016575025535777516853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22515344383350357185011235 33773016575025535777516853)
                    ·
                      refine ⟨3166220303908643979142205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33773016575025535777516853 3166220303908643979142205)
                      ·
                        rfl

theorem cell23_6166192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_6166192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166192 prefixEnd_6166192 := by exact prefixLift 6166192
  have htrace : WordTrace (prefixWord ++ tailWord_6166192) baseStart_6166192 baseEnd_6166192 := by
    simpa [prefixWord, tailWord_6166192, baseEnd_6166192] using wordTrace_append hprefix tailTrace_6166192
  have hstable : (prefixWord ++ tailWord_6166192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166192).length < 2 ^ (prefixWord ++ tailWord_6166192).sum := by decide
  have hdescent : baseEnd_6166192 < baseStart_6166192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166199 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 2, 4]
def baseStart_6166199 : Nat := 118140960795 + 6166199 * 2 ^ 59
def prefixEnd_6166199 : Nat := 4983230072969 + 3 ^ 40 * 6166199 * 2
def baseEnd_6166199 : Nat := 1055407966091075150584891

theorem tailTrace_6166199 : CollatzResearch.WordTrace tailWord_6166199 prefixEnd_6166199 1055407966091075150584891 := by
  unfold tailWord_6166199
  simp only [CollatzResearch.WordTrace]
  refine ⟨224899753787921600792501651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149933169191947733861667767 224899753787921600792501651)
  ·
    refine ⟨337349630681882401188752477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224899753787921600792501651 337349630681882401188752477)
    ·
      refine ⟨126506111505705900445782179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337349630681882401188752477 126506111505705900445782179)
      ·
        refine ⟨189759167258558850668673269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126506111505705900445782179 189759167258558850668673269)
        ·
          refine ⟨17789921930489892250188119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189759167258558850668673269 17789921930489892250188119)
          ·
            refine ⟨26684882895734838375282179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17789921930489892250188119 26684882895734838375282179)
            ·
              refine ⟨40027324343602257562923269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26684882895734838375282179 40027324343602257562923269)
              ·
                refine ⟨7505123314425423293048113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40027324343602257562923269 7505123314425423293048113)
                ·
                  refine ⟨5628842485819067469786085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505123314425423293048113 5628842485819067469786085)
                  ·
                    refine ⟨1055407966091075150584891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5628842485819067469786085 1055407966091075150584891)
                    ·
                      rfl

theorem cell23_6166199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_6166199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166199 prefixEnd_6166199 := by exact prefixLift 6166199
  have htrace : WordTrace (prefixWord ++ tailWord_6166199) baseStart_6166199 baseEnd_6166199 := by
    simpa [prefixWord, tailWord_6166199, baseEnd_6166199] using wordTrace_append hprefix tailTrace_6166199
  have hstable : (prefixWord ++ tailWord_6166199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166199).length < 2 ^ (prefixWord ++ tailWord_6166199).sum := by decide
  have hdescent : baseEnd_6166199 < baseStart_6166199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166239 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_6166239 : Nat := 118140960795 + 6166239 * 2 ^ 59
def prefixEnd_6166239 : Nat := 4983230072969 + 3 ^ 40 * 6166239 * 2
def baseEnd_6166239 : Nat := 3166244437499405295254489

theorem tailTrace_6166239 : CollatzResearch.WordTrace tailWord_6166239 prefixEnd_6166239 3166244437499405295254489 := by
  unfold tailWord_6166239
  simp only [CollatzResearch.WordTrace]
  refine ⟨224901212707776687623957771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149934141805184458415971847 224901212707776687623957771)
  ·
    refine ⟨337351819061665031435936657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224901212707776687623957771 337351819061665031435936657)
    ·
      refine ⟨253013864296248773576952493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337351819061665031435936657 253013864296248773576952493)
      ·
        refine ⟨94880199111093290091357185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253013864296248773576952493 94880199111093290091357185)
        ·
          refine ⟨71160149333319967568517889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94880199111093290091357185 71160149333319967568517889)
          ·
            refine ⟨53370111999989975676388417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71160149333319967568517889 53370111999989975676388417)
            ·
              refine ⟨40027583999992481757291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53370111999989975676388417 40027583999992481757291313)
              ·
                refine ⟨30020687999994361317968485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40027583999992481757291313 30020687999994361317968485)
                ·
                  refine ⟨5628878999998942747119091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30020687999994361317968485 5628878999998942747119091)
                  ·
                    refine ⟨8443318499998414120678637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5628878999998942747119091 8443318499998414120678637)
                    ·
                      refine ⟨3166244437499405295254489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8443318499998414120678637 3166244437499405295254489)
                      ·
                        rfl

theorem cell23_6166239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_6166239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166239 prefixEnd_6166239 := by exact prefixLift 6166239
  have htrace : WordTrace (prefixWord ++ tailWord_6166239) baseStart_6166239 baseEnd_6166239 := by
    simpa [prefixWord, tailWord_6166239, baseEnd_6166239] using wordTrace_append hprefix tailTrace_6166239
  have hstable : (prefixWord ++ tailWord_6166239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166239).length < 2 ^ (prefixWord ++ tailWord_6166239).sum := by decide
  have hdescent : baseEnd_6166239 < baseStart_6166239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166296 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_6166296 : Nat := 118140960795 + 6166296 * 2 ^ 59
def prefixEnd_6166296 : Nat := 4983230072969 + 3 ^ 40 * 6166296 * 2
def baseEnd_6166296 : Nat := 3166273705896711572241727

theorem tailTrace_6166296 : CollatzResearch.WordTrace tailWord_6166296 prefixEnd_6166296 3166273705896711572241727 := by
  unfold tailWord_6166296
  simp only [CollatzResearch.WordTrace]
  refine ⟨112451645834285093179391371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149935527779046790905855161 112451645834285093179391371)
  ·
    refine ⟨168677468751427639769087057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112451645834285093179391371 168677468751427639769087057)
    ·
      refine ⟨126508101563570729826815293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168677468751427639769087057 126508101563570729826815293)
      ·
        refine ⟨47440538086339023685055735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126508101563570729826815293 47440538086339023685055735)
        ·
          refine ⟨71160807129508535527583603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47440538086339023685055735 71160807129508535527583603)
          ·
            refine ⟨106741210694262803291375405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71160807129508535527583603 106741210694262803291375405)
            ·
              refine ⟨40027954010348551234265777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106741210694262803291375405 40027954010348551234265777)
              ·
                refine ⟨30020965507761413425699333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40027954010348551234265777 30020965507761413425699333)
                ·
                  refine ⟨5628931032705265017318625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30020965507761413425699333 5628931032705265017318625)
                  ·
                    refine ⟨4221698274528948762988969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628931032705265017318625 4221698274528948762988969)
                    ·
                      refine ⟨3166273705896711572241727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221698274528948762988969 3166273705896711572241727)
                      ·
                        rfl

theorem cell23_6166296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_6166296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166296 prefixEnd_6166296 := by exact prefixLift 6166296
  have htrace : WordTrace (prefixWord ++ tailWord_6166296) baseStart_6166296 baseEnd_6166296 := by
    simpa [prefixWord, tailWord_6166296, baseEnd_6166296] using wordTrace_append hprefix tailTrace_6166296
  have hstable : (prefixWord ++ tailWord_6166296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166296).length < 2 ^ (prefixWord ++ tailWord_6166296).sum := by decide
  have hdescent : baseEnd_6166296 < baseStart_6166296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166330 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2]
def baseStart_6166330 : Nat := 118140960795 + 6166330 * 2 ^ 59
def prefixEnd_6166330 : Nat := 4983230072969 + 3 ^ 40 * 6166330 * 2
def baseEnd_6166330 : Nat := 3166291164238964439216571

theorem tailTrace_6166330 : CollatzResearch.WordTrace tailWord_6166330 prefixEnd_6166330 3166291164238964439216571 := by
  unfold tailWord_6166330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56226132937611752541380111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149936354500298006777013629 56226132937611752541380111)
  ·
    refine ⟨84339199406417628812070167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56226132937611752541380111 84339199406417628812070167)
    ·
      refine ⟨126508799109626443218105251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84339199406417628812070167 126508799109626443218105251)
      ·
        refine ⟨189763198664439664827157877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126508799109626443218105251 189763198664439664827157877)
        ·
          refine ⟨17790299874791218577546051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189763198664439664827157877 17790299874791218577546051)
          ·
            refine ⟨26685449812186827866319077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17790299874791218577546051 26685449812186827866319077)
            ·
              refine ⟨5003521839785030224934827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26685449812186827866319077 5003521839785030224934827)
              ·
                refine ⟨7505282759677545337402241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003521839785030224934827 7505282759677545337402241)
                ·
                  refine ⟨5628962069758159003051681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505282759677545337402241 5628962069758159003051681)
                  ·
                    refine ⟨4221721552318619252288761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5628962069758159003051681 4221721552318619252288761)
                    ·
                      refine ⟨3166291164238964439216571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221721552318619252288761 3166291164238964439216571)
                      ·
                        rfl

theorem cell23_6166330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_6166330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166330 prefixEnd_6166330 := by exact prefixLift 6166330
  have htrace : WordTrace (prefixWord ++ tailWord_6166330) baseStart_6166330 baseEnd_6166330 := by
    simpa [prefixWord, tailWord_6166330, baseEnd_6166330] using wordTrace_append hprefix tailTrace_6166330
  have hstable : (prefixWord ++ tailWord_6166330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166330).length < 2 ^ (prefixWord ++ tailWord_6166330).sum := by decide
  have hdescent : baseEnd_6166330 < baseStart_6166330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166332 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_6166332 : Nat := 118140960795 + 6166332 * 2 ^ 59
def prefixEnd_6166332 : Nat := 4983230072969 + 3 ^ 40 * 6166332 * 2
def baseEnd_6166332 : Nat := 1055430730400091143797187

theorem tailTrace_6166332 : CollatzResearch.WordTrace tailWord_6166332 prefixEnd_6166332 1055430730400091143797187 := by
  unfold tailWord_6166332
  simp only [CollatzResearch.WordTrace]
  refine ⟨112452302348219882253546625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149936403130959843004728833 112452302348219882253546625)
  ·
    refine ⟨84339226761164911690159969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112452302348219882253546625 84339226761164911690159969)
    ·
      refine ⟨63254420070873683767619977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84339226761164911690159969 63254420070873683767619977)
      ·
        refine ⟨47440815053155262825714983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63254420070873683767619977 47440815053155262825714983)
        ·
          refine ⟨71161222579732894238572475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47440815053155262825714983 71161222579732894238572475)
          ·
            refine ⟨106741833869599341357858713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71161222579732894238572475 106741833869599341357858713)
            ·
              refine ⟨80056375402199506018394035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106741833869599341357858713 80056375402199506018394035)
              ·
                refine ⟨120084563103299259027591053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80056375402199506018394035 120084563103299259027591053)
                ·
                  refine ⟨45031711163737222135346645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120084563103299259027591053 45031711163737222135346645)
                  ·
                    refine ⟨1055430730400091143797187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45031711163737222135346645 1055430730400091143797187)
                    ·
                      rfl

theorem cell23_6166332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_6166332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166332 prefixEnd_6166332 := by exact prefixLift 6166332
  have htrace : WordTrace (prefixWord ++ tailWord_6166332) baseStart_6166332 baseEnd_6166332 := by
    simpa [prefixWord, tailWord_6166332, baseEnd_6166332] using wordTrace_append hprefix tailTrace_6166332
  have hstable : (prefixWord ++ tailWord_6166332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166332).length < 2 ^ (prefixWord ++ tailWord_6166332).sum := by decide
  have hdescent : baseEnd_6166332 < baseStart_6166332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166369 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6166369 : Nat := 118140960795 + 6166369 * 2 ^ 59
def prefixEnd_6166369 : Nat := 4983230072969 + 3 ^ 40 * 6166369 * 2
def baseEnd_6166369 : Nat := 3166311189984489786628891

theorem tailTrace_6166369 : CollatzResearch.WordTrace tailWord_6166369 prefixEnd_6166369 3166311189984489786628891 := by
  unfold tailWord_6166369
  simp only [CollatzResearch.WordTrace]
  refine ⟨224905954197305719826190161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149937302798203813217460107 224905954197305719826190161)
  ·
    refine ⟨168679465647979289869642621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224905954197305719826190161 168679465647979289869642621)
    ·
      refine ⟨63254799617992233701115983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168679465647979289869642621 63254799617992233701115983)
      ·
        refine ⟨94882199426988350551673975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63254799617992233701115983 94882199426988350551673975)
        ·
          refine ⟨142323299140482525827510963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94882199426988350551673975 142323299140482525827510963)
          ·
            refine ⟨213484948710723788741266445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142323299140482525827510963 213484948710723788741266445)
            ·
              refine ⟨80056855766521420777974917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213484948710723788741266445 80056855766521420777974917)
              ·
                refine ⟨15010660456222766395870297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80056855766521420777974917 15010660456222766395870297)
                ·
                  refine ⟨11257995342167074796902723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15010660456222766395870297 11257995342167074796902723)
                  ·
                    refine ⟨16886993013250612195354085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11257995342167074796902723 16886993013250612195354085)
                    ·
                      refine ⟨3166311189984489786628891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16886993013250612195354085 3166311189984489786628891)
                      ·
                        rfl

theorem cell23_6166369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6166369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166369 prefixEnd_6166369 := by exact prefixLift 6166369
  have htrace : WordTrace (prefixWord ++ tailWord_6166369) baseStart_6166369 baseEnd_6166369 := by
    simpa [prefixWord, tailWord_6166369, baseEnd_6166369] using wordTrace_append hprefix tailTrace_6166369
  have hstable : (prefixWord ++ tailWord_6166369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166369).length < 2 ^ (prefixWord ++ tailWord_6166369).sum := by decide
  have hdescent : baseEnd_6166369 < baseStart_6166369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166370 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_6166370 : Nat := 118140960795 + 6166370 * 2 ^ 59
def prefixEnd_6166370 : Nat := 4983230072969 + 3 ^ 40 * 6166370 * 2
def baseEnd_6166370 : Nat := 351812411496127142524043

theorem tailTrace_6166370 : CollatzResearch.WordTrace tailWord_6166370 prefixEnd_6166370 351812411496127142524043 := by
  unfold tailWord_6166370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56226497667575524249244141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149937327113534731331317709 56226497667575524249244141)
  ·
    refine ⟨21084936625340821593466553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56226497667575524249244141 21084936625340821593466553)
    ·
      refine ⟨15813702469005616195099915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21084936625340821593466553 15813702469005616195099915)
      ·
        refine ⟨23720553703508424292649873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813702469005616195099915 23720553703508424292649873)
        ·
          refine ⟨17790415277631318219487405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23720553703508424292649873 17790415277631318219487405)
          ·
            refine ⟨6671405729111744332307777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17790415277631318219487405 6671405729111744332307777)
            ·
              refine ⟨5003554296833808249230833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6671405729111744332307777 5003554296833808249230833)
              ·
                refine ⟨3752665722625356186923125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003554296833808249230833 3752665722625356186923125)
                ·
                  refine ⟨351812411496127142524043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752665722625356186923125 351812411496127142524043)
                  ·
                    rfl

theorem cell23_6166370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_6166370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166370 prefixEnd_6166370 := by exact prefixLift 6166370
  have htrace : WordTrace (prefixWord ++ tailWord_6166370) baseStart_6166370 baseEnd_6166370 := by
    simpa [prefixWord, tailWord_6166370, baseEnd_6166370] using wordTrace_append hprefix tailTrace_6166370
  have hstable : (prefixWord ++ tailWord_6166370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166370).length < 2 ^ (prefixWord ++ tailWord_6166370).sum := by decide
  have hdescent : baseEnd_6166370 < baseStart_6166370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166379 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 3, 4]
def baseStart_6166379 : Nat := 118140960795 + 6166379 * 2 ^ 59
def prefixEnd_6166379 : Nat := 4983230072969 + 3 ^ 40 * 6166379 * 2
def baseEnd_6166379 : Nat := 1055438774930344915834615

theorem tailTrace_6166379 : CollatzResearch.WordTrace tailWord_6166379 prefixEnd_6166379 1055438774930344915834615 := by
  unfold tailWord_6166379
  simp only [CollatzResearch.WordTrace]
  refine ⟨224906318927269491534054191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149937545951512994356036127 224906318927269491534054191)
  ·
    refine ⟨337359478390904237301081287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224906318927269491534054191 337359478390904237301081287)
    ·
      refine ⟨506039217586356355951621931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337359478390904237301081287 506039217586356355951621931)
      ·
        refine ⟨759058826379534533927432897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506039217586356355951621931 759058826379534533927432897)
        ·
          refine ⟨569294119784650900445574673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759058826379534533927432897 569294119784650900445574673)
          ·
            refine ⟨426970589838488175334181005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569294119784650900445574673 426970589838488175334181005)
            ·
              refine ⟨160113971189433065750317877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426970589838488175334181005 160113971189433065750317877)
              ·
                refine ⟨15010684799009349914092301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160113971189433065750317877 15010684799009349914092301)
                ·
                  refine ⟨5629006799628506217784613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15010684799009349914092301 5629006799628506217784613)
                  ·
                    refine ⟨1055438774930344915834615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629006799628506217784613 1055438774930344915834615)
                    ·
                      rfl

theorem cell23_6166379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 4].length) (baseStart_6166379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166379 prefixEnd_6166379 := by exact prefixLift 6166379
  have htrace : WordTrace (prefixWord ++ tailWord_6166379) baseStart_6166379 baseEnd_6166379 := by
    simpa [prefixWord, tailWord_6166379, baseEnd_6166379] using wordTrace_append hprefix tailTrace_6166379
  have hstable : (prefixWord ++ tailWord_6166379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166379).length < 2 ^ (prefixWord ++ tailWord_6166379).sum := by decide
  have hdescent : baseEnd_6166379 < baseStart_6166379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166426 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_6166426 : Nat := 118140960795 + 6166426 * 2 ^ 59
def prefixEnd_6166426 : Nat := 4983230072969 + 3 ^ 40 * 6166426 * 2
def baseEnd_6166426 : Nat := 351815606486866229290681

theorem tailTrace_6166426 : CollatzResearch.WordTrace tailWord_6166426 prefixEnd_6166426 351815606486866229290681 := by
  unfold tailWord_6166426
  simp only [CollatzResearch.WordTrace]
  refine ⟨56227008289524804640253783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149938688772066145707343421 56227008289524804640253783)
  ·
    refine ⟨84340512434287206960380675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56227008289524804640253783 84340512434287206960380675)
    ·
      refine ⟨126510768651430810440571013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84340512434287206960380675 126510768651430810440571013)
      ·
        refine ⟨23720769122143276957607065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126510768651430810440571013 23720769122143276957607065)
        ·
          refine ⟨17790576841607457718205299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23720769122143276957607065 17790576841607457718205299)
          ·
            refine ⟨26685865262411186577307949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17790576841607457718205299 26685865262411186577307949)
            ·
              refine ⟨10007199473404194966490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26685865262411186577307949 10007199473404194966490481)
              ·
                refine ⟨7505399605053146224867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10007199473404194966490481 7505399605053146224867861)
                ·
                  refine ⟨351815606486866229290681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7505399605053146224867861 351815606486866229290681)
                  ·
                    rfl

theorem cell23_6166426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_6166426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166426 prefixEnd_6166426 := by exact prefixLift 6166426
  have htrace : WordTrace (prefixWord ++ tailWord_6166426) baseStart_6166426 baseEnd_6166426 := by
    simpa [prefixWord, tailWord_6166426, baseEnd_6166426] using wordTrace_append hprefix tailTrace_6166426
  have hstable : (prefixWord ++ tailWord_6166426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166426).length < 2 ^ (prefixWord ++ tailWord_6166426).sum := by decide
  have hdescent : baseEnd_6166426 < baseStart_6166426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166429 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6166429 : Nat := 118140960795 + 6166429 * 2 ^ 59
def prefixEnd_6166429 : Nat := 4983230072969 + 3 ^ 40 * 6166429 * 2
def baseEnd_6166429 : Nat := 3166341998823759551878615

theorem tailTrace_6166429 : CollatzResearch.WordTrace tailWord_6166429 prefixEnd_6166429 3166341998823759551878615 := by
  unfold tailWord_6166429
  simp only [CollatzResearch.WordTrace]
  refine ⟨224908142577088350073374341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149938761718058900048916227 224908142577088350073374341)
  ·
    refine ⟨42170276733204065638757689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224908142577088350073374341 42170276733204065638757689)
    ·
      refine ⟨31627707549903049229068267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42170276733204065638757689 31627707549903049229068267)
      ·
        refine ⟨47441561324854573843602401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31627707549903049229068267 47441561324854573843602401)
        ·
          refine ⟨35581170993640930382701801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47441561324854573843602401 35581170993640930382701801)
          ·
            refine ⟨26685878245230697787026351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35581170993640930382701801 26685878245230697787026351)
            ·
              refine ⟨40028817367846046680539527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26685878245230697787026351 40028817367846046680539527)
              ·
                refine ⟨60043226051769070020809291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40028817367846046680539527 60043226051769070020809291)
                ·
                  refine ⟨90064839077653605031213937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60043226051769070020809291 90064839077653605031213937)
                  ·
                    refine ⟨67548629308240203773410453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90064839077653605031213937 67548629308240203773410453)
                    ·
                      refine ⟨3166341998823759551878615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67548629308240203773410453 3166341998823759551878615)
                      ·
                        rfl

theorem cell23_6166429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6166429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166429 prefixEnd_6166429 := by exact prefixLift 6166429
  have htrace : WordTrace (prefixWord ++ tailWord_6166429) baseStart_6166429 baseEnd_6166429 := by
    simpa [prefixWord, tailWord_6166429, baseEnd_6166429] using wordTrace_append hprefix tailTrace_6166429
  have hstable : (prefixWord ++ tailWord_6166429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166429).length < 2 ^ (prefixWord ++ tailWord_6166429).sum := by decide
  have hdescent : baseEnd_6166429 < baseStart_6166429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166453 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_6166453 : Nat := 118140960795 + 6166453 * 2 ^ 59
def prefixEnd_6166453 : Nat := 4983230072969 + 3 ^ 40 * 6166453 * 2
def baseEnd_6166453 : Nat := 3166354322359467457978505

theorem tailTrace_6166453 : CollatzResearch.WordTrace tailWord_6166453 prefixEnd_6166453 3166354322359467457978505 := by
  unfold tailWord_6166453
  simp only [CollatzResearch.WordTrace]
  refine ⟨224909017929001402172248013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149939345286000934781498675 224909017929001402172248013)
  ·
    refine ⟨84340881723375525814593005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224909017929001402172248013 84340881723375525814593005)
    ·
      refine ⟨31627830646265822180472377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84340881723375525814593005 31627830646265822180472377)
      ·
        refine ⟨23720872984699366635354283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31627830646265822180472377 23720872984699366635354283)
        ·
          refine ⟨35581309477049049953031425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23720872984699366635354283 35581309477049049953031425)
          ·
            refine ⟨26685982107786787464773569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35581309477049049953031425 26685982107786787464773569)
            ·
              refine ⟨20014486580840090598580177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26685982107786787464773569 20014486580840090598580177)
              ·
                refine ⟨15010864935630067948935133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20014486580840090598580177 15010864935630067948935133)
                ·
                  refine ⟨5629074350861275480850675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15010864935630067948935133 5629074350861275480850675)
                  ·
                    refine ⟨8443611526291913221276013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629074350861275480850675 8443611526291913221276013)
                    ·
                      refine ⟨3166354322359467457978505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8443611526291913221276013 3166354322359467457978505)
                      ·
                        rfl

theorem cell23_6166453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_6166453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166453 prefixEnd_6166453 := by exact prefixLift 6166453
  have htrace : WordTrace (prefixWord ++ tailWord_6166453) baseStart_6166453 baseEnd_6166453 := by
    simpa [prefixWord, tailWord_6166453, baseEnd_6166453] using wordTrace_append hprefix tailTrace_6166453
  have hstable : (prefixWord ++ tailWord_6166453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166453).length < 2 ^ (prefixWord ++ tailWord_6166453).sum := by decide
  have hdescent : baseEnd_6166453 < baseStart_6166453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166456 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_6166456 : Nat := 118140960795 + 6166456 * 2 ^ 59
def prefixEnd_6166456 : Nat := 4983230072969 + 3 ^ 40 * 6166456 * 2
def baseEnd_6166456 : Nat := 1055451954267143648746997

theorem tailTrace_6166456 : CollatzResearch.WordTrace tailWord_6166456 prefixEnd_6166456 1055451954267143648746997 := by
  unfold tailWord_6166456
  simp only [CollatzResearch.WordTrace]
  refine ⟨112454563673995266842303611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149939418231993689123071481 112454563673995266842303611)
  ·
    refine ⟨168681845510992900263455417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112454563673995266842303611 168681845510992900263455417)
    ·
      refine ⟨126511384133244675197591563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168681845510992900263455417 126511384133244675197591563)
      ·
        refine ⟨189767076199867012796387345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126511384133244675197591563 189767076199867012796387345)
        ·
          refine ⟨142325307149900259597290509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189767076199867012796387345 142325307149900259597290509)
          ·
            refine ⟨53371990181212597348983941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142325307149900259597290509 53371990181212597348983941)
            ·
              refine ⟨10007248158977362002934489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53371990181212597348983941 10007248158977362002934489)
              ·
                refine ⟨7505436119233021502200867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10007248158977362002934489 7505436119233021502200867)
                ·
                  refine ⟨11258154178849532253301301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505436119233021502200867 11258154178849532253301301)
                  ·
                    refine ⟨1055451954267143648746997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11258154178849532253301301 1055451954267143648746997)
                    ·
                      rfl

theorem cell23_6166456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_6166456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166456 prefixEnd_6166456 := by exact prefixLift 6166456
  have htrace : WordTrace (prefixWord ++ tailWord_6166456) baseStart_6166456 baseEnd_6166456 := by
    simpa [prefixWord, tailWord_6166456, baseEnd_6166456] using wordTrace_append hprefix tailTrace_6166456
  have hstable : (prefixWord ++ tailWord_6166456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166456).length < 2 ^ (prefixWord ++ tailWord_6166456).sum := by decide
  have hdescent : baseEnd_6166456 < baseStart_6166456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166499 : List Nat := [1, 1, 1, 6, 1, 2, 1, 10]
def baseStart_6166499 : Nat := 118140960795 + 6166499 * 2 ^ 59
def prefixEnd_6166499 : Nat := 4983230072969 + 3 ^ 40 * 6166499 * 2
def baseEnd_6166499 : Nat := 117273257128502751037159

theorem tailTrace_6166499 : CollatzResearch.WordTrace tailWord_6166499 prefixEnd_6166499 117273257128502751037159 := by
  unfold tailWord_6166499
  simp only [CollatzResearch.WordTrace]
  refine ⟨224910695686834752028422551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149940463791223168018948367 224910695686834752028422551)
  ·
    refine ⟨337366043530252128042633827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224910695686834752028422551 337366043530252128042633827)
    ·
      refine ⟨506049065295378192063950741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337366043530252128042633827 506049065295378192063950741)
      ·
        refine ⟨23721049935720852752997691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 506049065295378192063950741 23721049935720852752997691)
        ·
          refine ⟨35581574903581279129496537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23721049935720852752997691 35581574903581279129496537)
          ·
            refine ⟨26686181177685959347122403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35581574903581279129496537 26686181177685959347122403)
            ·
              refine ⟨40029271766528939020683605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26686181177685959347122403 40029271766528939020683605)
              ·
                refine ⟨117273257128502751037159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40029271766528939020683605 117273257128502751037159)
                ·
                  rfl

theorem cell23_6166499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 10].length) (baseStart_6166499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166499 prefixEnd_6166499 := by exact prefixLift 6166499
  have htrace : WordTrace (prefixWord ++ tailWord_6166499) baseStart_6166499 baseEnd_6166499 := by
    simpa [prefixWord, tailWord_6166499, baseEnd_6166499] using wordTrace_append hprefix tailTrace_6166499
  have hstable : (prefixWord ++ tailWord_6166499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166499).length < 2 ^ (prefixWord ++ tailWord_6166499).sum := by decide
  have hdescent : baseEnd_6166499 < baseStart_6166499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166506 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6166506 : Nat := 118140960795 + 6166506 * 2 ^ 59
def prefixEnd_6166506 : Nat := 4983230072969 + 3 ^ 40 * 6166506 * 2
def baseEnd_6166506 : Nat := 3166381536834155750615761

theorem tailTrace_6166506 : CollatzResearch.WordTrace tailWord_6166506 prefixEnd_6166506 3166381536834155750615761 := by
  unfold tailWord_6166506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56227737749452348055981843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149940633998539594815951581 56227737749452348055981843)
  ·
    refine ⟨84341606624178522083972765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56227737749452348055981843 84341606624178522083972765)
    ·
      refine ⟨31628102484066945781489787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84341606624178522083972765 31628102484066945781489787)
      ·
        refine ⟨47442153726100418672234681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31628102484066945781489787 47442153726100418672234681)
        ·
          refine ⟨35581615294575314004176011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47442153726100418672234681 35581615294575314004176011)
          ·
            refine ⟨53372422941862971006264017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35581615294575314004176011 53372422941862971006264017)
            ·
              refine ⟨40029317206397228254698013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53372422941862971006264017 40029317206397228254698013)
              ·
                refine ⟨15010993952398960595511755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40029317206397228254698013 15010993952398960595511755)
                ·
                  refine ⟨22516490928598440893267633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15010993952398960595511755 22516490928598440893267633)
                  ·
                    refine ⟨16887368196448830669950725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22516490928598440893267633 16887368196448830669950725)
                    ·
                      refine ⟨3166381536834155750615761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16887368196448830669950725 3166381536834155750615761)
                      ·
                        rfl

theorem cell23_6166506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6166506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166506 prefixEnd_6166506 := by exact prefixLift 6166506
  have htrace : WordTrace (prefixWord ++ tailWord_6166506) baseStart_6166506 baseEnd_6166506 := by
    simpa [prefixWord, tailWord_6166506, baseEnd_6166506] using wordTrace_append hprefix tailTrace_6166506
  have hstable : (prefixWord ++ tailWord_6166506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166506).length < 2 ^ (prefixWord ++ tailWord_6166506).sum := by decide
  have hdescent : baseEnd_6166506 < baseStart_6166506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166510 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_6166510 : Nat := 118140960795 + 6166510 * 2 ^ 59
def prefixEnd_6166510 : Nat := 4983230072969 + 3 ^ 40 * 6166510 * 2
def baseEnd_6166510 : Nat := 3166383590756773734965743

theorem tailTrace_6166510 : CollatzResearch.WordTrace tailWord_6166510 prefixEnd_6166510 3166383590756773734965743 := by
  unfold tailWord_6166510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28113887111224362613384123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149940731259863267271381989 28113887111224362613384123)
  ·
    refine ⟨42170830666836543920076185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28113887111224362613384123 42170830666836543920076185)
    ·
      refine ⟨31628123000127407940057139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42170830666836543920076185 31628123000127407940057139)
      ·
        refine ⟨47442184500191111910085709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31628123000127407940057139 47442184500191111910085709)
        ·
          refine ⟨17790819187571666966282141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47442184500191111910085709 17790819187571666966282141)
          ·
            refine ⟨6671557195339375112355803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17790819187571666966282141 6671557195339375112355803)
            ·
              refine ⟨10007335793009062668533705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671557195339375112355803 10007335793009062668533705)
              ·
                refine ⟨7505501844756797001400279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10007335793009062668533705 7505501844756797001400279)
                ·
                  refine ⟨11258252767135195502100419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505501844756797001400279 11258252767135195502100419)
                  ·
                    refine ⟨16887379150702793253150629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11258252767135195502100419 16887379150702793253150629)
                    ·
                      refine ⟨3166383590756773734965743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16887379150702793253150629 3166383590756773734965743)
                      ·
                        rfl

theorem cell23_6166510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_6166510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166510 prefixEnd_6166510 := by exact prefixLift 6166510
  have htrace : WordTrace (prefixWord ++ tailWord_6166510) baseStart_6166510 baseEnd_6166510 := by
    simpa [prefixWord, tailWord_6166510, baseEnd_6166510] using wordTrace_append hprefix tailTrace_6166510
  have hstable : (prefixWord ++ tailWord_6166510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166510).length < 2 ^ (prefixWord ++ tailWord_6166510).sum := by decide
  have hdescent : baseEnd_6166510 < baseStart_6166510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166513 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_6166513 : Nat := 118140960795 + 6166513 * 2 ^ 59
def prefixEnd_6166513 : Nat := 4983230072969 + 3 ^ 40 * 6166513 * 2
def baseEnd_6166513 : Nat := 3166385131198737223228229

theorem tailTrace_6166513 : CollatzResearch.WordTrace tailWord_6166513 prefixEnd_6166513 3166385131198737223228229 := by
  unfold tailWord_6166513
  simp only [CollatzResearch.WordTrace]
  refine ⟨224911206308784032419432193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149940804205856021612954795 224911206308784032419432193)
  ·
    refine ⟨168683404731588024314574145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224911206308784032419432193 168683404731588024314574145)
    ·
      refine ⟨126512553548691018235930609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168683404731588024314574145 126512553548691018235930609)
      ·
        refine ⟨94884415161518263676947957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126512553548691018235930609 94884415161518263676947957)
        ·
          refine ⟨8895413921392337219713871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94884415161518263676947957 8895413921392337219713871)
          ·
            refine ⟨13343120882088505829570807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895413921392337219713871 13343120882088505829570807)
            ·
              refine ⟨20014681323132758744356211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343120882088505829570807 20014681323132758744356211)
              ·
                refine ⟨30022021984699138116534317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20014681323132758744356211 30022021984699138116534317)
                ·
                  refine ⟨11258258244262176793700369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30022021984699138116534317 11258258244262176793700369)
                  ·
                    refine ⟨8443693683196632595275277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11258258244262176793700369 8443693683196632595275277)
                    ·
                      refine ⟨3166385131198737223228229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8443693683196632595275277 3166385131198737223228229)
                      ·
                        rfl

theorem cell23_6166513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_6166513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166513 prefixEnd_6166513 := by exact prefixLift 6166513
  have htrace : WordTrace (prefixWord ++ tailWord_6166513) baseStart_6166513 baseEnd_6166513 := by
    simpa [prefixWord, tailWord_6166513, baseEnd_6166513] using wordTrace_append hprefix tailTrace_6166513
  have hstable : (prefixWord ++ tailWord_6166513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166513).length < 2 ^ (prefixWord ++ tailWord_6166513).sum := by decide
  have hdescent : baseEnd_6166513 < baseStart_6166513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166570 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6166570 : Nat := 118140960795 + 6166570 * 2 ^ 59
def prefixEnd_6166570 : Nat := 4983230072969 + 3 ^ 40 * 6166570 * 2
def baseEnd_6166570 : Nat := 3166414399596043500215467

theorem tailTrace_6166570 : CollatzResearch.WordTrace tailWord_6166570 prefixEnd_6166570 3166414399596043500215467 := by
  unfold tailWord_6166570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56228321317394382788564291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149942190179718354102838109 56228321317394382788564291)
  ·
    refine ⟨84342481976091574182846437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56228321317394382788564291 84342481976091574182846437)
    ·
      refine ⟨15814215370517170159283707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84342481976091574182846437 15814215370517170159283707)
      ·
        refine ⟨23721323055775755238925561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15814215370517170159283707 23721323055775755238925561)
        ·
          refine ⟨17790992291831816429194171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23721323055775755238925561 17790992291831816429194171)
          ·
            refine ⟨26686488437747724643791257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17790992291831816429194171 26686488437747724643791257)
            ·
              refine ⟨20014866328310793482843443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26686488437747724643791257 20014866328310793482843443)
              ·
                refine ⟨30022299492466190224265165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20014866328310793482843443 30022299492466190224265165)
                ·
                  refine ⟨11258362309674821334099437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30022299492466190224265165 11258362309674821334099437)
                  ·
                    refine ⟨4221885866128058000287289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11258362309674821334099437 4221885866128058000287289)
                    ·
                      refine ⟨3166414399596043500215467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221885866128058000287289 3166414399596043500215467)
                      ·
                        rfl

theorem cell23_6166570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6166570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166570 prefixEnd_6166570 := by exact prefixLift 6166570
  have htrace : WordTrace (prefixWord ++ tailWord_6166570) baseStart_6166570 baseEnd_6166570 := by
    simpa [prefixWord, tailWord_6166570, baseEnd_6166570] using wordTrace_append hprefix tailTrace_6166570
  have hstable : (prefixWord ++ tailWord_6166570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166570).length < 2 ^ (prefixWord ++ tailWord_6166570).sum := by decide
  have hdescent : baseEnd_6166570 < baseStart_6166570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166583 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_6166583 : Nat := 118140960795 + 6166583 * 2 ^ 59
def prefixEnd_6166583 : Nat := 4983230072969 + 3 ^ 40 * 6166583 * 2
def baseEnd_6166583 : Nat := 3166421074844551949352907

theorem tailTrace_6166583 : CollatzResearch.WordTrace tailWord_6166583 prefixEnd_6166583 3166421074844551949352907 := by
  unfold tailWord_6166583
  simp only [CollatzResearch.WordTrace]
  refine ⟨224913759418530434374480403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149942506279020289582986935 224913759418530434374480403)
  ·
    refine ⟨337370639127795651561720605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224913759418530434374480403 337370639127795651561720605)
    ·
      refine ⟨126513989672923369335645227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337370639127795651561720605 126513989672923369335645227)
      ·
        refine ⟨189770984509385054003467841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126513989672923369335645227 189770984509385054003467841)
        ·
          refine ⟨142328238382038790502600881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189770984509385054003467841 142328238382038790502600881)
          ·
            refine ⟨106746178786529092876950661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142328238382038790502600881 106746178786529092876950661)
            ·
              refine ⟨20014908522474204914428249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106746178786529092876950661 20014908522474204914428249)
              ·
                refine ⟨15011181391855653685821187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20014908522474204914428249 15011181391855653685821187)
                ·
                  refine ⟨22516772087783480528731781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15011181391855653685821187 22516772087783480528731781)
                  ·
                    refine ⟨4221894766459402599137209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22516772087783480528731781 4221894766459402599137209)
                    ·
                      refine ⟨3166421074844551949352907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221894766459402599137209 3166421074844551949352907)
                      ·
                        rfl

theorem cell23_6166583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_6166583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166583 prefixEnd_6166583 := by exact prefixLift 6166583
  have htrace : WordTrace (prefixWord ++ tailWord_6166583) baseStart_6166583 baseEnd_6166583 := by
    simpa [prefixWord, tailWord_6166583, baseEnd_6166583] using wordTrace_append hprefix tailTrace_6166583
  have hstable : (prefixWord ++ tailWord_6166583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166583).length < 2 ^ (prefixWord ++ tailWord_6166583).sum := by decide
  have hdescent : baseEnd_6166583 < baseStart_6166583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166600 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_6166600 : Nat := 118140960795 + 6166600 * 2 ^ 59
def prefixEnd_6166600 : Nat := 4983230072969 + 3 ^ 40 * 6166600 * 2
def baseEnd_6166600 : Nat := 3166429804015678382840329

theorem tailTrace_6166600 : CollatzResearch.WordTrace tailWord_6166600 prefixEnd_6166600 3166429804015678382840329 := by
  unfold tailWord_6166600
  simp only [CollatzResearch.WordTrace]
  refine ⟨112457189729734423138924627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149942919639645897518566169 112457189729734423138924627)
  ·
    refine ⟨168685784594601634708386941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112457189729734423138924627 168685784594601634708386941)
    ·
      refine ⟨63257169222975613015645103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168685784594601634708386941 63257169222975613015645103)
      ·
        refine ⟨94885753834463419523467655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63257169222975613015645103 94885753834463419523467655)
        ·
          refine ⟨142328630751695129285201483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94885753834463419523467655 142328630751695129285201483)
          ·
            refine ⟨213492946127542693927802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142328630751695129285201483 213492946127542693927802225)
            ·
              refine ⟨160119709595657020445851669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213492946127542693927802225 160119709595657020445851669)
              ·
                refine ⟨7505611387296422833399297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160119709595657020445851669 7505611387296422833399297)
                ·
                  refine ⟨5629208540472317125049473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505611387296422833399297 5629208540472317125049473)
                  ·
                    refine ⟨4221906405354237843787105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629208540472317125049473 4221906405354237843787105)
                    ·
                      refine ⟨3166429804015678382840329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221906405354237843787105 3166429804015678382840329)
                      ·
                        rfl

theorem cell23_6166600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_6166600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166600 prefixEnd_6166600 := by exact prefixLift 6166600
  have htrace : WordTrace (prefixWord ++ tailWord_6166600) baseStart_6166600 baseEnd_6166600 := by
    simpa [prefixWord, tailWord_6166600, baseEnd_6166600] using wordTrace_append hprefix tailTrace_6166600
  have hstable : (prefixWord ++ tailWord_6166600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166600).length < 2 ^ (prefixWord ++ tailWord_6166600).sum := by decide
  have hdescent : baseEnd_6166600 < baseStart_6166600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166606 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_6166606 : Nat := 118140960795 + 6166606 * 2 ^ 59
def prefixEnd_6166606 : Nat := 4983230072969 + 3 ^ 40 * 6166606 * 2
def baseEnd_6166606 : Nat := 351825876099956151040589

theorem tailTrace_6166606 : CollatzResearch.WordTrace tailWord_6166606 prefixEnd_6166606 351825876099956151040589 := by
  unfold tailWord_6166606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28114324787180888662820959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149943065531631406201711781 28114324787180888662820959)
  ·
    refine ⟨42171487180771332994231439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28114324787180888662820959 42171487180771332994231439)
    ·
      refine ⟨63257230771156999491347159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42171487180771332994231439 63257230771156999491347159)
      ·
        refine ⟨94885846156735499237020739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63257230771156999491347159 94885846156735499237020739)
        ·
          refine ⟨142328769235103248855531109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94885846156735499237020739 142328769235103248855531109)
          ·
            refine ⟨26686644231581859160412083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142328769235103248855531109 26686644231581859160412083)
            ·
              refine ⟨40029966347372788740618125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26686644231581859160412083 40029966347372788740618125)
              ·
                refine ⟨15011237380264795777731797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40029966347372788740618125 15011237380264795777731797)
                ·
                  refine ⟨351825876099956151040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15011237380264795777731797 351825876099956151040589)
                  ·
                    rfl

theorem cell23_6166606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_6166606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166606 prefixEnd_6166606 := by exact prefixLift 6166606
  have htrace : WordTrace (prefixWord ++ tailWord_6166606) baseStart_6166606 baseEnd_6166606 := by
    simpa [prefixWord, tailWord_6166606, baseEnd_6166606] using wordTrace_append hprefix tailTrace_6166606
  have hstable : (prefixWord ++ tailWord_6166606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166606).length < 2 ^ (prefixWord ++ tailWord_6166606).sum := by decide
  have hdescent : baseEnd_6166606 < baseStart_6166606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166617 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 2, 2, 2]
def baseStart_6166617 : Nat := 118140960795 + 6166617 * 2 ^ 59
def prefixEnd_6166617 : Nat := 4983230072969 + 3 ^ 40 * 6166617 * 2
def baseEnd_6166617 : Nat := 3166438533186804816327751

theorem tailTrace_6166617 : CollatzResearch.WordTrace tailWord_6166617 prefixEnd_6166617 3166438533186804816327751 := by
  unfold tailWord_6166617
  simp only [CollatzResearch.WordTrace]
  refine ⟨224914999500407258181218105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149943333000271505454145403 224914999500407258181218105)
  ·
    refine ⟨168686249625305443635913579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224914999500407258181218105 168686249625305443635913579)
    ·
      refine ⟨253029374437958165453870369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168686249625305443635913579 253029374437958165453870369)
      ·
        refine ⟨189772030828468624090402777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253029374437958165453870369 189772030828468624090402777)
        ·
          refine ⟨142329023121351468067802083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189772030828468624090402777 142329023121351468067802083)
          ·
            refine ⟨213493534682027202101703125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142329023121351468067802083 213493534682027202101703125)
            ·
              refine ⟨5003754719110012549258667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213493534682027202101703125 5003754719110012549258667)
              ·
                refine ⟨7505632078665018823888001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5003754719110012549258667 7505632078665018823888001)
                ·
                  refine ⟨5629224058998764117916001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505632078665018823888001 5629224058998764117916001)
                  ·
                    refine ⟨4221918044249073088437001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629224058998764117916001 4221918044249073088437001)
                    ·
                      refine ⟨3166438533186804816327751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4221918044249073088437001 3166438533186804816327751)
                      ·
                        rfl

theorem cell23_6166617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_6166617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166617 prefixEnd_6166617 := by exact prefixLift 6166617
  have htrace : WordTrace (prefixWord ++ tailWord_6166617) baseStart_6166617 baseEnd_6166617 := by
    simpa [prefixWord, tailWord_6166617, baseEnd_6166617] using wordTrace_append hprefix tailTrace_6166617
  have hstable : (prefixWord ++ tailWord_6166617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166617).length < 2 ^ (prefixWord ++ tailWord_6166617).sum := by decide
  have hdescent : baseEnd_6166617 < baseStart_6166617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166636 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_6166636 : Nat := 118140960795 + 6166636 * 2 ^ 59
def prefixEnd_6166636 : Nat := 4983230072969 + 3 ^ 40 * 6166636 * 2
def baseEnd_6166636 : Nat := 1055482763106413413996721

theorem tailTrace_6166636 : CollatzResearch.WordTrace tailWord_6166636 prefixEnd_6166636 1055482763106413413996721 := by
  unfold tailWord_6166636
  simp only [CollatzResearch.WordTrace]
  refine ⟨112457846243669212213079881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149943794991558949617439841 112457846243669212213079881)
  ·
    refine ⟨84343384682751909159809911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112457846243669212213079881 84343384682751909159809911)
    ·
      refine ⟨126515077024127863739714867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84343384682751909159809911 126515077024127863739714867)
      ·
        refine ⟨189772615536191795609572301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126515077024127863739714867 189772615536191795609572301)
        ·
          refine ⟨71164730826071923353589613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189772615536191795609572301 71164730826071923353589613)
          ·
            refine ⟨26686774059776971257596105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71164730826071923353589613 26686774059776971257596105)
            ·
              refine ⟨20015080544832728443197079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26686774059776971257596105 20015080544832728443197079)
              ·
                refine ⟨30022620817249092664795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20015080544832728443197079 30022620817249092664795619)
                ·
                  refine ⟨45033931225873638997193429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30022620817249092664795619 45033931225873638997193429)
                  ·
                    refine ⟨1055482763106413413996721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45033931225873638997193429 1055482763106413413996721)
                    ·
                      rfl

theorem cell23_6166636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_6166636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166636 prefixEnd_6166636 := by exact prefixLift 6166636
  have htrace : WordTrace (prefixWord ++ tailWord_6166636) baseStart_6166636 baseEnd_6166636 := by
    simpa [prefixWord, tailWord_6166636, baseEnd_6166636] using wordTrace_append hprefix tailTrace_6166636
  have hstable : (prefixWord ++ tailWord_6166636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166636).length < 2 ^ (prefixWord ++ tailWord_6166636).sum := by decide
  have hdescent : baseEnd_6166636 < baseStart_6166636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166640 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 5]
def baseStart_6166640 : Nat := 118140960795 + 6166640 * 2 ^ 59
def prefixEnd_6166640 : Nat := 4983230072969 + 3 ^ 40 * 6166640 * 2
def baseEnd_6166640 : Nat := 351827815915762025148905

theorem tailTrace_6166640 : CollatzResearch.WordTrace tailWord_6166640 prefixEnd_6166640 351827815915762025148905 := by
  unfold tailWord_6166640
  simp only [CollatzResearch.WordTrace]
  refine ⟨112457919189661966554652687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149943892252882622072870249 112457919189661966554652687)
  ·
    refine ⟨168686878784492949831979031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112457919189661966554652687 168686878784492949831979031)
    ·
      refine ⟨253030318176739424747968547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168686878784492949831979031 253030318176739424747968547)
      ·
        refine ⟨379545477265109137121952821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253030318176739424747968547 379545477265109137121952821)
        ·
          refine ⟨35582388493603981605183077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379545477265109137121952821 35582388493603981605183077)
          ·
            refine ⟨6671697842550746550971827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35582388493603981605183077 6671697842550746550971827)
            ·
              refine ⟨10007546763826119826457741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6671697842550746550971827 10007546763826119826457741)
              ·
                refine ⟨3752830036434794934921653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10007546763826119826457741 3752830036434794934921653)
                ·
                  refine ⟨351827815915762025148905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752830036434794934921653 351827815915762025148905)
                  ·
                    rfl

theorem cell23_6166640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 5].length) (baseStart_6166640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166640 prefixEnd_6166640 := by exact prefixLift 6166640
  have htrace : WordTrace (prefixWord ++ tailWord_6166640) baseStart_6166640 baseEnd_6166640 := by
    simpa [prefixWord, tailWord_6166640, baseEnd_6166640] using wordTrace_append hprefix tailTrace_6166640
  have hstable : (prefixWord ++ tailWord_6166640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166640).length < 2 ^ (prefixWord ++ tailWord_6166640).sum := by decide
  have hdescent : baseEnd_6166640 < baseStart_6166640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166653 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_6166653 : Nat := 118140960795 + 6166653 * 2 ^ 59
def prefixEnd_6166653 : Nat := 4983230072969 + 3 ^ 40 * 6166653 * 2
def baseEnd_6166653 : Nat := 1055485672830122225159195

theorem tailTrace_6166653 : CollatzResearch.WordTrace tailWord_6166653 prefixEnd_6166653 1055485672830122225159195 := by
  unfold tailWord_6166653
  simp only [CollatzResearch.WordTrace]
  refine ⟨224916312528276836329528613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149944208352184557553019075 224916312528276836329528613)
  ·
    refine ⟨42171808599051906811786615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224916312528276836329528613 42171808599051906811786615)
    ·
      refine ⟨63257712898577860217679923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42171808599051906811786615 63257712898577860217679923)
      ·
        refine ⟨94886569347866790326519885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63257712898577860217679923 94886569347866790326519885)
        ·
          refine ⟨35582463505450046372444957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94886569347866790326519885 35582463505450046372444957)
          ·
            refine ⟨13343423814543767389666859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35582463505450046372444957 13343423814543767389666859)
            ·
              refine ⟨20015135721815651084500289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343423814543767389666859 20015135721815651084500289)
              ·
                refine ⟨15011351791361738313375217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20015135721815651084500289 15011351791361738313375217)
                ·
                  refine ⟨11258513843521303735031413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15011351791361738313375217 11258513843521303735031413)
                  ·
                    refine ⟨1055485672830122225159195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11258513843521303735031413 1055485672830122225159195)
                    ·
                      rfl

theorem cell23_6166653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_6166653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166653 prefixEnd_6166653 := by exact prefixLift 6166653
  have htrace : WordTrace (prefixWord ++ tailWord_6166653) baseStart_6166653 baseEnd_6166653 := by
    simpa [prefixWord, tailWord_6166653, baseEnd_6166653] using wordTrace_append hprefix tailTrace_6166653
  have hstable : (prefixWord ++ tailWord_6166653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166653).length < 2 ^ (prefixWord ++ tailWord_6166653).sum := by decide
  have hdescent : baseEnd_6166653 < baseStart_6166653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166657 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 5]
def baseStart_6166657 : Nat := 118140960795 + 6166657 * 2 ^ 59
def prefixEnd_6166657 : Nat := 4983230072969 + 3 ^ 40 * 6166657 * 2
def baseEnd_6166657 : Nat := 351828785823664962203063

theorem tailTrace_6166657 : CollatzResearch.WordTrace tailWord_6166657 prefixEnd_6166657 351828785823664962203063 := by
  unfold tailWord_6166657
  simp only [CollatzResearch.WordTrace]
  refine ⟨224916458420262345012674225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149944305613508230008449483 224916458420262345012674225)
  ·
    refine ⟨168687343815196758759505669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224916458420262345012674225 168687343815196758759505669)
    ·
      refine ⟨31628876965349392267407313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168687343815196758759505669 31628876965349392267407313)
      ·
        refine ⟨23721657724012044200555485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31628876965349392267407313 23721657724012044200555485)
        ·
          refine ⟨8895621646504516575208307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23721657724012044200555485 8895621646504516575208307)
          ·
            refine ⟨13343432469756774862812461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8895621646504516575208307 13343432469756774862812461)
            ·
              refine ⟨5003787176158790573554673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13343432469756774862812461 5003787176158790573554673)
              ·
                refine ⟨3752840382119092930166005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003787176158790573554673 3752840382119092930166005)
                ·
                  refine ⟨351828785823664962203063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752840382119092930166005 351828785823664962203063)
                  ·
                    rfl

theorem cell23_6166657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 5].length) (baseStart_6166657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166657 prefixEnd_6166657 := by exact prefixLift 6166657
  have htrace : WordTrace (prefixWord ++ tailWord_6166657) baseStart_6166657 baseEnd_6166657 := by
    simpa [prefixWord, tailWord_6166657, baseEnd_6166657] using wordTrace_append hprefix tailTrace_6166657
  have hstable : (prefixWord ++ tailWord_6166657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166657).length < 2 ^ (prefixWord ++ tailWord_6166657).sum := by decide
  have hdescent : baseEnd_6166657 < baseStart_6166657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166690 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6166690 : Nat := 118140960795 + 6166690 * 2 ^ 59
def prefixEnd_6166690 : Nat := 4983230072969 + 3 ^ 40 * 6166690 * 2
def baseEnd_6166690 : Nat := 3166476017274583030714915

theorem tailTrace_6166690 : CollatzResearch.WordTrace tailWord_6166690 prefixEnd_6166690 3166476017274583030714915 := by
  unfold tailWord_6166690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56229415507285697912156381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149945108019428527765750349 56229415507285697912156381)
  ·
    refine ⟨21086030815232136717058643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56229415507285697912156381 21086030815232136717058643)
    ·
      refine ⟨31629046222848205075587965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086030815232136717058643 31629046222848205075587965)
      ·
        refine ⟨11860892333568076903345487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31629046222848205075587965 11860892333568076903345487)
        ·
          refine ⟨17791338500352115355018231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11860892333568076903345487 17791338500352115355018231)
          ·
            refine ⟨26687007750528173032527347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17791338500352115355018231 26687007750528173032527347)
            ·
              refine ⟨40030511625792259548791021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26687007750528173032527347 40030511625792259548791021)
              ·
                refine ⟨15011441859672097330796633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40030511625792259548791021 15011441859672097330796633)
                ·
                  refine ⟨11258581394754072998097475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15011441859672097330796633 11258581394754072998097475)
                  ·
                    refine ⟨16887872092131109497146213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11258581394754072998097475 16887872092131109497146213)
                    ·
                      refine ⟨3166476017274583030714915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16887872092131109497146213 3166476017274583030714915)
                      ·
                        rfl

theorem cell23_6166690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6166690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166690 prefixEnd_6166690 := by exact prefixLift 6166690
  have htrace : WordTrace (prefixWord ++ tailWord_6166690) baseStart_6166690 baseEnd_6166690 := by
    simpa [prefixWord, tailWord_6166690, baseEnd_6166690] using wordTrace_append hprefix tailTrace_6166690
  have hstable : (prefixWord ++ tailWord_6166690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166690).length < 2 ^ (prefixWord ++ tailWord_6166690).sum := by decide
  have hdescent : baseEnd_6166690 < baseStart_6166690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166708 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 5]
def baseStart_6166708 : Nat := 118140960795 + 6166708 * 2 ^ 59
def prefixEnd_6166708 : Nat := 4983230072969 + 3 ^ 40 * 6166708 * 2
def baseEnd_6166708 : Nat := 351831695547373773365537

theorem tailTrace_6166708 : CollatzResearch.WordTrace tailWord_6166708 prefixEnd_6166708 351831695547373773365537 := by
  unfold tailWord_6166708
  simp only [CollatzResearch.WordTrace]
  refine ⟨112459159271538790361390389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149945545695385053815187185 112459159271538790361390389)
  ·
    refine ⟨10543046181706761596380349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112459159271538790361390389 10543046181706761596380349)
    ·
      refine ⟨3953642318140035598642631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10543046181706761596380349 3953642318140035598642631)
      ·
        refine ⟨5930463477210053397963947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953642318140035598642631 5930463477210053397963947)
        ·
          refine ⟨8895695215815080096945921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930463477210053397963947 8895695215815080096945921)
          ·
            refine ⟨6671771411861310072709441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8895695215815080096945921 6671771411861310072709441)
            ·
              refine ⟨5003828558895982554532081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6671771411861310072709441 5003828558895982554532081)
              ·
                refine ⟨3752871419171986915899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5003828558895982554532081 3752871419171986915899061)
                ·
                  refine ⟨351831695547373773365537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3752871419171986915899061 351831695547373773365537)
                  ·
                    rfl

theorem cell23_6166708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_6166708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166708 prefixEnd_6166708 := by exact prefixLift 6166708
  have htrace : WordTrace (prefixWord ++ tailWord_6166708) baseStart_6166708 baseEnd_6166708 := by
    simpa [prefixWord, tailWord_6166708, baseEnd_6166708] using wordTrace_append hprefix tailTrace_6166708
  have hstable : (prefixWord ++ tailWord_6166708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166708).length < 2 ^ (prefixWord ++ tailWord_6166708).sum := by decide
  have hdescent : baseEnd_6166708 < baseStart_6166708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166713 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 6]
def baseStart_6166713 : Nat := 118140960795 + 6166713 * 2 ^ 59
def prefixEnd_6166713 : Nat := 4983230072969 + 3 ^ 40 * 6166713 * 2
def baseEnd_6166713 : Nat := 351831980814404048969701

theorem tailTrace_6166713 : CollatzResearch.WordTrace tailWord_6166713 prefixEnd_6166713 351831980814404048969701 := by
  unfold tailWord_6166713
  simp only [CollatzResearch.WordTrace]
  refine ⟨224918500908059466576712793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149945667272039644384475195 224918500908059466576712793)
  ·
    refine ⟨168688875681044599932534595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224918500908059466576712793 168688875681044599932534595)
    ·
      refine ⟨253033313521566899898801893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168688875681044599932534595 253033313521566899898801893)
      ·
        refine ⟨47443746285293793731025355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253033313521566899898801893 47443746285293793731025355)
        ·
          refine ⟨71165619427940690596538033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47443746285293793731025355 71165619427940690596538033)
          ·
            refine ⟨53374214570955517947403525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71165619427940690596538033 53374214570955517947403525)
            ·
              refine ⟨10007665232054159615138161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53374214570955517947403525 10007665232054159615138161)
              ·
                refine ⟨7505748924040619711353621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10007665232054159615138161 7505748924040619711353621)
                ·
                  refine ⟨351831980814404048969701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7505748924040619711353621 351831980814404048969701)
                  ·
                    rfl

theorem cell23_6166713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_6166713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166713 prefixEnd_6166713 := by exact prefixLift 6166713
  have htrace : WordTrace (prefixWord ++ tailWord_6166713) baseStart_6166713 baseEnd_6166713 := by
    simpa [prefixWord, tailWord_6166713, baseEnd_6166713] using wordTrace_append hprefix tailTrace_6166713
  have hstable : (prefixWord ++ tailWord_6166713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166713).length < 2 ^ (prefixWord ++ tailWord_6166713).sum := by decide
  have hdescent : baseEnd_6166713 < baseStart_6166713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166743 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 1, 5]
def baseStart_6166743 : Nat := 118140960795 + 6166743 * 2 ^ 59
def prefixEnd_6166743 : Nat := 4983230072969 + 3 ^ 40 * 6166743 * 2
def baseEnd_6166743 : Nat := 1055501077249757107784057

theorem tailTrace_6166743 : CollatzResearch.WordTrace tailWord_6166743 prefixEnd_6166743 1055501077249757107784057 := by
  unfold tailWord_6166743
  simp only [CollatzResearch.WordTrace]
  refine ⟨224919595097950781700304883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149946396731967187800203255 224919595097950781700304883)
  ·
    refine ⟨337379392646926172550457325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224919595097950781700304883 337379392646926172550457325)
    ·
      refine ⟨126517272242597314706421497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337379392646926172550457325 126517272242597314706421497)
      ·
        refine ⟨94887954181947986029816123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126517272242597314706421497 94887954181947986029816123)
        ·
          refine ⟨142331931272921979044724185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94887954181947986029816123 142331931272921979044724185)
          ·
            refine ⟨106748948454691484283543139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142331931272921979044724185 106748948454691484283543139)
            ·
              refine ⟨160123422682037226425314709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106748948454691484283543139 160123422682037226425314709)
              ·
                refine ⟨7505785438220494988686627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160123422682037226425314709 7505785438220494988686627)
                ·
                  refine ⟨11258678157330742483029941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505785438220494988686627 11258678157330742483029941)
                  ·
                    refine ⟨1055501077249757107784057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11258678157330742483029941 1055501077249757107784057)
                    ·
                      rfl

theorem cell23_6166743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_6166743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166743 prefixEnd_6166743 := by exact prefixLift 6166743
  have htrace : WordTrace (prefixWord ++ tailWord_6166743) baseStart_6166743 baseEnd_6166743 := by
    simpa [prefixWord, tailWord_6166743, baseEnd_6166743] using wordTrace_append hprefix tailTrace_6166743
  have hstable : (prefixWord ++ tailWord_6166743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166743).length < 2 ^ (prefixWord ++ tailWord_6166743).sum := by decide
  have hdescent : baseEnd_6166743 < baseStart_6166743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166760 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6166760 : Nat := 118140960795 + 6166760 * 2 ^ 59
def prefixEnd_6166760 : Nat := 4983230072969 + 3 ^ 40 * 6166760 * 2
def baseEnd_6166760 : Nat := 1055503986973465918946531

theorem tailTrace_6166760 : CollatzResearch.WordTrace tailWord_6166760 prefixEnd_6166760 1055503986973465918946531 := by
  unfold tailWord_6166760
  simp only [CollatzResearch.WordTrace]
  refine ⟨112460107569444596801836867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149946810092592795735782489 112460107569444596801836867)
  ·
    refine ⟨168690161354166895202755301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112460107569444596801836867 168690161354166895202755301)
    ·
      refine ⟨31629405253906292850516619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168690161354166895202755301 31629405253906292850516619)
      ·
        refine ⟨47444107880859439275774929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31629405253906292850516619 47444107880859439275774929)
        ·
          refine ⟨35583080910644579456831197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47444107880859439275774929 35583080910644579456831197)
          ·
            refine ⟨13343655341491717296311699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35583080910644579456831197 13343655341491717296311699)
            ·
              refine ⟨20015483012237575944467549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343655341491717296311699 20015483012237575944467549)
              ·
                refine ⟨7505806129589090979175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20015483012237575944467549 7505806129589090979175331)
                ·
                  refine ⟨11258709194383636468762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505806129589090979175331 11258709194383636468762997)
                  ·
                    refine ⟨1055503986973465918946531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11258709194383636468762997 1055503986973465918946531)
                    ·
                      rfl

theorem cell23_6166760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6166760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166760 prefixEnd_6166760 := by exact prefixLift 6166760
  have htrace : WordTrace (prefixWord ++ tailWord_6166760) baseStart_6166760 baseEnd_6166760 := by
    simpa [prefixWord, tailWord_6166760, baseEnd_6166760] using wordTrace_append hprefix tailTrace_6166760
  have hstable : (prefixWord ++ tailWord_6166760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166760).length < 2 ^ (prefixWord ++ tailWord_6166760).sum := by decide
  have hdescent : baseEnd_6166760 < baseStart_6166760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166774 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6166774 : Nat := 118140960795 + 6166774 * 2 ^ 59
def prefixEnd_6166774 : Nat := 4983230072969 + 3 ^ 40 * 6166774 * 2
def baseEnd_6166774 : Nat := 3166519149649560702064529

theorem tailTrace_6166774 : CollatzResearch.WordTrace tailWord_6166774 prefixEnd_6166774 3166519149649560702064529 := by
  unfold tailWord_6166774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057545360052404624667711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149947150507225649329788917 14057545360052404624667711)
  ·
    refine ⟨21086318040078606937001567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14057545360052404624667711 21086318040078606937001567)
    ·
      refine ⟨31629477060117910405502351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086318040078606937001567 31629477060117910405502351)
      ·
        refine ⟨47444215590176865608253527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31629477060117910405502351 47444215590176865608253527)
        ·
          refine ⟨71166323385265298412380291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47444215590176865608253527 71166323385265298412380291)
          ·
            refine ⟨106749485077897947618570437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71166323385265298412380291 106749485077897947618570437)
            ·
              refine ⟨20015528452105865178481957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106749485077897947618570437 20015528452105865178481957)
              ·
                refine ⟨3752911584769849720965367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20015528452105865178481957 3752911584769849720965367)
                ·
                  refine ⟨5629367377154774581448051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752911584769849720965367 5629367377154774581448051)
                  ·
                    refine ⟨8444051065732161872172077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629367377154774581448051 8444051065732161872172077)
                    ·
                      refine ⟨3166519149649560702064529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444051065732161872172077 3166519149649560702064529)
                      ·
                        rfl

theorem cell23_6166774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6166774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166774 prefixEnd_6166774 := by exact prefixLift 6166774
  have htrace : WordTrace (prefixWord ++ tailWord_6166774) baseStart_6166774 baseEnd_6166774 := by
    simpa [prefixWord, tailWord_6166774, baseEnd_6166774] using wordTrace_append hprefix tailTrace_6166774
  have hstable : (prefixWord ++ tailWord_6166774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166774).length < 2 ^ (prefixWord ++ tailWord_6166774).sum := by decide
  have hdescent : baseEnd_6166774 < baseStart_6166774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166783 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_6166783 : Nat := 118140960795 + 6166783 * 2 ^ 59
def prefixEnd_6166783 : Nat := 4983230072969 + 3 ^ 40 * 6166783 * 2
def baseEnd_6166783 : Nat := 3166523770975451166851987

theorem tailTrace_6166783 : CollatzResearch.WordTrace tailWord_6166783 prefixEnd_6166783 3166523770975451166851987 := by
  unfold tailWord_6166783
  simp only [CollatzResearch.WordTrace]
  refine ⟨224921054017805868531761003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149947369345203912354507335 224921054017805868531761003)
  ·
    refine ⟨337381581026708802797641505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224921054017805868531761003 337381581026708802797641505)
    ·
      refine ⟨253036185770031602098231129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337381581026708802797641505 253036185770031602098231129)
      ·
        refine ⟨189777139327523701573673347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253036185770031602098231129 189777139327523701573673347)
        ·
          refine ⟨284665708991285552360510021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189777139327523701573673347 284665708991285552360510021)
          ·
            refine ⟨53374820435866041067595629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284665708991285552360510021 53374820435866041067595629)
            ·
              refine ⟨20015557663449765400348361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53374820435866041067595629 20015557663449765400348361)
              ·
                refine ⟨15011668247587324050261271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20015557663449765400348361 15011668247587324050261271)
                ·
                  refine ⟨22517502371380986075391907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15011668247587324050261271 22517502371380986075391907)
                  ·
                    refine ⟨33776253557071479113087861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22517502371380986075391907 33776253557071479113087861)
                    ·
                      refine ⟨3166523770975451166851987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33776253557071479113087861 3166523770975451166851987)
                      ·
                        rfl

theorem cell23_6166783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_6166783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166783 prefixEnd_6166783 := by exact prefixLift 6166783
  have htrace : WordTrace (prefixWord ++ tailWord_6166783) baseStart_6166783 baseEnd_6166783 := by
    simpa [prefixWord, tailWord_6166783, baseEnd_6166783] using wordTrace_append hprefix tailTrace_6166783
  have hstable : (prefixWord ++ tailWord_6166783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166783).length < 2 ^ (prefixWord ++ tailWord_6166783).sum := by decide
  have hdescent : baseEnd_6166783 < baseStart_6166783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166793 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_6166793 : Nat := 118140960795 + 6166793 * 2 ^ 59
def prefixEnd_6166793 : Nat := 4983230072969 + 3 ^ 40 * 6166793 * 2
def baseEnd_6166793 : Nat := 3166528905781996127726941

theorem tailTrace_6166793 : CollatzResearch.WordTrace tailWord_6166793 prefixEnd_6166793 3166528905781996127726941 := by
  unfold tailWord_6166793
  simp only [CollatzResearch.WordTrace]
  refine ⟨224921418747769640239625033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149947612498513093493083355 224921418747769640239625033)
  ·
    refine ⟨168691064060827230179718775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224921418747769640239625033 168691064060827230179718775)
    ·
      refine ⟨253036596091240845269578163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168691064060827230179718775 253036596091240845269578163)
      ·
        refine ⟨379554894136861267904367245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253036596091240845269578163 379554894136861267904367245)
        ·
          refine ⟨142333085301322975464137717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379554894136861267904367245 142333085301322975464137717)
          ·
            refine ⟨13343726746999028949762911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142333085301322975464137717 13343726746999028949762911)
            ·
              refine ⟨20015590120498543424644367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13343726746999028949762911 20015590120498543424644367)
              ·
                refine ⟨30023385180747815136966551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20015590120498543424644367 30023385180747815136966551)
                ·
                  refine ⟨45035077771121722705449827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30023385180747815136966551 45035077771121722705449827)
                  ·
                    refine ⟨67552616656682584058174741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45035077771121722705449827 67552616656682584058174741)
                    ·
                      refine ⟨3166528905781996127726941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67552616656682584058174741 3166528905781996127726941)
                      ·
                        rfl

theorem cell23_6166793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_6166793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166793 prefixEnd_6166793 := by exact prefixLift 6166793
  have htrace : WordTrace (prefixWord ++ tailWord_6166793) baseStart_6166793 baseEnd_6166793 := by
    simpa [prefixWord, tailWord_6166793, baseEnd_6166793] using wordTrace_append hprefix tailTrace_6166793
  have hstable : (prefixWord ++ tailWord_6166793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166793).length < 2 ^ (prefixWord ++ tailWord_6166793).sum := by decide
  have hdescent : baseEnd_6166793 < baseStart_6166793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166814 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6166814 : Nat := 118140960795 + 6166814 * 2 ^ 59
def prefixEnd_6166814 : Nat := 4983230072969 + 3 ^ 40 * 6166814 * 2
def baseEnd_6166814 : Nat := 3166539688875740545564345

theorem tailTrace_6166814 : CollatzResearch.WordTrace tailWord_6166814 prefixEnd_6166814 3166539688875740545564345 := by
  unfold tailWord_6166814
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115273085086695103267437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149948123120462373884092997 28115273085086695103267437)
  ·
    refine ⟨10543227406907510663725289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28115273085086695103267437 10543227406907510663725289)
    ·
      refine ⟨7907420555180632997793967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10543227406907510663725289 7907420555180632997793967)
      ·
        refine ⟨11861130832770949496690951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7907420555180632997793967 11861130832770949496690951)
        ·
          refine ⟨17791696249156424245036427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861130832770949496690951 17791696249156424245036427)
          ·
            refine ⟨26687544373734636367554641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17791696249156424245036427 26687544373734636367554641)
            ·
              refine ⟨20015658280300977275665981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26687544373734636367554641 20015658280300977275665981)
              ·
                refine ⟨7505871855112866478374743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20015658280300977275665981 7505871855112866478374743)
                ·
                  refine ⟨11258807782669299717562115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7505871855112866478374743 11258807782669299717562115)
                  ·
                    refine ⟨16888211674003949576343173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11258807782669299717562115 16888211674003949576343173)
                    ·
                      refine ⟨3166539688875740545564345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16888211674003949576343173 3166539688875740545564345)
                      ·
                        rfl

theorem cell23_6166814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6166814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166814 prefixEnd_6166814 := by exact prefixLift 6166814
  have htrace : WordTrace (prefixWord ++ tailWord_6166814) baseStart_6166814 baseEnd_6166814 := by
    simpa [prefixWord, tailWord_6166814, baseEnd_6166814] using wordTrace_append hprefix tailTrace_6166814
  have hstable : (prefixWord ++ tailWord_6166814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166814).length < 2 ^ (prefixWord ++ tailWord_6166814).sum := by decide
  have hdescent : baseEnd_6166814 < baseStart_6166814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166847 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_6166847 : Nat := 118140960795 + 6166847 * 2 ^ 59
def prefixEnd_6166847 : Nat := 4983230072969 + 3 ^ 40 * 6166847 * 2
def baseEnd_6166847 : Nat := 3166556633737338916451693

theorem tailTrace_6166847 : CollatzResearch.WordTrace tailWord_6166847 prefixEnd_6166847 3166556633737338916451693 := by
  unfold tailWord_6166847
  simp only [CollatzResearch.WordTrace]
  refine ⟨224923388289574007462090795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149948925526382671641393863 224923388289574007462090795)
  ·
    refine ⟨337385082434361011193136193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224923388289574007462090795 337385082434361011193136193)
    ·
      refine ⟨253038811825770758394852145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337385082434361011193136193 253038811825770758394852145)
      ·
        refine ⟨189779108869328068796139109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253038811825770758394852145 189779108869328068796139109)
        ·
          refine ⟨35583582912999012899276083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189779108869328068796139109 35583582912999012899276083)
          ·
            refine ⟨53375374369498519348914125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35583582912999012899276083 53375374369498519348914125)
            ·
              refine ⟨20015765388561944755842797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53375374369498519348914125 20015765388561944755842797)
              ·
                refine ⟨7505912020710729283441049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20015765388561944755842797 7505912020710729283441049)
                ·
                  refine ⟨5629434015533046962580787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7505912020710729283441049 5629434015533046962580787)
                  ·
                    refine ⟨8444151023299570443871181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629434015533046962580787 8444151023299570443871181)
                    ·
                      refine ⟨3166556633737338916451693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444151023299570443871181 3166556633737338916451693)
                      ·
                        rfl

theorem cell23_6166847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_6166847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166847 prefixEnd_6166847 := by exact prefixLift 6166847
  have htrace : WordTrace (prefixWord ++ tailWord_6166847) baseStart_6166847 baseEnd_6166847 := by
    simpa [prefixWord, tailWord_6166847, baseEnd_6166847] using wordTrace_append hprefix tailTrace_6166847
  have hstable : (prefixWord ++ tailWord_6166847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166847).length < 2 ^ (prefixWord ++ tailWord_6166847).sum := by decide
  have hdescent : baseEnd_6166847 < baseStart_6166847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166920 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_6166920 : Nat := 118140960795 + 6166920 * 2 ^ 59
def prefixEnd_6166920 : Nat := 4983230072969 + 3 ^ 40 * 6166920 * 2
def baseEnd_6166920 : Nat := 3166594117825117130838857

theorem tailTrace_6166920 : CollatzResearch.WordTrace tailWord_6166920 prefixEnd_6166920 3166594117825117130838857 := by
  unfold tailWord_6166920
  simp only [CollatzResearch.WordTrace]
  refine ⟨112463025409154770464749107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149950700545539693952998809 112463025409154770464749107)
  ·
    refine ⟨168694538113732155697123661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112463025409154770464749107 168694538113732155697123661)
    ·
      refine ⟨63260451792649558386421373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168694538113732155697123661 63260451792649558386421373)
      ·
        refine ⟨23722669422243584394908015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63260451792649558386421373 23722669422243584394908015)
        ·
          refine ⟨35584004133365376592362023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23722669422243584394908015 35584004133365376592362023)
          ·
            refine ⟨53376006200048064888543035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35584004133365376592362023 53376006200048064888543035)
            ·
              refine ⟨80064009300072097332814553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53376006200048064888543035 80064009300072097332814553)
              ·
                refine ⟨60048006975054072999610915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80064009300072097332814553 60048006975054072999610915)
                ·
                  refine ⟨90072010462581109499416373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60048006975054072999610915 90072010462581109499416373)
                  ·
                    refine ⟨8444250980866979015570285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90072010462581109499416373 8444250980866979015570285)
                    ·
                      refine ⟨3166594117825117130838857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444250980866979015570285 3166594117825117130838857)
                      ·
                        rfl

theorem cell23_6166920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_6166920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166920 prefixEnd_6166920 := by exact prefixLift 6166920
  have htrace : WordTrace (prefixWord ++ tailWord_6166920) baseStart_6166920 baseEnd_6166920 := by
    simpa [prefixWord, tailWord_6166920, baseEnd_6166920] using wordTrace_append hprefix tailTrace_6166920
  have hstable : (prefixWord ++ tailWord_6166920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166920).length < 2 ^ (prefixWord ++ tailWord_6166920).sum := by decide
  have hdescent : baseEnd_6166920 < baseStart_6166920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6166997 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6166997 : Nat := 118140960795 + 6166997 * 2 ^ 59
def prefixEnd_6166997 : Nat := 4983230072969 + 3 ^ 40 * 6166997 * 2
def baseEnd_6166997 : Nat := 3166633655835513329576003

theorem tailTrace_6166997 : CollatzResearch.WordTrace tailWord_6166997 prefixEnd_6166997 3166633655835513329576003 := by
  unfold tailWord_6166997
  simp only [CollatzResearch.WordTrace]
  refine ⟨224928859239030583080051245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149952572826020388720034163 224928859239030583080051245)
  ·
    refine ⟨84348322214636468655019217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224928859239030583080051245 84348322214636468655019217)
    ·
      refine ⟨63261241660977351491264413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84348322214636468655019217 63261241660977351491264413)
      ·
        refine ⟨23722965622866506809224155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63261241660977351491264413 23722965622866506809224155)
        ·
          refine ⟨35584448434299760213836233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23722965622866506809224155 35584448434299760213836233)
          ·
            refine ⟨26688336325724820160377175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35584448434299760213836233 26688336325724820160377175)
            ·
              refine ⟨40032504488587230240565763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26688336325724820160377175 40032504488587230240565763)
              ·
                refine ⟨60048756732880845360848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40032504488587230240565763 60048756732880845360848645)
                ·
                  refine ⟨11259141887415158505159121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60048756732880845360848645 11259141887415158505159121)
                  ·
                    refine ⟨8444356415561368878869341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11259141887415158505159121 8444356415561368878869341)
                    ·
                      refine ⟨3166633655835513329576003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444356415561368878869341 3166633655835513329576003)
                      ·
                        rfl

theorem cell23_6166997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6166997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6166997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6166997 prefixEnd_6166997 := by exact prefixLift 6166997
  have htrace : WordTrace (prefixWord ++ tailWord_6166997) baseStart_6166997 baseEnd_6166997 := by
    simpa [prefixWord, tailWord_6166997, baseEnd_6166997] using wordTrace_append hprefix tailTrace_6166997
  have hstable : (prefixWord ++ tailWord_6166997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6166997).length < 2 ^ (prefixWord ++ tailWord_6166997).sum := by decide
  have hdescent : baseEnd_6166997 < baseStart_6166997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6166997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167000 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 6]
def baseStart_6167000 : Nat := 118140960795 + 6167000 * 2 ^ 59
def prefixEnd_6167000 : Nat := 4983230072969 + 3 ^ 40 * 6167000 * 2
def baseEnd_6167000 : Nat := 351848355141941868648721

theorem tailTrace_6167000 : CollatzResearch.WordTrace tailWord_6167000 prefixEnd_6167000 351848355141941868648721 := by
  unfold tailWord_6167000
  simp only [CollatzResearch.WordTrace]
  refine ⟨112464484329009857296205227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149952645772013143061606969 112464484329009857296205227)
  ·
    refine ⟨168696726493514785944307841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112464484329009857296205227 168696726493514785944307841)
    ·
      refine ⟨126522544870136089458230881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168696726493514785944307841 126522544870136089458230881)
      ·
        refine ⟨94891908652602067093673161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126522544870136089458230881 94891908652602067093673161)
        ·
          refine ⟨71168931489451550320254871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94891908652602067093673161 71168931489451550320254871)
          ·
            refine ⟨106753397234177325480382307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71168931489451550320254871 106753397234177325480382307)
            ·
              refine ⟨160130095851265988220573461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106753397234177325480382307 160130095851265988220573461)
              ·
                refine ⟨7506098243028093197839381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160130095851265988220573461 7506098243028093197839381)
                ·
                  refine ⟨351848355141941868648721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7506098243028093197839381 351848355141941868648721)
                  ·
                    rfl

theorem cell23_6167000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_6167000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167000 prefixEnd_6167000 := by exact prefixLift 6167000
  have htrace : WordTrace (prefixWord ++ tailWord_6167000) baseStart_6167000 baseEnd_6167000 := by
    simpa [prefixWord, tailWord_6167000, baseEnd_6167000] using wordTrace_append hprefix tailTrace_6167000
  have hstable : (prefixWord ++ tailWord_6167000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167000).length < 2 ^ (prefixWord ++ tailWord_6167000).sum := by decide
  have hdescent : baseEnd_6167000 < baseStart_6167000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167027 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 3]
def baseStart_6167027 : Nat := 118140960795 + 6167027 * 2 ^ 59
def prefixEnd_6167027 : Nat := 4983230072969 + 3 ^ 40 * 6167027 * 2
def baseEnd_6167027 : Nat := 3166649060255148212200865

theorem tailTrace_6167027 : CollatzResearch.WordTrace tailWord_6167027 prefixEnd_6167027 3166649060255148212200865 := by
  unfold tailWord_6167027
  simp only [CollatzResearch.WordTrace]
  refine ⟨224929953428921898203643335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149953302285947932135762223 224929953428921898203643335)
  ·
    refine ⟨337394930143382847305465003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224929953428921898203643335 337394930143382847305465003)
    ·
      refine ⟨506092395215074270958197505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337394930143382847305465003 506092395215074270958197505)
      ·
        refine ⟨379569296411305703218648129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506092395215074270958197505 379569296411305703218648129)
        ·
          refine ⟨284676972308479277413986097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379569296411305703218648129 284676972308479277413986097)
          ·
            refine ⟨213507729231359458060489573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284676972308479277413986097 213507729231359458060489573)
            ·
              refine ⟨40032699230879898386341795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213507729231359458060489573 40032699230879898386341795)
              ·
                refine ⟨60049048846319847579512693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40032699230879898386341795 60049048846319847579512693)
                ·
                  refine ⟨5629598329342485710579315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60049048846319847579512693 5629598329342485710579315)
                  ·
                    refine ⟨8444397494013728565868973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629598329342485710579315 8444397494013728565868973)
                    ·
                      refine ⟨3166649060255148212200865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444397494013728565868973 3166649060255148212200865)
                      ·
                        rfl

theorem cell23_6167027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_6167027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167027 prefixEnd_6167027 := by exact prefixLift 6167027
  have htrace : WordTrace (prefixWord ++ tailWord_6167027) baseStart_6167027 baseEnd_6167027 := by
    simpa [prefixWord, tailWord_6167027, baseEnd_6167027] using wordTrace_append hprefix tailTrace_6167027
  have hstable : (prefixWord ++ tailWord_6167027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167027).length < 2 ^ (prefixWord ++ tailWord_6167027).sum := by decide
  have hdescent : baseEnd_6167027 < baseStart_6167027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167061 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_6167061 : Nat := 118140960795 + 6167061 * 2 ^ 59
def prefixEnd_6167061 : Nat := 4983230072969 + 3 ^ 40 * 6167061 * 2
def baseEnd_6167061 : Nat := 3166666518597401079175709

theorem tailTrace_6167061 : CollatzResearch.WordTrace tailWord_6167061 prefixEnd_6167061 3166666518597401079175709 := by
  unfold tailWord_6167061
  simp only [CollatzResearch.WordTrace]
  refine ⟨224931193510798722010381037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149954129007199148006920691 224931193510798722010381037)
  ·
    refine ⟨84349197566549520753892889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224931193510798722010381037 84349197566549520753892889)
    ·
      refine ⟨63261898174912140565419667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84349197566549520753892889 63261898174912140565419667)
      ·
        refine ⟨94892847262368210848129501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63261898174912140565419667 94892847262368210848129501)
        ·
          refine ⟨35584817723388079068048563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94892847262368210848129501 35584817723388079068048563)
          ·
            refine ⟨53377226585082118602072845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35584817723388079068048563 53377226585082118602072845)
            ·
              refine ⟨20016459969405794475777317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53377226585082118602072845 20016459969405794475777317)
              ·
                refine ⟨3753086244263586464208247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20016459969405794475777317 3753086244263586464208247)
                ·
                  refine ⟨5629629366395379696312371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753086244263586464208247 5629629366395379696312371)
                  ·
                    refine ⟨8444444049593069544468557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629629366395379696312371 8444444049593069544468557)
                    ·
                      refine ⟨3166666518597401079175709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444444049593069544468557 3166666518597401079175709)
                      ·
                        rfl

theorem cell23_6167061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_6167061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167061 prefixEnd_6167061 := by exact prefixLift 6167061
  have htrace : WordTrace (prefixWord ++ tailWord_6167061) baseStart_6167061 baseEnd_6167061 := by
    simpa [prefixWord, tailWord_6167061, baseEnd_6167061] using wordTrace_append hprefix tailTrace_6167061
  have hstable : (prefixWord ++ tailWord_6167061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167061).length < 2 ^ (prefixWord ++ tailWord_6167061).sum := by decide
  have hdescent : baseEnd_6167061 < baseStart_6167061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167090 : List Nat := [3, 2, 1, 1, 2, 1, 2, 11]
def baseStart_6167090 : Nat := 118140960795 + 6167090 * 2 ^ 59
def prefixEnd_6167090 : Nat := 4983230072969 + 3 ^ 40 * 6167090 * 2
def baseEnd_6167090 : Nat := 117284496649495609841225

theorem tailTrace_6167090 : CollatzResearch.WordTrace tailWord_6167090 prefixEnd_6167090 117284496649495609841225 := by
  unfold tailWord_6167090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56233062806923414990796681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149954834151795773308791149 56233062806923414990796681)
  ·
    refine ⟨42174797105192561243097511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56233062806923414990796681 42174797105192561243097511)
    ·
      refine ⟨63262195657788841864646267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42174797105192561243097511 63262195657788841864646267)
      ·
        refine ⟨94893293486683262796969401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63262195657788841864646267 94893293486683262796969401)
        ·
          refine ⟨71169970115012447097727051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94893293486683262796969401 71169970115012447097727051)
          ·
            refine ⟨106754955172518670646590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71169970115012447097727051 106754955172518670646590577)
            ·
              refine ⟨80066216379389002984942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106754955172518670646590577 80066216379389002984942933)
              ·
                refine ⟨117284496649495609841225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80066216379389002984942933 117284496649495609841225)
                ·
                  rfl

theorem cell23_6167090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_6167090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167090 prefixEnd_6167090 := by exact prefixLift 6167090
  have htrace : WordTrace (prefixWord ++ tailWord_6167090) baseStart_6167090 baseEnd_6167090 := by
    simpa [prefixWord, tailWord_6167090, baseEnd_6167090] using wordTrace_append hprefix tailTrace_6167090
  have hstable : (prefixWord ++ tailWord_6167090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167090).length < 2 ^ (prefixWord ++ tailWord_6167090).sum := by decide
  have hdescent : baseEnd_6167090 < baseStart_6167090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167094 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6167094 : Nat := 118140960795 + 6167094 * 2 ^ 59
def prefixEnd_6167094 : Nat := 4983230072969 + 3 ^ 40 * 6167094 * 2
def baseEnd_6167094 : Nat := 1055561154486333150021019

theorem tailTrace_6167094 : CollatzResearch.WordTrace tailWord_6167094 prefixEnd_6167094 1055561154486333150021019 := by
  unfold tailWord_6167094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058274819979948040395771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149954931413119445764221557 14058274819979948040395771)
  ·
    refine ⟨21087412229969922060593657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058274819979948040395771 21087412229969922060593657)
    ·
      refine ⟨15815559172477441545445243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21087412229969922060593657 15815559172477441545445243)
      ·
        refine ⟨23723338758716162318167865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15815559172477441545445243 23723338758716162318167865)
        ·
          refine ⟨17792504069037121738625899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23723338758716162318167865 17792504069037121738625899)
          ·
            refine ⟨26688756103555682607938849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792504069037121738625899 26688756103555682607938849)
            ·
              refine ⟨20016567077666761955954137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26688756103555682607938849 20016567077666761955954137)
              ·
                refine ⟨15012425308250071466965603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20016567077666761955954137 15012425308250071466965603)
                ·
                  refine ⟨22518637962375107200448405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15012425308250071466965603 22518637962375107200448405)
                  ·
                    refine ⟨1055561154486333150021019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22518637962375107200448405 1055561154486333150021019)
                    ·
                      rfl

theorem cell23_6167094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6167094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167094 prefixEnd_6167094 := by exact prefixLift 6167094
  have htrace : WordTrace (prefixWord ++ tailWord_6167094) baseStart_6167094 baseEnd_6167094 := by
    simpa [prefixWord, tailWord_6167094, baseEnd_6167094] using wordTrace_append hprefix tailTrace_6167094
  have hstable : (prefixWord ++ tailWord_6167094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167094).length < 2 ^ (prefixWord ++ tailWord_6167094).sum := by decide
  have hdescent : baseEnd_6167094 < baseStart_6167094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167097 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6167097 : Nat := 118140960795 + 6167097 * 2 ^ 59
def prefixEnd_6167097 : Nat := 4983230072969 + 3 ^ 40 * 6167097 * 2
def baseEnd_6167097 : Nat := 3166685003900962938325543

theorem tailTrace_6167097 : CollatzResearch.WordTrace tailWord_6167097 prefixEnd_6167097 3166685003900962938325543 := by
  unfold tailWord_6167097
  simp only [CollatzResearch.WordTrace]
  refine ⟨224932506538668300158691545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149955004359112200105794363 224932506538668300158691545)
  ·
    refine ⟨168699379904001225119018659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224932506538668300158691545 168699379904001225119018659)
    ·
      refine ⟨253049069856001837678527989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168699379904001225119018659 253049069856001837678527989)
      ·
        refine ⟨23723350299000172282361999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253049069856001837678527989 23723350299000172282361999)
        ·
          refine ⟨35585025448500258423542999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23723350299000172282361999 35585025448500258423542999)
          ·
            refine ⟨53377538172750387635314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35585025448500258423542999 53377538172750387635314499)
            ·
              refine ⟨80066307259125581452971749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53377538172750387635314499 80066307259125581452971749)
              ·
                refine ⟨15012432611086046522432203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80066307259125581452971749 15012432611086046522432203)
                ·
                  refine ⟨22518648916629069783648305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15012432611086046522432203 22518648916629069783648305)
                  ·
                    refine ⟨16888986687471802337736229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22518648916629069783648305 16888986687471802337736229)
                    ·
                      refine ⟨3166685003900962938325543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16888986687471802337736229 3166685003900962938325543)
                      ·
                        rfl

theorem cell23_6167097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6167097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167097 prefixEnd_6167097 := by exact prefixLift 6167097
  have htrace : WordTrace (prefixWord ++ tailWord_6167097) baseStart_6167097 baseEnd_6167097 := by
    simpa [prefixWord, tailWord_6167097, baseEnd_6167097] using wordTrace_append hprefix tailTrace_6167097
  have hstable : (prefixWord ++ tailWord_6167097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167097).length < 2 ^ (prefixWord ++ tailWord_6167097).sum := by decide
  have hdescent : baseEnd_6167097 < baseStart_6167097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167101 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6167101 : Nat := 118140960795 + 6167101 * 2 ^ 59
def prefixEnd_6167101 : Nat := 4983230072969 + 3 ^ 40 * 6167101 * 2
def baseEnd_6167101 : Nat := 3166687057823580922675525

theorem tailTrace_6167101 : CollatzResearch.WordTrace tailWord_6167101 prefixEnd_6167101 3166687057823580922675525 := by
  unfold tailWord_6167101
  simp only [CollatzResearch.WordTrace]
  refine ⟨224932652430653808841837157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149955101620435872561224771 224932652430653808841837157)
  ·
    refine ⟨42174872330747589157844467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224932652430653808841837157 42174872330747589157844467)
    ·
      refine ⟨63262308496121383736766701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42174872330747589157844467 63262308496121383736766701)
      ·
        refine ⟨23723365686045518901287513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63262308496121383736766701 23723365686045518901287513)
        ·
          refine ⟨17792524264534139175965635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23723365686045518901287513 17792524264534139175965635)
          ·
            refine ⟨26688786396801208763948453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792524264534139175965635 26688786396801208763948453)
            ·
              refine ⟨5004147449400226643240335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26688786396801208763948453 5004147449400226643240335)
              ·
                refine ⟨7506221174100339964860503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004147449400226643240335 7506221174100339964860503)
                ·
                  refine ⟨11259331761150509947290755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506221174100339964860503 11259331761150509947290755)
                  ·
                    refine ⟨16888997641725764920936133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11259331761150509947290755 16888997641725764920936133)
                    ·
                      refine ⟨3166687057823580922675525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16888997641725764920936133 3166687057823580922675525)
                      ·
                        rfl

theorem cell23_6167101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6167101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167101 prefixEnd_6167101 := by exact prefixLift 6167101
  have htrace : WordTrace (prefixWord ++ tailWord_6167101) baseStart_6167101 baseEnd_6167101 := by
    simpa [prefixWord, tailWord_6167101, baseEnd_6167101] using wordTrace_append hprefix tailTrace_6167101
  have hstable : (prefixWord ++ tailWord_6167101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167101).length < 2 ^ (prefixWord ++ tailWord_6167101).sum := by decide
  have hdescent : baseEnd_6167101 < baseStart_6167101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167111 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 2, 4]
def baseStart_6167111 : Nat := 118140960795 + 6167111 * 2 ^ 59
def prefixEnd_6167111 : Nat := 4983230072969 + 3 ^ 40 * 6167111 * 2
def baseEnd_6167111 : Nat := 1055564064210041961183493

theorem tailTrace_6167111 : CollatzResearch.WordTrace tailWord_6167111 prefixEnd_6167111 1055564064210041961183493 := by
  unfold tailWord_6167111
  simp only [CollatzResearch.WordTrace]
  refine ⟨224933017160617580549701187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149955344773745053699800791 224933017160617580549701187)
  ·
    refine ⟨337399525740926370824551781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224933017160617580549701187 337399525740926370824551781)
    ·
      refine ⟨63262411076423694529603459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337399525740926370824551781 63262411076423694529603459)
      ·
        refine ⟨94893616614635541794405189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63262411076423694529603459 94893616614635541794405189)
        ·
          refine ⟨17792553115244164086450973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94893616614635541794405189 17792553115244164086450973)
          ·
            refine ⟨6672207418216561532419115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17792553115244164086450973 6672207418216561532419115)
            ·
              refine ⟨10008311127324842298628673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672207418216561532419115 10008311127324842298628673)
              ·
                refine ⟨7506233345493631723971505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10008311127324842298628673 7506233345493631723971505)
                ·
                  refine ⟨5629675009120223792978629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7506233345493631723971505 5629675009120223792978629)
                  ·
                    refine ⟨1055564064210041961183493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629675009120223792978629 1055564064210041961183493)
                    ·
                      rfl

theorem cell23_6167111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_6167111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167111 prefixEnd_6167111 := by exact prefixLift 6167111
  have htrace : WordTrace (prefixWord ++ tailWord_6167111) baseStart_6167111 baseEnd_6167111 := by
    simpa [prefixWord, tailWord_6167111, baseEnd_6167111] using wordTrace_append hprefix tailTrace_6167111
  have hstable : (prefixWord ++ tailWord_6167111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167111).length < 2 ^ (prefixWord ++ tailWord_6167111).sum := by decide
  have hdescent : baseEnd_6167111 < baseStart_6167111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167118 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_6167118 : Nat := 118140960795 + 6167118 * 2 ^ 59
def prefixEnd_6167118 : Nat := 4983230072969 + 3 ^ 40 * 6167118 * 2
def baseEnd_6167118 : Nat := 3166695786994707356162947

theorem tailTrace_6167118 : CollatzResearch.WordTrace tailWord_6167118 prefixEnd_6167118 3166695786994707356162947 := by
  unfold tailWord_6167118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28116659058949027593150751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149955514981061480496804005 28116659058949027593150751)
  ·
    refine ⟨42174988588423541389726127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28116659058949027593150751 42174988588423541389726127)
    ·
      refine ⟨63262482882635312084589191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42174988588423541389726127 63262482882635312084589191)
      ·
        refine ⟨94893724323952968126883787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63262482882635312084589191 94893724323952968126883787)
        ·
          refine ⟨142340586485929452190325681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94893724323952968126883787 142340586485929452190325681)
          ·
            refine ⟨106755439864447089142744261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142340586485929452190325681 106755439864447089142744261)
            ·
              refine ⟨20016644974583829214264549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106755439864447089142744261 20016644974583829214264549)
              ·
                refine ⟨3753120932734467977674603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20016644974583829214264549 3753120932734467977674603)
                ·
                  refine ⟨5629681399101701966511905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753120932734467977674603 5629681399101701966511905)
                  ·
                    refine ⟨4222261049326276474883929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629681399101701966511905 4222261049326276474883929)
                    ·
                      refine ⟨3166695786994707356162947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222261049326276474883929 3166695786994707356162947)
                      ·
                        rfl

theorem cell23_6167118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_6167118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167118 prefixEnd_6167118 := by exact prefixLift 6167118
  have htrace : WordTrace (prefixWord ++ tailWord_6167118) baseStart_6167118 baseEnd_6167118 := by
    simpa [prefixWord, tailWord_6167118, baseEnd_6167118] using wordTrace_append hprefix tailTrace_6167118
  have hstable : (prefixWord ++ tailWord_6167118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167118).length < 2 ^ (prefixWord ++ tailWord_6167118).sum := by decide
  have hdescent : baseEnd_6167118 < baseStart_6167118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167120 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_6167120 : Nat := 118140960795 + 6167120 * 2 ^ 59
def prefixEnd_6167120 : Nat := 4983230072969 + 3 ^ 40 * 6167120 * 2
def baseEnd_6167120 : Nat := 1055565604652005449445979

theorem tailTrace_6167120 : CollatzResearch.WordTrace tailWord_6167120 prefixEnd_6167120 1055565604652005449445979 := by
  unfold tailWord_6167120
  simp only [CollatzResearch.WordTrace]
  refine ⟨112466672708792487543389407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149955563611723316724519209 112466672708792487543389407)
  ·
    refine ⟨168700009063188731315084111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112466672708792487543389407 168700009063188731315084111)
    ·
      refine ⟨253050013594783096972626167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168700009063188731315084111 253050013594783096972626167)
      ·
        refine ⟨379575020392174645458939251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253050013594783096972626167 379575020392174645458939251)
        ·
          refine ⟨569362530588261968188408877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379575020392174645458939251 569362530588261968188408877)
          ·
            refine ⟨213510948970598238070653329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569362530588261968188408877 213510948970598238070653329)
            ·
              refine ⟨160133211727948678552989997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213510948970598238070653329 160133211727948678552989997)
              ·
                refine ⟨60049954397980754457371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160133211727948678552989997 60049954397980754457371249)
                ·
                  refine ⟨45037465798485565843028437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60049954397980754457371249 45037465798485565843028437)
                  ·
                    refine ⟨1055565604652005449445979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45037465798485565843028437 1055565604652005449445979)
                    ·
                      rfl

theorem cell23_6167120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_6167120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167120 prefixEnd_6167120 := by exact prefixLift 6167120
  have htrace : WordTrace (prefixWord ++ tailWord_6167120) baseStart_6167120 baseEnd_6167120 := by
    simpa [prefixWord, tailWord_6167120, baseEnd_6167120] using wordTrace_append hprefix tailTrace_6167120
  have hstable : (prefixWord ++ tailWord_6167120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167120).length < 2 ^ (prefixWord ++ tailWord_6167120).sum := by decide
  have hdescent : baseEnd_6167120 < baseStart_6167120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167141 : List Nat := [1, 3, 1, 3, 5, 1, 2, 7]
def baseStart_6167141 : Nat := 118140960795 + 6167141 * 2 ^ 59
def prefixEnd_6167141 : Nat := 4983230072969 + 3 ^ 40 * 6167141 * 2
def baseEnd_6167141 : Nat := 117285466557398546895383

theorem tailTrace_6167141 : CollatzResearch.WordTrace tailWord_6167141 prefixEnd_6167141 117285466557398546895383 := by
  unfold tailWord_6167141
  simp only [CollatzResearch.WordTrace]
  refine ⟨224934111350508895673293277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149956074233672597115528851 224934111350508895673293277)
  ·
    refine ⟨84350291756440835877484979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224934111350508895673293277 84350291756440835877484979)
    ·
      refine ⟨126525437634661253816227469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84350291756440835877484979 126525437634661253816227469)
      ·
        refine ⟨47447039112997970181085301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126525437634661253816227469 47447039112997970181085301)
        ·
          refine ⟨4448159916843559704476747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47447039112997970181085301 4448159916843559704476747)
          ·
            refine ⟨6672239875265339556715121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448159916843559704476747 6672239875265339556715121)
            ·
              refine ⟨5004179906449004667536341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672239875265339556715121 5004179906449004667536341)
              ·
                refine ⟨117285466557398546895383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5004179906449004667536341 117285466557398546895383)
                ·
                  rfl

theorem cell23_6167141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 7].length) (baseStart_6167141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167141 prefixEnd_6167141 := by exact prefixLift 6167141
  have htrace : WordTrace (prefixWord ++ tailWord_6167141) baseStart_6167141 baseEnd_6167141 := by
    simpa [prefixWord, tailWord_6167141, baseEnd_6167141] using wordTrace_append hprefix tailTrace_6167141
  have hstable : (prefixWord ++ tailWord_6167141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167141).length < 2 ^ (prefixWord ++ tailWord_6167141).sum := by decide
  have hdescent : baseEnd_6167141 < baseStart_6167141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167152 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 1, 2, 2]
def baseStart_6167152 : Nat := 118140960795 + 6167152 * 2 ^ 59
def prefixEnd_6167152 : Nat := 4983230072969 + 3 ^ 40 * 6167152 * 2
def baseEnd_6167152 : Nat := 3166713245336960223137791

theorem tailTrace_6167152 : CollatzResearch.WordTrace tailWord_6167152 prefixEnd_6167152 3166713245336960223137791 := by
  unfold tailWord_6167152
  simp only [CollatzResearch.WordTrace]
  refine ⟨112467256276734522275971855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149956341702312696367962473 112467256276734522275971855)
  ·
    refine ⟨168700884415101783413957783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112467256276734522275971855 168700884415101783413957783)
    ·
      refine ⟨253051326622652675120936675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168700884415101783413957783 253051326622652675120936675)
      ·
        refine ⟨379576989933979012681405013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253051326622652675120936675 379576989933979012681405013)
        ·
          refine ⟨4448167850788816554860215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 379576989933979012681405013 4448167850788816554860215)
          ·
            refine ⟨6672251776183224832290323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448167850788816554860215 6672251776183224832290323)
            ·
              refine ⟨10008377664274837248435485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672251776183224832290323 10008377664274837248435485)
              ·
                refine ⟨3753141624103063968163307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10008377664274837248435485 3753141624103063968163307)
                ·
                  refine ⟨5629712436154595952244961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753141624103063968163307 5629712436154595952244961)
                  ·
                    refine ⟨4222284327115946964183721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5629712436154595952244961 4222284327115946964183721)
                    ·
                      refine ⟨3166713245336960223137791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222284327115946964183721 3166713245336960223137791)
                      ·
                        rfl

theorem cell23_6167152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 2, 2].length) (baseStart_6167152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167152 prefixEnd_6167152 := by exact prefixLift 6167152
  have htrace : WordTrace (prefixWord ++ tailWord_6167152) baseStart_6167152 baseEnd_6167152 := by
    simpa [prefixWord, tailWord_6167152, baseEnd_6167152] using wordTrace_append hprefix tailTrace_6167152
  have hstable : (prefixWord ++ tailWord_6167152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167152).length < 2 ^ (prefixWord ++ tailWord_6167152).sum := by decide
  have hdescent : baseEnd_6167152 < baseStart_6167152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167161 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 1, 3, 2]
def baseStart_6167161 : Nat := 118140960795 + 6167161 * 2 ^ 59
def prefixEnd_6167161 : Nat := 4983230072969 + 3 ^ 40 * 6167161 * 2
def baseEnd_6167161 : Nat := 3166717866662850687925249

theorem tailTrace_6167161 : CollatzResearch.WordTrace tailWord_6167161 prefixEnd_6167161 3166717866662850687925249 := by
  unfold tailWord_6167161
  simp only [CollatzResearch.WordTrace]
  refine ⟨224934840810436439089021337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149956560540290959392680891 224934840810436439089021337)
  ·
    refine ⟨168701130607827329316766003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224934840810436439089021337 168701130607827329316766003)
    ·
      refine ⟨253051695911740993975149005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168701130607827329316766003 253051695911740993975149005)
      ·
        refine ⟨94894385966902872740680877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253051695911740993975149005 94894385966902872740680877)
        ·
          refine ⟨35585394737588577277755329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94894385966902872740680877 35585394737588577277755329)
          ·
            refine ⟨26689046053191432958316497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35585394737588577277755329 26689046053191432958316497)
            ·
              refine ⟨20016784539893574718737373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26689046053191432958316497 20016784539893574718737373)
              ·
                refine ⟨7506294202460090519526515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20016784539893574718737373 7506294202460090519526515)
                ·
                  refine ⟨11259441303690135779289773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506294202460090519526515 11259441303690135779289773)
                  ·
                    refine ⟨4222290488883800917233665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11259441303690135779289773 4222290488883800917233665)
                    ·
                      refine ⟨3166717866662850687925249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222290488883800917233665 3166717866662850687925249)
                      ·
                        rfl

theorem cell23_6167161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_6167161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167161 prefixEnd_6167161 := by exact prefixLift 6167161
  have htrace : WordTrace (prefixWord ++ tailWord_6167161) baseStart_6167161 baseEnd_6167161 := by
    simpa [prefixWord, tailWord_6167161, baseEnd_6167161] using wordTrace_append hprefix tailTrace_6167161
  have hstable : (prefixWord ++ tailWord_6167161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167161).length < 2 ^ (prefixWord ++ tailWord_6167161).sum := by decide
  have hdescent : baseEnd_6167161 < baseStart_6167161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167177 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_6167177 : Nat := 118140960795 + 6167177 * 2 ^ 59
def prefixEnd_6167177 : Nat := 4983230072969 + 3 ^ 40 * 6167177 * 2
def baseEnd_6167177 : Nat := 3166726082353322625325175

theorem tailTrace_6167177 : CollatzResearch.WordTrace tailWord_6167177 prefixEnd_6167177 3166726082353322625325175 := by
  unfold tailWord_6167177
  simp only [CollatzResearch.WordTrace]
  refine ⟨224935424378378473821603785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149956949585585649214402523 224935424378378473821603785)
  ·
    refine ⟨168701568283783855366202839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224935424378378473821603785 168701568283783855366202839)
    ·
      refine ⟨253052352425675783049304259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168701568283783855366202839 253052352425675783049304259)
      ·
        refine ⟨379578528638513674573956389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253052352425675783049304259 379578528638513674573956389)
        ·
          refine ⟨71170974119721313982616823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379578528638513674573956389 71170974119721313982616823)
          ·
            refine ⟨106756461179581970973925235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71170974119721313982616823 106756461179581970973925235)
            ·
              refine ⟨160134691769372956460887853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106756461179581970973925235 160134691769372956460887853)
              ·
                refine ⟨60050509413514858672832945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160134691769372956460887853 60050509413514858672832945)
                ·
                  refine ⟨45037882060136144004624709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60050509413514858672832945 45037882060136144004624709)
                  ·
                    refine ⟨8444602886275527000867133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45037882060136144004624709 8444602886275527000867133)
                    ·
                      refine ⟨3166726082353322625325175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444602886275527000867133 3166726082353322625325175)
                      ·
                        rfl

theorem cell23_6167177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_6167177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167177 prefixEnd_6167177 := by exact prefixLift 6167177
  have htrace : WordTrace (prefixWord ++ tailWord_6167177) baseStart_6167177 baseEnd_6167177 := by
    simpa [prefixWord, tailWord_6167177, baseEnd_6167177] using wordTrace_append hprefix tailTrace_6167177
  have hstable : (prefixWord ++ tailWord_6167177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167177).length < 2 ^ (prefixWord ++ tailWord_6167177).sum := by decide
  have hdescent : baseEnd_6167177 < baseStart_6167177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167197 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 7]
def baseStart_6167197 : Nat := 118140960795 + 6167197 * 2 ^ 59
def prefixEnd_6167197 : Nat := 4983230072969 + 3 ^ 40 * 6167197 * 2
def baseEnd_6167197 : Nat := 351859594662934727452787

theorem tailTrace_6167197 : CollatzResearch.WordTrace tailWord_6167197 prefixEnd_6167197 351859594662934727452787 := by
  unfold tailWord_6167197
  simp only [CollatzResearch.WordTrace]
  refine ⟨224936153838306017237331845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149957435892204011491554563 224936153838306017237331845)
  ·
    refine ⟨42175528844682378231999721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224936153838306017237331845 42175528844682378231999721)
    ·
      refine ⟨31631646633511783673999791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42175528844682378231999721 31631646633511783673999791)
      ·
        refine ⟨47447469950267675510999687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31631646633511783673999791 47447469950267675510999687)
        ·
          refine ⟨71171204925401513266499531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47447469950267675510999687 71171204925401513266499531)
          ·
            refine ⟨106756807388102269899749297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71171204925401513266499531 106756807388102269899749297)
            ·
              refine ⟨80067605541076702424811973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106756807388102269899749297 80067605541076702424811973)
              ·
                refine ⟨15012676038951881704652245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80067605541076702424811973 15012676038951881704652245)
                ·
                  refine ⟨351859594662934727452787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15012676038951881704652245 351859594662934727452787)
                  ·
                    rfl

theorem cell23_6167197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_6167197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167197 prefixEnd_6167197 := by exact prefixLift 6167197
  have htrace : WordTrace (prefixWord ++ tailWord_6167197) baseStart_6167197 baseEnd_6167197 := by
    simpa [prefixWord, tailWord_6167197, baseEnd_6167197] using wordTrace_append hprefix tailTrace_6167197
  have hstable : (prefixWord ++ tailWord_6167197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167197).length < 2 ^ (prefixWord ++ tailWord_6167197).sum := by decide
  have hdescent : baseEnd_6167197 < baseStart_6167197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167231 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 5]
def baseStart_6167231 : Nat := 118140960795 + 6167231 * 2 ^ 59
def prefixEnd_6167231 : Nat := 4983230072969 + 3 ^ 40 * 6167231 * 2
def baseEnd_6167231 : Nat := 351861534478740601561103

theorem tailTrace_6167231 : CollatzResearch.WordTrace tailWord_6167231 prefixEnd_6167231 351861534478740601561103 := by
  unfold tailWord_6167231
  simp only [CollatzResearch.WordTrace]
  refine ⟨224937393920182841044069547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149958262613455227362713031 224937393920182841044069547)
  ·
    refine ⟨337406090880274261566104321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224937393920182841044069547 337406090880274261566104321)
    ·
      refine ⟨253054568160205696174578241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337406090880274261566104321 253054568160205696174578241)
      ·
        refine ⟨189790926120154272130933681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253054568160205696174578241 189790926120154272130933681)
        ·
          refine ⟨142343194590115704098200261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189790926120154272130933681 142343194590115704098200261)
          ·
            refine ⟨26689348985646694518412549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142343194590115704098200261 26689348985646694518412549)
            ·
              refine ⟨5004252934808755222202353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26689348985646694518412549 5004252934808755222202353)
              ·
                refine ⟨3753189701106566416651765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004252934808755222202353 3753189701106566416651765)
                ·
                  refine ⟨351861534478740601561103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753189701106566416651765 351861534478740601561103)
                  ·
                    rfl

theorem cell23_6167231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 5].length) (baseStart_6167231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167231 prefixEnd_6167231 := by exact prefixLift 6167231
  have htrace : WordTrace (prefixWord ++ tailWord_6167231) baseStart_6167231 baseEnd_6167231 := by
    simpa [prefixWord, tailWord_6167231, baseEnd_6167231] using wordTrace_append hprefix tailTrace_6167231
  have hstable : (prefixWord ++ tailWord_6167231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167231).length < 2 ^ (prefixWord ++ tailWord_6167231).sum := by decide
  have hdescent : baseEnd_6167231 < baseStart_6167231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167264 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2]
def baseStart_6167264 : Nat := 118140960795 + 6167264 * 2 ^ 59
def prefixEnd_6167264 : Nat := 4983230072969 + 3 ^ 40 * 6167264 * 2
def baseEnd_6167264 : Nat := 3166770755170263784937275

theorem tailTrace_6167264 : CollatzResearch.WordTrace tailWord_6167264 prefixEnd_6167264 3166770755170263784937275 := by
  unfold tailWord_6167264
  simp only [CollatzResearch.WordTrace]
  refine ⟨112469298764531643840010423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149959065019375525120013897 112469298764531643840010423)
  ·
    refine ⟨168703948146797465760015635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112469298764531643840010423 168703948146797465760015635)
    ·
      refine ⟨253055922220196198640023453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168703948146797465760015635 253055922220196198640023453)
      ·
        refine ⟨94895970832573574490008795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253055922220196198640023453 94895970832573574490008795)
        ·
          refine ⟨142343956248860361735013193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94895970832573574490008795 142343956248860361735013193)
          ·
            refine ⟨106757967186645271301259895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142343956248860361735013193 106757967186645271301259895)
            ·
              refine ⟨160136950779967906951889843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106757967186645271301259895 160136950779967906951889843)
              ·
                refine ⟨240205426169951860427834765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160136950779967906951889843 240205426169951860427834765)
                ·
                  refine ⟨90077034813731947660438037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240205426169951860427834765 90077034813731947660438037)
                  ·
                    refine ⟨4222361006893685046583033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90077034813731947660438037 4222361006893685046583033)
                    ·
                      refine ⟨3166770755170263784937275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222361006893685046583033 3166770755170263784937275)
                      ·
                        rfl

theorem cell23_6167264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_6167264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167264 prefixEnd_6167264 := by exact prefixLift 6167264
  have htrace : WordTrace (prefixWord ++ tailWord_6167264) baseStart_6167264 baseEnd_6167264 := by
    simpa [prefixWord, tailWord_6167264, baseEnd_6167264] using wordTrace_append hprefix tailTrace_6167264
  have hstable : (prefixWord ++ tailWord_6167264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167264).length < 2 ^ (prefixWord ++ tailWord_6167264).sum := by decide
  have hdescent : baseEnd_6167264 < baseStart_6167264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167274 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_6167274 : Nat := 118140960795 + 6167274 * 2 ^ 59
def prefixEnd_6167274 : Nat := 4983230072969 + 3 ^ 40 * 6167274 * 2
def baseEnd_6167274 : Nat := 1055591963325602915270743

theorem tailTrace_6167274 : CollatzResearch.WordTrace tailWord_6167274 prefixEnd_6167274 1055591963325602915270743 := by
  unfold tailWord_6167274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56234740564756764846971219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149959308172684706258589917 56234740564756764846971219)
  ·
    refine ⟨84352110847135147270456829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56234740564756764846971219 84352110847135147270456829)
    ·
      refine ⟨31632041567675680226421311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84352110847135147270456829 31632041567675680226421311)
      ·
        refine ⟨47448062351513520339631967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31632041567675680226421311 47448062351513520339631967)
        ·
          refine ⟨71172093527270280509447951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47448062351513520339631967 71172093527270280509447951)
          ·
            refine ⟨106758140290905420764171927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71172093527270280509447951 106758140290905420764171927)
            ·
              refine ⟨160137210436358131146257891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106758140290905420764171927 160137210436358131146257891)
              ·
                refine ⟨240205815654537196719386837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160137210436358131146257891 240205815654537196719386837)
                ·
                  refine ⟨5629823804403215548110629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 240205815654537196719386837 5629823804403215548110629)
                  ·
                    refine ⟨1055591963325602915270743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629823804403215548110629 1055591963325602915270743)
                    ·
                      rfl

theorem cell23_6167274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_6167274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167274 prefixEnd_6167274 := by exact prefixLift 6167274
  have htrace : WordTrace (prefixWord ++ tailWord_6167274) baseStart_6167274 baseEnd_6167274 := by
    simpa [prefixWord, tailWord_6167274, baseEnd_6167274] using wordTrace_append hprefix tailTrace_6167274
  have hstable : (prefixWord ++ tailWord_6167274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167274).length < 2 ^ (prefixWord ++ tailWord_6167274).sum := by decide
  have hdescent : baseEnd_6167274 < baseStart_6167274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167298 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6167298 : Nat := 118140960795 + 6167298 * 2 ^ 59
def prefixEnd_6167298 : Nat := 4983230072969 + 3 ^ 40 * 6167298 * 2
def baseEnd_6167298 : Nat := 3166788213512516651912119

theorem tailTrace_6167298 : CollatzResearch.WordTrace tailWord_6167298 prefixEnd_6167298 3166788213512516651912119 := by
  unfold tailWord_6167298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56234959402735027871689637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149959891740626740991172365 56234959402735027871689637)
  ·
    refine ⟨10544054888012817725941807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56234959402735027871689637 10544054888012817725941807)
    ·
      refine ⟨15816082332019226588912711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10544054888012817725941807 15816082332019226588912711)
      ·
        refine ⟨23724123498028839883369067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15816082332019226588912711 23724123498028839883369067)
        ·
          refine ⟨35586185247043259825053601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724123498028839883369067 35586185247043259825053601)
          ·
            refine ⟨26689638935282444868790201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35586185247043259825053601 26689638935282444868790201)
            ·
              refine ⟨20017229201461833651592651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26689638935282444868790201 20017229201461833651592651)
              ·
                refine ⟨30025843802192750477388977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20017229201461833651592651 30025843802192750477388977)
                ·
                  refine ⟨22519382851644562858041733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30025843802192750477388977 22519382851644562858041733)
                  ·
                    refine ⟨4222384284683355535882825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22519382851644562858041733 4222384284683355535882825)
                    ·
                      refine ⟨3166788213512516651912119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222384284683355535882825 3166788213512516651912119)
                      ·
                        rfl

theorem cell23_6167298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6167298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167298 prefixEnd_6167298 := by exact prefixLift 6167298
  have htrace : WordTrace (prefixWord ++ tailWord_6167298) baseStart_6167298 baseEnd_6167298 := by
    simpa [prefixWord, tailWord_6167298, baseEnd_6167298] using wordTrace_append hprefix tailTrace_6167298
  have hstable : (prefixWord ++ tailWord_6167298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167298).length < 2 ^ (prefixWord ++ tailWord_6167298).sum := by decide
  have hdescent : baseEnd_6167298 < baseStart_6167298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167307 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_6167307 : Nat := 118140960795 + 6167307 * 2 ^ 59
def prefixEnd_6167307 : Nat := 4983230072969 + 3 ^ 40 * 6167307 * 2
def baseEnd_6167307 : Nat := 3166792834838407116699577

theorem tailTrace_6167307 : CollatzResearch.WordTrace tailWord_6167307 prefixEnd_6167307 3166792834838407116699577 := by
  unfold tailWord_6167307
  simp only [CollatzResearch.WordTrace]
  refine ⟨224940165867907506023836175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149960110578605004015890783 224940165867907506023836175)
  ·
    refine ⟨337410248801861259035754263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224940165867907506023836175 337410248801861259035754263)
    ·
      refine ⟨506115373202791888553631395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337410248801861259035754263 506115373202791888553631395)
      ·
        refine ⟨759173059804187832830447093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506115373202791888553631395 759173059804187832830447093)
        ·
          refine ⟨71172474356642609327854415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 759173059804187832830447093 71172474356642609327854415)
          ·
            refine ⟨106758711534963913991781623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71172474356642609327854415 106758711534963913991781623)
            ·
              refine ⟨160138067302445870987672435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106758711534963913991781623 160138067302445870987672435)
              ·
                refine ⟨240207100953668806481508653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160138067302445870987672435 240207100953668806481508653)
                ·
                  refine ⟨90077662857625802430565745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240207100953668806481508653 90077662857625802430565745)
                  ·
                    refine ⟨67558247143219351822924309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90077662857625802430565745 67558247143219351822924309)
                    ·
                      refine ⟨3166792834838407116699577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67558247143219351822924309 3166792834838407116699577)
                      ·
                        rfl

theorem cell23_6167307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_6167307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167307 prefixEnd_6167307 := by exact prefixLift 6167307
  have htrace : WordTrace (prefixWord ++ tailWord_6167307) baseStart_6167307 baseEnd_6167307 := by
    simpa [prefixWord, tailWord_6167307, baseEnd_6167307] using wordTrace_append hprefix tailTrace_6167307
  have hstable : (prefixWord ++ tailWord_6167307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167307).length < 2 ^ (prefixWord ++ tailWord_6167307).sum := by decide
  have hdescent : baseEnd_6167307 < baseStart_6167307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167342 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_6167342 : Nat := 118140960795 + 6167342 * 2 ^ 59
def prefixEnd_6167342 : Nat := 4983230072969 + 3 ^ 40 * 6167342 * 2
def baseEnd_6167342 : Nat := 1055603602220438159920639

theorem tailTrace_6167342 : CollatzResearch.WordTrace tailWord_6167342 prefixEnd_6167342 1055603602220438159920639 := by
  unfold tailWord_6167342
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117680302847588375170035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149960961615187138000906853 28117680302847588375170035)
  ·
    refine ⟨42176520454271382562755053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28117680302847588375170035 42176520454271382562755053)
    ·
      refine ⟨15816195170351768461033145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42176520454271382562755053 15816195170351768461033145)
      ·
        refine ⟨11862146377763826345774859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15816195170351768461033145 11862146377763826345774859)
        ·
          refine ⟨17793219566645739518662289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862146377763826345774859 17793219566645739518662289)
          ·
            refine ⟨13344914674984304638996717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17793219566645739518662289 13344914674984304638996717)
            ·
              refine ⟨5004343003119114239623769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13344914674984304638996717 5004343003119114239623769)
              ·
                refine ⟨3753257252339335679717827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004343003119114239623769 3753257252339335679717827)
                ·
                  refine ⟨5629885878509003519576741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753257252339335679717827 5629885878509003519576741)
                  ·
                    refine ⟨1055603602220438159920639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5629885878509003519576741 1055603602220438159920639)
                    ·
                      rfl

theorem cell23_6167342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_6167342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167342 prefixEnd_6167342 := by exact prefixLift 6167342
  have htrace : WordTrace (prefixWord ++ tailWord_6167342) baseStart_6167342 baseEnd_6167342 := by
    simpa [prefixWord, tailWord_6167342, baseEnd_6167342] using wordTrace_append hprefix tailTrace_6167342
  have hstable : (prefixWord ++ tailWord_6167342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167342).length < 2 ^ (prefixWord ++ tailWord_6167342).sum := by decide
  have hdescent : baseEnd_6167342 < baseStart_6167342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167374 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6167374 : Nat := 118140960795 + 6167374 * 2 ^ 59
def prefixEnd_6167374 : Nat := 4983230072969 + 3 ^ 40 * 6167374 * 2
def baseEnd_6167374 : Nat := 3166827238042258354561769

theorem tailTrace_6167374 : CollatzResearch.WordTrace tailWord_6167374 prefixEnd_6167374 3166827238042258354561769 := by
  unfold tailWord_6167374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117826194833097058315647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149961739705776517644350117 28117826194833097058315647)
  ·
    refine ⟨42176739292249645587473471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28117826194833097058315647 42176739292249645587473471)
    ·
      refine ⟨63265108938374468381210207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42176739292249645587473471 63265108938374468381210207)
      ·
        refine ⟨94897663407561702571815311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63265108938374468381210207 94897663407561702571815311)
        ·
          refine ⟨142346495111342553857722967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94897663407561702571815311 142346495111342553857722967)
          ·
            refine ⟨213519742667013830786584451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142346495111342553857722967 213519742667013830786584451)
            ·
              refine ⟨320279614000520746179876677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213519742667013830786584451 320279614000520746179876677)
              ·
                refine ⟨60052427625097639908726877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320279614000520746179876677 60052427625097639908726877)
                ·
                  refine ⟨22519660359411614965772579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60052427625097639908726877 22519660359411614965772579)
                  ·
                    refine ⟨33779490539117422448658869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22519660359411614965772579 33779490539117422448658869)
                    ·
                      refine ⟨3166827238042258354561769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33779490539117422448658869 3166827238042258354561769)
                      ·
                        rfl

theorem cell23_6167374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6167374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167374 prefixEnd_6167374 := by exact prefixLift 6167374
  have htrace : WordTrace (prefixWord ++ tailWord_6167374) baseStart_6167374 baseEnd_6167374 := by
    simpa [prefixWord, tailWord_6167374, baseEnd_6167374] using wordTrace_append hprefix tailTrace_6167374
  have hstable : (prefixWord ++ tailWord_6167374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167374).length < 2 ^ (prefixWord ++ tailWord_6167374).sum := by decide
  have hdescent : baseEnd_6167374 < baseStart_6167374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167394 : List Nat := [3, 3, 2, 1, 14]
def baseStart_6167394 : Nat := 118140960795 + 6167394 * 2 ^ 59
def prefixEnd_6167394 : Nat := 4983230072969 + 3 ^ 40 * 6167394 * 2
def baseEnd_6167394 : Nat := 4344084372641081311813

theorem tailTrace_6167394 : CollatzResearch.WordTrace tailWord_6167394 prefixEnd_6167394 4344084372641081311813 := by
  unfold tailWord_6167394
  simp only [CollatzResearch.WordTrace]
  refine ⟨56235834754648079970563309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149962226012394879921502157 56235834754648079970563309)
  ·
    refine ⟨21088438032993029988961241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56235834754648079970563309 21088438032993029988961241)
    ·
      refine ⟨15816328524744772491720931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21088438032993029988961241 15816328524744772491720931)
      ·
        refine ⟨23724492787117158737581397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15816328524744772491720931 23724492787117158737581397)
        ·
          refine ⟨4344084372641081311813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 23724492787117158737581397 4344084372641081311813)
          ·
            rfl

theorem cell23_6167394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 14].length) (baseStart_6167394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167394 prefixEnd_6167394 := by exact prefixLift 6167394
  have htrace : WordTrace (prefixWord ++ tailWord_6167394) baseStart_6167394 baseEnd_6167394 := by
    simpa [prefixWord, tailWord_6167394, baseEnd_6167394] using wordTrace_append hprefix tailTrace_6167394
  have hstable : (prefixWord ++ tailWord_6167394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167394).length < 2 ^ (prefixWord ++ tailWord_6167394).sum := by decide
  have hdescent : baseEnd_6167394 < baseStart_6167394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167421 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_6167421 : Nat := 118140960795 + 6167421 * 2 ^ 59
def prefixEnd_6167421 : Nat := 4983230072969 + 3 ^ 40 * 6167421 * 2
def baseEnd_6167421 : Nat := 3166851371633019670674053

theorem tailTrace_6167421 : CollatzResearch.WordTrace tailWord_6167421 prefixEnd_6167421 3166851371633019670674053 := by
  unfold tailWord_6167421
  simp only [CollatzResearch.WordTrace]
  refine ⟨224944323789494503493486117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149962882526329668995657411 224944323789494503493486117)
  ·
    refine ⟨42177060710530219405028647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224944323789494503493486117 42177060710530219405028647)
    ·
      refine ⟨63265591065795329107542971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42177060710530219405028647 63265591065795329107542971)
      ·
        refine ⟨94898386598692993661314457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63265591065795329107542971 94898386598692993661314457)
        ·
          refine ⟨71173789949019745245985843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94898386598692993661314457 71173789949019745245985843)
          ·
            refine ⟨106760684923529617868978765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71173789949019745245985843 106760684923529617868978765)
            ·
              refine ⟨40035256846323606700867037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106760684923529617868978765 40035256846323606700867037)
              ·
                refine ⟨15013221317371352512825139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40035256846323606700867037 15013221317371352512825139)
                ·
                  refine ⟨22519831976057028769237709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15013221317371352512825139 22519831976057028769237709)
                  ·
                    refine ⟨8444936991021385788464141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22519831976057028769237709 8444936991021385788464141)
                    ·
                      refine ⟨3166851371633019670674053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444936991021385788464141 3166851371633019670674053)
                      ·
                        rfl

theorem cell23_6167421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_6167421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167421 prefixEnd_6167421 := by exact prefixLift 6167421
  have htrace : WordTrace (prefixWord ++ tailWord_6167421) baseStart_6167421 baseEnd_6167421 := by
    simpa [prefixWord, tailWord_6167421, baseEnd_6167421] using wordTrace_append hprefix tailTrace_6167421
  have hstable : (prefixWord ++ tailWord_6167421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167421).length < 2 ^ (prefixWord ++ tailWord_6167421).sum := by decide
  have hdescent : baseEnd_6167421 < baseStart_6167421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167426 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6167426 : Nat := 118140960795 + 6167426 * 2 ^ 59
def prefixEnd_6167426 : Nat := 4983230072969 + 3 ^ 40 * 6167426 * 2
def baseEnd_6167426 : Nat := 3166853939036292151111531

theorem tailTrace_6167426 : CollatzResearch.WordTrace tailWord_6167426 prefixEnd_6167426 3166853939036292151111531 := by
  unfold tailWord_6167426
  simp only [CollatzResearch.WordTrace]
  refine ⟨56236126538619097336854533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149963004102984259564945421 56236126538619097336854533)
  ·
    refine ⟨10544273725991080750660225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56236126538619097336854533 10544273725991080750660225)
    ·
      refine ⟨7908205294493310562995169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10544273725991080750660225 7908205294493310562995169)
      ·
        refine ⟨5931153970869982922246377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7908205294493310562995169 5931153970869982922246377)
        ·
          refine ⟨4448365478152487191684783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5931153970869982922246377 4448365478152487191684783)
          ·
            refine ⟨6672548217228730787527175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448365478152487191684783 6672548217228730787527175)
            ·
              refine ⟨10008822325843096181290763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672548217228730787527175 10008822325843096181290763)
              ·
                refine ⟨15013233488764644271936145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10008822325843096181290763 15013233488764644271936145)
                ·
                  refine ⟨11259925116573483203952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15013233488764644271936145 11259925116573483203952109)
                  ·
                    refine ⟨4222471918715056201482041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11259925116573483203952109 4222471918715056201482041)
                    ·
                      refine ⟨3166853939036292151111531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222471918715056201482041 3166853939036292151111531)
                      ·
                        rfl

theorem cell23_6167426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6167426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167426 prefixEnd_6167426 := by exact prefixLift 6167426
  have htrace : WordTrace (prefixWord ++ tailWord_6167426) baseStart_6167426 baseEnd_6167426 := by
    simpa [prefixWord, tailWord_6167426, baseEnd_6167426] using wordTrace_append hprefix tailTrace_6167426
  have hstable : (prefixWord ++ tailWord_6167426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167426).length < 2 ^ (prefixWord ++ tailWord_6167426).sum := by decide
  have hdescent : baseEnd_6167426 < baseStart_6167426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167455 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6167455 : Nat := 118140960795 + 6167455 * 2 ^ 59
def prefixEnd_6167455 : Nat := 4983230072969 + 3 ^ 40 * 6167455 * 2
def baseEnd_6167455 : Nat := 3166868829975272537648897

theorem tailTrace_6167455 : CollatzResearch.WordTrace tailWord_6167455 prefixEnd_6167455 3166868829975272537648897 := by
  unfold tailWord_6167455
  simp only [CollatzResearch.WordTrace]
  refine ⟨224945563871371327300223819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149963709247580884866815879 224945563871371327300223819)
  ·
    refine ⟨337418345807056990950335729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224945563871371327300223819 337418345807056990950335729)
    ·
      refine ⟨253063759355292743212751797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337418345807056990950335729 253063759355292743212751797)
      ·
        refine ⟨23724727439558694676195481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253063759355292743212751797 23724727439558694676195481)
        ·
          refine ⟨17793545579669021007146611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23724727439558694676195481 17793545579669021007146611)
          ·
            refine ⟨26690318369503531510719917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17793545579669021007146611 26690318369503531510719917)
            ·
              refine ⟨10008869388563824316519969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26690318369503531510719917 10008869388563824316519969)
              ·
                refine ⟨7506652041422868237389977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10008869388563824316519969 7506652041422868237389977)
                ·
                  refine ⟨5629989031067151178042483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7506652041422868237389977 5629989031067151178042483)
                  ·
                    refine ⟨8444983546600726767063725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629989031067151178042483 8444983546600726767063725)
                    ·
                      refine ⟨3166868829975272537648897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8444983546600726767063725 3166868829975272537648897)
                      ·
                        rfl

theorem cell23_6167455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6167455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167455 prefixEnd_6167455 := by exact prefixLift 6167455
  have htrace : WordTrace (prefixWord ++ tailWord_6167455) baseStart_6167455 baseEnd_6167455 := by
    simpa [prefixWord, tailWord_6167455, baseEnd_6167455] using wordTrace_append hprefix tailTrace_6167455
  have hstable : (prefixWord ++ tailWord_6167455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167455).length < 2 ^ (prefixWord ++ tailWord_6167455).sum := by decide
  have hdescent : baseEnd_6167455 < baseStart_6167455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167461 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_6167461 : Nat := 118140960795 + 6167461 * 2 ^ 59
def prefixEnd_6167461 : Nat := 4983230072969 + 3 ^ 40 * 6167461 * 2
def baseEnd_6167461 : Nat := 3166871910859199514173869

theorem tailTrace_6167461 : CollatzResearch.WordTrace tailWord_6167461 prefixEnd_6167461 3166871910859199514173869 := by
  unfold tailWord_6167461
  simp only [CollatzResearch.WordTrace]
  refine ⟨224945782709349590324942237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149963855139566393549961491 224945782709349590324942237)
  ·
    refine ⟨84354668516006096371853339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224945782709349590324942237 84354668516006096371853339)
    ·
      refine ⟨126532002774009144557780009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84354668516006096371853339 126532002774009144557780009)
      ·
        refine ⟨94899002080506858418335007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126532002774009144557780009 94899002080506858418335007)
        ·
          refine ⟨142348503120760287627502511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94899002080506858418335007 142348503120760287627502511)
          ·
            refine ⟨213522754681140431441253767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142348503120760287627502511 213522754681140431441253767)
            ·
              refine ⟨320284132021710647161880651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213522754681140431441253767 320284132021710647161880651)
              ·
                refine ⟨480426198032565970742820977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320284132021710647161880651 480426198032565970742820977)
                ·
                  refine ⟨360319648524424478057115733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480426198032565970742820977 360319648524424478057115733)
                  ·
                    refine ⟨4222495881145599352231825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 360319648524424478057115733 4222495881145599352231825)
                    ·
                      refine ⟨3166871910859199514173869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222495881145599352231825 3166871910859199514173869)
                      ·
                        rfl

theorem cell23_6167461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_6167461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167461 prefixEnd_6167461 := by exact prefixLift 6167461
  have htrace : WordTrace (prefixWord ++ tailWord_6167461) baseStart_6167461 baseEnd_6167461 := by
    simpa [prefixWord, tailWord_6167461, baseEnd_6167461] using wordTrace_append hprefix tailTrace_6167461
  have hstable : (prefixWord ++ tailWord_6167461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167461).length < 2 ^ (prefixWord ++ tailWord_6167461).sum := by decide
  have hdescent : baseEnd_6167461 < baseStart_6167461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167511 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_6167511 : Nat := 118140960795 + 6167511 * 2 ^ 59
def prefixEnd_6167511 : Nat := 4983230072969 + 3 ^ 40 * 6167511 * 2
def baseEnd_6167511 : Nat := 3166897584891924318548639

theorem tailTrace_6167511 : CollatzResearch.WordTrace tailWord_6167511 prefixEnd_6167511 3166897584891924318548639 := by
  unfold tailWord_6167511
  simp only [CollatzResearch.WordTrace]
  refine ⟨224947606359168448864262387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149965070906112299242841591 224947606359168448864262387)
  ·
    refine ⟨337421409538752673296393581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224947606359168448864262387 337421409538752673296393581)
    ·
      refine ⟨126533028577032252486147593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337421409538752673296393581 126533028577032252486147593)
      ·
        refine ⟨94899771432774189364610695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126533028577032252486147593 94899771432774189364610695)
        ·
          refine ⟨142349657149161284046916043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94899771432774189364610695 142349657149161284046916043)
          ·
            refine ⟨213524485723741926070374065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142349657149161284046916043 213524485723741926070374065)
            ·
              refine ⟨160143364292806444552780549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213524485723741926070374065 160143364292806444552780549)
              ·
                refine ⟨30026880804901208353646353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160143364292806444552780549 30026880804901208353646353)
                ·
                  refine ⟨22520160603675906265234765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30026880804901208353646353 22520160603675906265234765)
                  ·
                    refine ⟨8445060226378464849463037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22520160603675906265234765 8445060226378464849463037)
                    ·
                      refine ⟨3166897584891924318548639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445060226378464849463037 3166897584891924318548639)
                      ·
                        rfl

theorem cell23_6167511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_6167511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167511 prefixEnd_6167511 := by exact prefixLift 6167511
  have htrace : WordTrace (prefixWord ++ tailWord_6167511) baseStart_6167511 baseEnd_6167511 := by
    simpa [prefixWord, tailWord_6167511, baseEnd_6167511] using wordTrace_append hprefix tailTrace_6167511
  have hstable : (prefixWord ++ tailWord_6167511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167511).length < 2 ^ (prefixWord ++ tailWord_6167511).sum := by decide
  have hdescent : baseEnd_6167511 < baseStart_6167511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167548 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_6167548 : Nat := 118140960795 + 6167548 * 2 ^ 59
def prefixEnd_6167548 : Nat := 4983230072969 + 3 ^ 40 * 6167548 * 2
def baseEnd_6167548 : Nat := 1055638861225380224595323

theorem tailTrace_6167548 : CollatzResearch.WordTrace tailWord_6167548 prefixEnd_6167548 1055638861225380224595323 := by
  unfold tailWord_6167548
  simp only [CollatzResearch.WordTrace]
  refine ⟨112474477930017202091679649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149965970573356269455572865 112474477930017202091679649)
  ·
    refine ⟨84355858447512901568759737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112474477930017202091679649 84355858447512901568759737)
    ·
      refine ⟨63266893835634676176569803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84355858447512901568759737 63266893835634676176569803)
      ·
        refine ⟨94900340753452014264854705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63266893835634676176569803 94900340753452014264854705)
        ·
          refine ⟨71175255565089010698641029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94900340753452014264854705 71175255565089010698641029)
          ·
            refine ⟨13345360418454189505995193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71175255565089010698641029 13345360418454189505995193)
            ·
              refine ⟨10009020313840642129496395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13345360418454189505995193 10009020313840642129496395)
              ·
                refine ⟨15013530470760963194244593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10009020313840642129496395 15013530470760963194244593)
                ·
                  refine ⟨11260147853070722395683445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15013530470760963194244593 11260147853070722395683445)
                  ·
                    refine ⟨1055638861225380224595323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11260147853070722395683445 1055638861225380224595323)
                    ·
                      rfl

theorem cell23_6167548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_6167548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167548 prefixEnd_6167548 := by exact prefixLift 6167548
  have htrace : WordTrace (prefixWord ++ tailWord_6167548) baseStart_6167548 baseEnd_6167548 := by
    simpa [prefixWord, tailWord_6167548, baseEnd_6167548] using wordTrace_append hprefix tailTrace_6167548
  have hstable : (prefixWord ++ tailWord_6167548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167548).length < 2 ^ (prefixWord ++ tailWord_6167548).sum := by decide
  have hdescent : baseEnd_6167548 < baseStart_6167548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167571 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3]
def baseStart_6167571 : Nat := 118140960795 + 6167571 * 2 ^ 59
def prefixEnd_6167571 : Nat := 4983230072969 + 3 ^ 40 * 6167571 * 2
def baseEnd_6167571 : Nat := 3166928393731194083798363

theorem tailTrace_6167571 : CollatzResearch.WordTrace tailWord_6167571 prefixEnd_6167571 3166928393731194083798363 := by
  unfold tailWord_6167571
  simp only [CollatzResearch.WordTrace]
  refine ⟨224949794738951079111446567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149966529825967386074297711 224949794738951079111446567)
  ·
    refine ⟨337424692108426618667169851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224949794738951079111446567 337424692108426618667169851)
    ·
      refine ⟨506137038162639928000754777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337424692108426618667169851 506137038162639928000754777)
      ·
        refine ⟨379602778621979946000566083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506137038162639928000754777 379602778621979946000566083)
        ·
          refine ⟨569404167932969919000849125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379602778621979946000566083 569404167932969919000849125)
          ·
            refine ⟨106763281487431859812659211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 569404167932969919000849125 106763281487431859812659211)
            ·
              refine ⟨160144922231147789718988817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106763281487431859812659211 160144922231147789718988817)
              ·
                refine ⟨120108691673360842289241613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160144922231147789718988817 120108691673360842289241613)
                ·
                  refine ⟨45040759377510315858465605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120108691673360842289241613 45040759377510315858465605)
                  ·
                    refine ⟨8445142383283184223462301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45040759377510315858465605 8445142383283184223462301)
                    ·
                      refine ⟨3166928393731194083798363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445142383283184223462301 3166928393731194083798363)
                      ·
                        rfl

theorem cell23_6167571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_6167571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167571 prefixEnd_6167571 := by exact prefixLift 6167571
  have htrace : WordTrace (prefixWord ++ tailWord_6167571) baseStart_6167571 baseEnd_6167571 := by
    simpa [prefixWord, tailWord_6167571, baseEnd_6167571] using wordTrace_append hprefix tailTrace_6167571
  have hstable : (prefixWord ++ tailWord_6167571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167571).length < 2 ^ (prefixWord ++ tailWord_6167571).sum := by decide
  have hdescent : baseEnd_6167571 < baseStart_6167571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167578 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_6167578 : Nat := 118140960795 + 6167578 * 2 ^ 59
def prefixEnd_6167578 : Nat := 4983230072969 + 3 ^ 40 * 6167578 * 2
def baseEnd_6167578 : Nat := 1055643996031925185470277

theorem tailTrace_6167578 : CollatzResearch.WordTrace tailWord_6167578 prefixEnd_6167578 1055643996031925185470277 := by
  unfold tailWord_6167578
  simp only [CollatzResearch.WordTrace]
  refine ⟨56237512512481429826737847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149966700033283812871300925 56237512512481429826737847)
  ·
    refine ⟨84356268768722144740106771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56237512512481429826737847 84356268768722144740106771)
    ·
      refine ⟨126534403153083217110160157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84356268768722144740106771 126534403153083217110160157)
      ·
        refine ⟨47450401182406206416310059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126534403153083217110160157 47450401182406206416310059)
        ·
          refine ⟨71175601773609309624465089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47450401182406206416310059 71175601773609309624465089)
          ·
            refine ⟨53381701330206982218348817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71175601773609309624465089 53381701330206982218348817)
            ·
              refine ⟨40036275997655236663761613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53381701330206982218348817 40036275997655236663761613)
              ·
                refine ⟨15013603499120713748910605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40036275997655236663761613 15013603499120713748910605)
                ·
                  refine ⟨5630101312170267655841477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15013603499120713748910605 5630101312170267655841477)
                  ·
                    refine ⟨1055643996031925185470277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630101312170267655841477 1055643996031925185470277)
                    ·
                      rfl

theorem cell23_6167578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_6167578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167578 prefixEnd_6167578 := by exact prefixLift 6167578
  have htrace : WordTrace (prefixWord ++ tailWord_6167578) baseStart_6167578 baseEnd_6167578 := by
    simpa [prefixWord, tailWord_6167578, baseEnd_6167578] using wordTrace_append hprefix tailTrace_6167578
  have hstable : (prefixWord ++ tailWord_6167578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167578).length < 2 ^ (prefixWord ++ tailWord_6167578).sum := by decide
  have hdescent : baseEnd_6167578 < baseStart_6167578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167585 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6167585 : Nat := 118140960795 + 6167585 * 2 ^ 59
def prefixEnd_6167585 : Nat := 4983230072969 + 3 ^ 40 * 6167585 * 2
def baseEnd_6167585 : Nat := 3166935582460357029023299

theorem tailTrace_6167585 : CollatzResearch.WordTrace tailWord_6167585 prefixEnd_6167585 3166935582460357029023299 := by
  unfold tailWord_6167585
  simp only [CollatzResearch.WordTrace]
  refine ⟨224950305360900359502456209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149966870240600239668304139 224950305360900359502456209)
  ·
    refine ⟨168712729020675269626842157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224950305360900359502456209 168712729020675269626842157)
    ·
      refine ⟨63267273382753226110065809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168712729020675269626842157 63267273382753226110065809)
      ·
        refine ⟨47450455037064919582549357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63267273382753226110065809 47450455037064919582549357)
        ·
          refine ⟨17793920638899344843456009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47450455037064919582549357 17793920638899344843456009)
          ·
            refine ⟨13345440479174508632592007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17793920638899344843456009 13345440479174508632592007)
            ·
              refine ⟨20018160718761762948888011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13345440479174508632592007 20018160718761762948888011)
              ·
                refine ⟨30027241078142644423332017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20018160718761762948888011 30027241078142644423332017)
                ·
                  refine ⟨22520430808606983317499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30027241078142644423332017 22520430808606983317499013)
                  ·
                    refine ⟨4222580776613809372031065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22520430808606983317499013 4222580776613809372031065)
                    ·
                      refine ⟨3166935582460357029023299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222580776613809372031065 3166935582460357029023299)
                      ·
                        rfl

theorem cell23_6167585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6167585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167585 prefixEnd_6167585 := by exact prefixLift 6167585
  have htrace : WordTrace (prefixWord ++ tailWord_6167585) baseStart_6167585 baseEnd_6167585 := by
    simpa [prefixWord, tailWord_6167585, baseEnd_6167585] using wordTrace_append hprefix tailTrace_6167585
  have hstable : (prefixWord ++ tailWord_6167585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167585).length < 2 ^ (prefixWord ++ tailWord_6167585).sum := by decide
  have hdescent : baseEnd_6167585 < baseStart_6167585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167612 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_6167612 : Nat := 118140960795 + 6167612 * 2 ^ 59
def prefixEnd_6167612 : Nat := 4983230072969 + 3 ^ 40 * 6167612 * 2
def baseEnd_6167612 : Nat := 1055649815479342807795225

theorem tailTrace_6167612 : CollatzResearch.WordTrace tailWord_6167612 prefixEnd_6167612 1055649815479342807795225 := by
  unfold tailWord_6167612
  simp only [CollatzResearch.WordTrace]
  refine ⟨112475645065901271556844545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149967526754535028742459393 112475645065901271556844545)
  ·
    refine ⟨84356733799425953667633409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112475645065901271556844545 84356733799425953667633409)
    ·
      refine ⟨63267550349569465250725057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84356733799425953667633409 63267550349569465250725057)
      ·
        refine ⟨47450662762177098938043793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63267550349569465250725057 47450662762177098938043793)
        ·
          refine ⟨35587997071632824203532845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47450662762177098938043793 35587997071632824203532845)
          ·
            refine ⟨13345498901862309076324817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35587997071632824203532845 13345498901862309076324817)
            ·
              refine ⟨10009124176396731807243613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13345498901862309076324817 10009124176396731807243613)
              ·
                refine ⟨3753421566148774427716355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10009124176396731807243613 3753421566148774427716355)
                ·
                  refine ⟨5630132349223161641574533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753421566148774427716355 5630132349223161641574533)
                  ·
                    refine ⟨1055649815479342807795225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630132349223161641574533 1055649815479342807795225)
                    ·
                      rfl

theorem cell23_6167612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_6167612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167612 prefixEnd_6167612 := by exact prefixLift 6167612
  have htrace : WordTrace (prefixWord ++ tailWord_6167612) baseStart_6167612 baseEnd_6167612 := by
    simpa [prefixWord, tailWord_6167612, baseEnd_6167612] using wordTrace_append hprefix tailTrace_6167612
  have hstable : (prefixWord ++ tailWord_6167612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167612).length < 2 ^ (prefixWord ++ tailWord_6167612).sum := by decide
  have hdescent : baseEnd_6167612 < baseStart_6167612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167641 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_6167641 : Nat := 118140960795 + 6167641 * 2 ^ 59
def prefixEnd_6167641 : Nat := 4983230072969 + 3 ^ 40 * 6167641 * 2
def baseEnd_6167641 : Nat := 3166964337377008809923041

theorem tailTrace_6167641 : CollatzResearch.WordTrace tailWord_6167641 prefixEnd_6167641 3166964337377008809923041 := by
  unfold tailWord_6167641
  simp only [CollatzResearch.WordTrace]
  refine ⟨224952347848697481066494777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149968231899131654044329851 224952347848697481066494777)
  ·
    refine ⟨168714260886523110799871083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224952347848697481066494777 168714260886523110799871083)
    ·
      refine ⟨253071391329784666199806625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168714260886523110799871083 253071391329784666199806625)
      ·
        refine ⟨189803543497338499649854969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253071391329784666199806625 189803543497338499649854969)
        ·
          refine ⟨142352657623003874737391227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189803543497338499649854969 142352657623003874737391227)
          ·
            refine ⟨213528986434505812106086841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142352657623003874737391227 213528986434505812106086841)
            ·
              refine ⟨160146739825879359079565131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213528986434505812106086841 160146739825879359079565131)
              ·
                refine ⟨240220109738819038619347697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160146739825879359079565131 240220109738819038619347697)
                ·
                  refine ⟨180165082304114278964510773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240220109738819038619347697 180165082304114278964510773)
                  ·
                    refine ⟨16890476466010713652922885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180165082304114278964510773 16890476466010713652922885)
                    ·
                      refine ⟨3166964337377008809923041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16890476466010713652922885 3166964337377008809923041)
                      ·
                        rfl

theorem cell23_6167641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_6167641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167641 prefixEnd_6167641 := by exact prefixLift 6167641
  have htrace : WordTrace (prefixWord ++ tailWord_6167641) baseStart_6167641 baseEnd_6167641 := by
    simpa [prefixWord, tailWord_6167641, baseEnd_6167641] using wordTrace_append hprefix tailTrace_6167641
  have hstable : (prefixWord ++ tailWord_6167641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167641).length < 2 ^ (prefixWord ++ tailWord_6167641).sum := by decide
  have hdescent : baseEnd_6167641 < baseStart_6167641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167655 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 1, 5]
def baseStart_6167655 : Nat := 118140960795 + 6167655 * 2 ^ 59
def prefixEnd_6167655 : Nat := 4983230072969 + 3 ^ 40 * 6167655 * 2
def baseEnd_6167655 : Nat := 1055657175368723918382659

theorem tailTrace_6167655 : CollatzResearch.WordTrace tailWord_6167655 prefixEnd_6167655 1055657175368723918382659 := by
  unfold tailWord_6167655
  simp only [CollatzResearch.WordTrace]
  refine ⟨224952858470646761457504419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149968572313764507638336279 224952858470646761457504419)
  ·
    refine ⟨337429287705970142186256629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224952858470646761457504419 337429287705970142186256629)
    ·
      refine ⟨31633995722434700829961559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337429287705970142186256629 31633995722434700829961559)
      ·
        refine ⟨47450993583652051244942339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31633995722434700829961559 47450993583652051244942339)
        ·
          refine ⟨71176490375478076867413509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47450993583652051244942339 71176490375478076867413509)
          ·
            refine ⟨13345591945402139412640033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71176490375478076867413509 13345591945402139412640033)
            ·
              refine ⟨10009193959051604559480025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13345591945402139412640033 10009193959051604559480025)
              ·
                refine ⟨7506895469288703419610019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10009193959051604559480025 7506895469288703419610019)
                ·
                  refine ⟨11260343203933055129415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506895469288703419610019 11260343203933055129415029)
                  ·
                    refine ⟨1055657175368723918382659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11260343203933055129415029 1055657175368723918382659)
                    ·
                      rfl

theorem cell23_6167655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_6167655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167655 prefixEnd_6167655 := by exact prefixLift 6167655
  have htrace : WordTrace (prefixWord ++ tailWord_6167655) baseStart_6167655 baseEnd_6167655 := by
    simpa [prefixWord, tailWord_6167655, baseEnd_6167655] using wordTrace_append hprefix tailTrace_6167655
  have hstable : (prefixWord ++ tailWord_6167655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167655).length < 2 ^ (prefixWord ++ tailWord_6167655).sum := by decide
  have hdescent : baseEnd_6167655 < baseStart_6167655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167675 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 5, 2, 2]
def baseStart_6167675 : Nat := 118140960795 + 6167675 * 2 ^ 59
def prefixEnd_6167675 : Nat := 4983230072969 + 3 ^ 40 * 6167675 * 2
def baseEnd_6167675 : Nat := 3166981795719261676897885

theorem tailTrace_6167675 : CollatzResearch.WordTrace tailWord_6167675 prefixEnd_6167675 3166981795719261676897885 := by
  unfold tailWord_6167675
  simp only [CollatzResearch.WordTrace]
  refine ⟨224953587930574304873232479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149969058620382869915488319 224953587930574304873232479)
  ·
    refine ⟨337430381895861457309848719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224953587930574304873232479 337430381895861457309848719)
    ·
      refine ⟨506145572843792185964773079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337430381895861457309848719 506145572843792185964773079)
      ·
        refine ⟨759218359265688278947159619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506145572843792185964773079 759218359265688278947159619)
        ·
          refine ⟨1138827538898532418420739429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759218359265688278947159619 1138827538898532418420739429)
          ·
            refine ⟨213530163543474828453888643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1138827538898532418420739429 213530163543474828453888643)
            ·
              refine ⟨320295245315212242680832965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213530163543474828453888643 320295245315212242680832965)
              ·
                refine ⟨60055358496602295502656181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320295245315212242680832965 60055358496602295502656181)
                ·
                  refine ⟨5630189859056465203374017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60055358496602295502656181 5630189859056465203374017)
                  ·
                    refine ⟨4222642394292348902530513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5630189859056465203374017 4222642394292348902530513)
                    ·
                      refine ⟨3166981795719261676897885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222642394292348902530513 3166981795719261676897885)
                      ·
                        rfl

theorem cell23_6167675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2, 2].length) (baseStart_6167675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167675 prefixEnd_6167675 := by exact prefixLift 6167675
  have htrace : WordTrace (prefixWord ++ tailWord_6167675) baseStart_6167675 baseEnd_6167675 := by
    simpa [prefixWord, tailWord_6167675, baseEnd_6167675] using wordTrace_append hprefix tailTrace_6167675
  have hstable : (prefixWord ++ tailWord_6167675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167675).length < 2 ^ (prefixWord ++ tailWord_6167675).sum := by decide
  have hdescent : baseEnd_6167675 < baseStart_6167675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167698 : List Nat := [3, 2, 3, 1, 1, 2, 1, 10]
def baseStart_6167698 : Nat := 118140960795 + 6167698 * 2 ^ 59
def prefixEnd_6167698 : Nat := 4983230072969 + 3 ^ 40 * 6167698 * 2
def baseEnd_6167698 : Nat := 117296059473122780996677

theorem tailTrace_6167698 : CollatzResearch.WordTrace tailWord_6167698 prefixEnd_6167698 117296059473122780996677 := by
  unfold tailWord_6167698
  simp only [CollatzResearch.WordTrace]
  refine ⟨56238606702372744950329937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149969617872993986534213165 56238606702372744950329937)
  ·
    refine ⟨42178955026779558712747453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56238606702372744950329937 42178955026779558712747453)
    ·
      refine ⟨15817108135042334517280295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42178955026779558712747453 15817108135042334517280295)
      ·
        refine ⟨23725662202563501775920443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15817108135042334517280295 23725662202563501775920443)
        ·
          refine ⟨35588493303845252663880665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23725662202563501775920443 35588493303845252663880665)
          ·
            refine ⟨26691369977883939497910499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35588493303845252663880665 26691369977883939497910499)
            ·
              refine ⟨40037054966825909246865749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26691369977883939497910499 40037054966825909246865749)
              ·
                refine ⟨117296059473122780996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40037054966825909246865749 117296059473122780996677)
                ·
                  rfl

theorem cell23_6167698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_6167698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167698 prefixEnd_6167698 := by exact prefixLift 6167698
  have htrace : WordTrace (prefixWord ++ tailWord_6167698) baseStart_6167698 baseEnd_6167698 := by
    simpa [prefixWord, tailWord_6167698, baseEnd_6167698] using wordTrace_append hprefix tailTrace_6167698
  have hstable : (prefixWord ++ tailWord_6167698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167698).length < 2 ^ (prefixWord ++ tailWord_6167698).sum := by decide
  have hdescent : baseEnd_6167698 < baseStart_6167698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167722 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6167722 : Nat := 118140960795 + 6167722 * 2 ^ 59
def prefixEnd_6167722 : Nat := 4983230072969 + 3 ^ 40 * 6167722 * 2
def baseEnd_6167722 : Nat := 3167005929310022993010169

theorem tailTrace_6167722 : CollatzResearch.WordTrace tailWord_6167722 prefixEnd_6167722 3167005929310022993010169 := by
  unfold tailWord_6167722
  simp only [CollatzResearch.WordTrace]
  refine ⟨56238825540351007975048355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149970201440936021266795613 56238825540351007975048355)
  ·
    refine ⟨84358238310526511962572533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56238825540351007975048355 84358238310526511962572533)
    ·
      refine ⟨7908584841611860496491175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84358238310526511962572533 7908584841611860496491175)
      ·
        refine ⟨11862877262417790744736763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908584841611860496491175 11862877262417790744736763)
        ·
          refine ⟨17794315893626686117105145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862877262417790744736763 17794315893626686117105145)
          ·
            refine ⟨13345736920220014587828859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794315893626686117105145 13345736920220014587828859)
            ·
              refine ⟨20018605380330021881743289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13345736920220014587828859 20018605380330021881743289)
              ·
                refine ⟨15013954035247516411307467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20018605380330021881743289 15013954035247516411307467)
                ·
                  refine ⟨22520931052871274616961201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15013954035247516411307467 22520931052871274616961201)
                  ·
                    refine ⟨16890698289653455962720901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22520931052871274616961201 16890698289653455962720901)
                    ·
                      refine ⟨3167005929310022993010169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16890698289653455962720901 3167005929310022993010169)
                      ·
                        rfl

theorem cell23_6167722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6167722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167722 prefixEnd_6167722 := by exact prefixLift 6167722
  have htrace : WordTrace (prefixWord ++ tailWord_6167722) baseStart_6167722 baseEnd_6167722 := by
    simpa [prefixWord, tailWord_6167722, baseEnd_6167722] using wordTrace_append hprefix tailTrace_6167722
  have hstable : (prefixWord ++ tailWord_6167722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167722).length < 2 ^ (prefixWord ++ tailWord_6167722).sum := by decide
  have hdescent : baseEnd_6167722 < baseStart_6167722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167729 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6167729 : Nat := 118140960795 + 6167729 * 2 ^ 59
def prefixEnd_6167729 : Nat := 4983230072969 + 3 ^ 40 * 6167729 * 2
def baseEnd_6167729 : Nat := 3167009523674604465622637

theorem tailTrace_6167729 : CollatzResearch.WordTrace tailWord_6167729 prefixEnd_6167729 3167009523674604465622637 := by
  unfold tailWord_6167729
  simp only [CollatzResearch.WordTrace]
  refine ⟨224955557472378672095698241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149970371648252448063798827 224955557472378672095698241)
  ·
    refine ⟨168716668104284004071773681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224955557472378672095698241 168716668104284004071773681)
    ·
      refine ⟨126537501078213003053830261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168716668104284004071773681 126537501078213003053830261)
      ·
        refine ⟨11862890726082469036296587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126537501078213003053830261 11862890726082469036296587)
        ·
          refine ⟨17794336089123703554444881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862890726082469036296587 17794336089123703554444881)
          ·
            refine ⟨13345752066842777665833661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794336089123703554444881 13345752066842777665833661)
            ·
              refine ⟨5004657025066041624687623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13345752066842777665833661 5004657025066041624687623)
              ·
                refine ⟨7506985537599062437031435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004657025066041624687623 7506985537599062437031435)
                ·
                  refine ⟨11260478306398593655547153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506985537599062437031435 11260478306398593655547153)
                  ·
                    refine ⟨8445358729798945241660365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11260478306398593655547153 8445358729798945241660365)
                    ·
                      refine ⟨3167009523674604465622637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445358729798945241660365 3167009523674604465622637)
                      ·
                        rfl

theorem cell23_6167729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6167729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167729 prefixEnd_6167729 := by exact prefixLift 6167729
  have htrace : WordTrace (prefixWord ++ tailWord_6167729) baseStart_6167729 baseEnd_6167729 := by
    simpa [prefixWord, tailWord_6167729, baseEnd_6167729] using wordTrace_append hprefix tailTrace_6167729
  have hstable : (prefixWord ++ tailWord_6167729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167729).length < 2 ^ (prefixWord ++ tailWord_6167729).sum := by decide
  have hdescent : baseEnd_6167729 < baseStart_6167729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167745 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6167745 : Nat := 118140960795 + 6167745 * 2 ^ 59
def prefixEnd_6167745 : Nat := 4983230072969 + 3 ^ 40 * 6167745 * 2
def baseEnd_6167745 : Nat := 1055672579788358801007521

theorem tailTrace_6167745 : CollatzResearch.WordTrace tailWord_6167745 prefixEnd_6167745 1055672579788358801007521 := by
  unfold tailWord_6167745
  simp only [CollatzResearch.WordTrace]
  refine ⟨224956141040320706828280689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149970760693547137885520459 224956141040320706828280689)
  ·
    refine ⟨168717105780240530121210517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224956141040320706828280689 168717105780240530121210517)
    ·
      refine ⟨7908614333448774849431743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168717105780240530121210517 7908614333448774849431743)
      ·
        refine ⟨11862921500173162274147615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908614333448774849431743 11862921500173162274147615)
        ·
          refine ⟨17794382250259743411221423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862921500173162274147615 17794382250259743411221423)
          ·
            refine ⟨26691573375389615116832135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17794382250259743411221423 26691573375389615116832135)
            ·
              refine ⟨40037360063084422675248203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26691573375389615116832135 40037360063084422675248203)
              ·
                refine ⟨60056040094626634012872305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40037360063084422675248203 60056040094626634012872305)
                ·
                  refine ⟨45042030070969975509654229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60056040094626634012872305 45042030070969975509654229)
                  ·
                    refine ⟨1055672579788358801007521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45042030070969975509654229 1055672579788358801007521)
                    ·
                      rfl

theorem cell23_6167745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6167745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167745 prefixEnd_6167745 := by exact prefixLift 6167745
  have htrace : WordTrace (prefixWord ++ tailWord_6167745) baseStart_6167745 baseEnd_6167745 := by
    simpa [prefixWord, tailWord_6167745, baseEnd_6167745] using wordTrace_append hprefix tailTrace_6167745
  have hstable : (prefixWord ++ tailWord_6167745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167745).length < 2 ^ (prefixWord ++ tailWord_6167745).sum := by decide
  have hdescent : baseEnd_6167745 < baseStart_6167745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167786 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_6167786 : Nat := 118140960795 + 6167786 * 2 ^ 59
def prefixEnd_6167786 : Nat := 4983230072969 + 3 ^ 40 * 6167786 * 2
def baseEnd_6167786 : Nat := 3167038792071910742609875

theorem tailTrace_6167786 : CollatzResearch.WordTrace tailWord_6167786 prefixEnd_6167786 3167038792071910742609875 := by
  unfold tailWord_6167786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56239409108293042707630803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149971757622114780553682141 56239409108293042707630803)
  ·
    refine ⟨84359113662439564061446205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56239409108293042707630803 84359113662439564061446205)
    ·
      refine ⟨31634667623414836523042327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84359113662439564061446205 31634667623414836523042327)
      ·
        refine ⟨47452001435122254784563491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31634667623414836523042327 47452001435122254784563491)
        ·
          refine ⟨71178002152683382176845237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47452001435122254784563491 71178002152683382176845237)
          ·
            refine ⟨6672937701814067079079241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71178002152683382176845237 6672937701814067079079241)
            ·
              refine ⟨5004703276360550309309431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672937701814067079079241 5004703276360550309309431)
              ·
                refine ⟨7507054914540825463964147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004703276360550309309431 7507054914540825463964147)
                ·
                  refine ⟨11260582371811238195946221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507054914540825463964147 11260582371811238195946221)
                  ·
                    refine ⟨4222718389429214323479833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11260582371811238195946221 4222718389429214323479833)
                    ·
                      refine ⟨3167038792071910742609875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222718389429214323479833 3167038792071910742609875)
                      ·
                        rfl

theorem cell23_6167786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_6167786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167786 prefixEnd_6167786 := by exact prefixLift 6167786
  have htrace : WordTrace (prefixWord ++ tailWord_6167786) baseStart_6167786 baseEnd_6167786 := by
    simpa [prefixWord, tailWord_6167786, baseEnd_6167786] using wordTrace_append hprefix tailTrace_6167786
  have hstable : (prefixWord ++ tailWord_6167786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167786).length < 2 ^ (prefixWord ++ tailWord_6167786).sum := by decide
  have hdescent : baseEnd_6167786 < baseStart_6167786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167816 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_6167816 : Nat := 118140960795 + 6167816 * 2 ^ 59
def prefixEnd_6167816 : Nat := 4983230072969 + 3 ^ 40 * 6167816 * 2
def baseEnd_6167816 : Nat := 3167054196491545625234737

theorem tailTrace_6167816 : CollatzResearch.WordTrace tailWord_6167816 prefixEnd_6167816 3167054196491545625234737 := by
  unfold tailWord_6167816
  simp only [CollatzResearch.WordTrace]
  refine ⟨112479365311531742977057651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149972487082042323969410201 112479365311531742977057651)
  ·
    refine ⟨168719047967297614465586477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112479365311531742977057651 168719047967297614465586477)
    ·
      refine ⟨63269642987736605424594929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168719047967297614465586477 63269642987736605424594929)
      ·
        refine ⟨47452232240802454068446197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63269642987736605424594929 47452232240802454068446197)
        ·
          refine ⟨4448646772575230068916831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47452232240802454068446197 4448646772575230068916831)
          ·
            refine ⟨6672970158862845103375247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448646772575230068916831 6672970158862845103375247)
            ·
              refine ⟨10009455238294267655062871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672970158862845103375247 10009455238294267655062871)
              ·
                refine ⟨15014182857441401482594307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10009455238294267655062871 15014182857441401482594307)
                ·
                  refine ⟨22521274286162102223891461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15014182857441401482594307 22521274286162102223891461)
                  ·
                    refine ⟨4222738928655394166979649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22521274286162102223891461 4222738928655394166979649)
                    ·
                      refine ⟨3167054196491545625234737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222738928655394166979649 3167054196491545625234737)
                      ·
                        rfl

theorem cell23_6167816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_6167816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167816 prefixEnd_6167816 := by exact prefixLift 6167816
  have htrace : WordTrace (prefixWord ++ tailWord_6167816) baseStart_6167816 baseEnd_6167816 := by
    simpa [prefixWord, tailWord_6167816, baseEnd_6167816] using wordTrace_append hprefix tailTrace_6167816
  have hstable : (prefixWord ++ tailWord_6167816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167816).length < 2 ^ (prefixWord ++ tailWord_6167816).sum := by decide
  have hdescent : baseEnd_6167816 < baseStart_6167816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167839 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 5]
def baseStart_6167839 : Nat := 118140960795 + 6167839 * 2 ^ 59
def prefixEnd_6167839 : Nat := 4983230072969 + 3 ^ 40 * 6167839 * 2
def baseEnd_6167839 : Nat := 351896222949622115027459

theorem tailTrace_6167839 : CollatzResearch.WordTrace tailWord_6167839 prefixEnd_6167839 351896222949622115027459 := by
  unfold tailWord_6167839
  simp only [CollatzResearch.WordTrace]
  refine ⟨224959569501980160882202571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149973046334653440588135047 224959569501980160882202571)
  ·
    refine ⟨337439354252970241323303857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224959569501980160882202571 337439354252970241323303857)
    ·
      refine ⟨253079515689727680992477893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337439354252970241323303857 253079515689727680992477893)
      ·
        refine ⟨47452409191823940186089605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253079515689727680992477893 47452409191823940186089605)
        ·
          refine ⟨8897326723466988784891801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47452409191823940186089605 8897326723466988784891801)
          ·
            refine ⟨6672995042600241588668851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8897326723466988784891801 6672995042600241588668851)
            ·
              refine ⟨10009492563900362383003277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672995042600241588668851 10009492563900362383003277)
              ·
                refine ⟨3753559711462635893626229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10009492563900362383003277 3753559711462635893626229)
                ·
                  refine ⟨351896222949622115027459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753559711462635893626229 351896222949622115027459)
                  ·
                    rfl

theorem cell23_6167839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 5].length) (baseStart_6167839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167839 prefixEnd_6167839 := by exact prefixLift 6167839
  have htrace : WordTrace (prefixWord ++ tailWord_6167839) baseStart_6167839 baseEnd_6167839 := by
    simpa [prefixWord, tailWord_6167839, baseEnd_6167839] using wordTrace_append hprefix tailTrace_6167839
  have hstable : (prefixWord ++ tailWord_6167839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167839).length < 2 ^ (prefixWord ++ tailWord_6167839).sum := by decide
  have hdescent : baseEnd_6167839 < baseStart_6167839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167875 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3]
def baseStart_6167875 : Nat := 118140960795 + 6167875 * 2 ^ 59
def prefixEnd_6167875 : Nat := 4983230072969 + 3 ^ 40 * 6167875 * 2
def baseEnd_6167875 : Nat := 3167084491850160894396965

theorem tailTrace_6167875 : CollatzResearch.WordTrace tailWord_6167875 prefixEnd_6167875 3167084491850160894396965 := by
  unfold tailWord_6167875
  simp only [CollatzResearch.WordTrace]
  refine ⟨224960882529849739030513079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149973921686566492687008719 224960882529849739030513079)
  ·
    refine ⟨337441323794774608545769619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224960882529849739030513079 337441323794774608545769619)
    ·
      refine ⟨506161985692161912818654429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337441323794774608545769619 506161985692161912818654429)
      ·
        refine ⟨189810744634560717306995411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506161985692161912818654429 189810744634560717306995411)
        ·
          refine ⟨284716116951841075960493117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189810744634560717306995411 284716116951841075960493117)
          ·
            refine ⟨106768543856940403485184919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284716116951841075960493117 106768543856940403485184919)
            ·
              refine ⟨160152815785410605227777379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106768543856940403485184919 160152815785410605227777379)
              ·
                refine ⟨240229223678115907841666069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160152815785410605227777379 240229223678115907841666069)
                ·
                  refine ⟨11260744859911683180078097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240229223678115907841666069 11260744859911683180078097)
                  ·
                    refine ⟨8445558644933762385058573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11260744859911683180078097 8445558644933762385058573)
                    ·
                      refine ⟨3167084491850160894396965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445558644933762385058573 3167084491850160894396965)
                      ·
                        rfl

theorem cell23_6167875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_6167875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167875 prefixEnd_6167875 := by exact prefixLift 6167875
  have htrace : WordTrace (prefixWord ++ tailWord_6167875) baseStart_6167875 baseEnd_6167875 := by
    simpa [prefixWord, tailWord_6167875, baseEnd_6167875] using wordTrace_append hprefix tailTrace_6167875
  have hstable : (prefixWord ++ tailWord_6167875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167875).length < 2 ^ (prefixWord ++ tailWord_6167875).sum := by decide
  have hdescent : baseEnd_6167875 < baseStart_6167875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167916 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_6167916 : Nat := 118140960795 + 6167916 * 2 ^ 59
def prefixEnd_6167916 : Nat := 4983230072969 + 3 ^ 40 * 6167916 * 2
def baseEnd_6167916 : Nat := 1055701848185665077994759

theorem tailTrace_6167916 : CollatzResearch.WordTrace tailWord_6167916 prefixEnd_6167916 1055701848185665077994759 := by
  unfold tailWord_6167916
  simp only [CollatzResearch.WordTrace]
  refine ⟨112481188961350601516377801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149974918615134135355170401 112481188961350601516377801)
  ·
    refine ⟨84360891721012951137283351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112481188961350601516377801 84360891721012951137283351)
    ·
      refine ⟨126541337581519426705925027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84360891721012951137283351 126541337581519426705925027)
      ·
        refine ⟨189812006372279140058887541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126541337581519426705925027 189812006372279140058887541)
        ·
          refine ⟨17794875597401169380520707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189812006372279140058887541 17794875597401169380520707)
          ·
            refine ⟨26692313396101754070781061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17794875597401169380520707 26692313396101754070781061)
            ·
              refine ⟨5004808761769078888271449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26692313396101754070781061 5004808761769078888271449)
              ·
                refine ⟨3753606571326809166203587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004808761769078888271449 3753606571326809166203587)
                ·
                  refine ⟨5630409856990213749305381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753606571326809166203587 5630409856990213749305381)
                  ·
                    refine ⟨1055701848185665077994759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630409856990213749305381 1055701848185665077994759)
                    ·
                      rfl

theorem cell23_6167916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_6167916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167916 prefixEnd_6167916 := by exact prefixLift 6167916
  have htrace : WordTrace (prefixWord ++ tailWord_6167916) baseStart_6167916 baseEnd_6167916 := by
    simpa [prefixWord, tailWord_6167916, baseEnd_6167916] using wordTrace_append hprefix tailTrace_6167916
  have hstable : (prefixWord ++ tailWord_6167916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167916).length < 2 ^ (prefixWord ++ tailWord_6167916).sum := by decide
  have hdescent : baseEnd_6167916 < baseStart_6167916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167932 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_6167932 : Nat := 118140960795 + 6167932 * 2 ^ 59
def prefixEnd_6167932 : Nat := 4983230072969 + 3 ^ 40 * 6167932 * 2
def baseEnd_6167932 : Nat := 3167113760247467171384203

theorem tailTrace_6167932 : CollatzResearch.WordTrace tailWord_6167932 prefixEnd_6167932 3167113760247467171384203 := by
  unfold tailWord_6167932
  simp only [CollatzResearch.WordTrace]
  refine ⟨112481480745321618882669025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149975307660428825176892033 112481480745321618882669025)
  ·
    refine ⟨84361110558991214162001769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112481480745321618882669025 84361110558991214162001769)
    ·
      refine ⟨63270832919243410621501327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84361110558991214162001769 63270832919243410621501327)
      ·
        refine ⟨94906249378865115932251991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63270832919243410621501327 94906249378865115932251991)
        ·
          refine ⟨142359374068297673898377987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94906249378865115932251991 142359374068297673898377987)
          ·
            refine ⟨213539061102446510847566981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142359374068297673898377987 213539061102446510847566981)
            ·
              refine ⟨40038573956708720783918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213539061102446510847566981 40038573956708720783918809)
              ·
                refine ⟨30028930467531540587939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40038573956708720783918809 30028930467531540587939107)
                ·
                  refine ⟨45043395701297310881908661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30028930467531540587939107 45043395701297310881908661)
                  ·
                    refine ⟨4222818346996622895178937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45043395701297310881908661 4222818346996622895178937)
                    ·
                      refine ⟨3167113760247467171384203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222818346996622895178937 3167113760247467171384203)
                      ·
                        rfl

theorem cell23_6167932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_6167932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167932 prefixEnd_6167932 := by exact prefixLift 6167932
  have htrace : WordTrace (prefixWord ++ tailWord_6167932) baseStart_6167932 baseEnd_6167932 := by
    simpa [prefixWord, tailWord_6167932, baseEnd_6167932] using wordTrace_append hprefix tailTrace_6167932
  have hstable : (prefixWord ++ tailWord_6167932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167932).length < 2 ^ (prefixWord ++ tailWord_6167932).sum := by decide
  have hdescent : baseEnd_6167932 < baseStart_6167932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167939 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 3]
def baseStart_6167939 : Nat := 118140960795 + 6167939 * 2 ^ 59
def prefixEnd_6167939 : Nat := 4983230072969 + 3 ^ 40 * 6167939 * 2
def baseEnd_6167939 : Nat := 3167117354612048643996671

theorem tailTrace_6167939 : CollatzResearch.WordTrace tailWord_6167939 prefixEnd_6167939 3167117354612048643996671 := by
  unfold tailWord_6167939
  simp only [CollatzResearch.WordTrace]
  refine ⟨224963216801617877960842871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149975477867745251973895247 224963216801617877960842871)
  ·
    refine ⟨337444825202426816941264307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224963216801617877960842871 337444825202426816941264307)
    ·
      refine ⟨506167237803640225411896461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337444825202426816941264307 506167237803640225411896461)
      ·
        refine ⟨189812714176365084529461173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506167237803640225411896461 189812714176365084529461173)
        ·
          refine ⟨17794941954034226674636985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189812714176365084529461173 17794941954034226674636985)
          ·
            refine ⟨13346206465525670005977739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794941954034226674636985 13346206465525670005977739)
            ·
              refine ⟨20019309698288505008966609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13346206465525670005977739 20019309698288505008966609)
              ·
                refine ⟨15014482273716378756724957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20019309698288505008966609 15014482273716378756724957)
                ·
                  refine ⟨5630430852643642033771859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15014482273716378756724957 5630430852643642033771859)
                  ·
                    refine ⟨8445646278965463050657789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630430852643642033771859 8445646278965463050657789)
                    ·
                      refine ⟨3167117354612048643996671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445646278965463050657789 3167117354612048643996671)
                      ·
                        rfl

theorem cell23_6167939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_6167939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167939 prefixEnd_6167939 := by exact prefixLift 6167939
  have htrace : WordTrace (prefixWord ++ tailWord_6167939) baseStart_6167939 baseEnd_6167939 := by
    simpa [prefixWord, tailWord_6167939, baseEnd_6167939] using wordTrace_append hprefix tailTrace_6167939
  have hstable : (prefixWord ++ tailWord_6167939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167939).length < 2 ^ (prefixWord ++ tailWord_6167939).sum := by decide
  have hdescent : baseEnd_6167939 < baseStart_6167939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167985 : List Nat := [1, 2, 2, 4, 1, 1, 2, 10]
def baseStart_6167985 : Nat := 118140960795 + 6167985 * 2 ^ 59
def prefixEnd_6167985 : Nat := 4983230072969 + 3 ^ 40 * 6167985 * 2
def baseEnd_6167985 : Nat := 117301517582302054223017

theorem tailTrace_6167985 : CollatzResearch.WordTrace tailWord_6167985 prefixEnd_6167985 117301517582302054223017 := by
  unfold tailWord_6167985
  simp only [CollatzResearch.WordTrace]
  refine ⟨224964894559451227817017409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149976596372967485211344939 224964894559451227817017409)
  ·
    refine ⟨168723670919588420862763057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224964894559451227817017409 168723670919588420862763057)
    ·
      refine ⟨126542753189691315647072293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168723670919588420862763057 126542753189691315647072293)
      ·
        refine ⟨23726766223067121683826055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126542753189691315647072293 23726766223067121683826055)
        ·
          refine ⟨35590149334600682525739083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23726766223067121683826055 35590149334600682525739083)
          ·
            refine ⟨53385224001901023788608625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35590149334600682525739083 53385224001901023788608625)
            ·
              refine ⟨40038918001425767841456469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53385224001901023788608625 40038918001425767841456469)
              ·
                refine ⟨117301517582302054223017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40038918001425767841456469 117301517582302054223017)
                ·
                  rfl

theorem cell23_6167985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 10].length) (baseStart_6167985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167985 prefixEnd_6167985 := by exact prefixLift 6167985
  have htrace : WordTrace (prefixWord ++ tailWord_6167985) baseStart_6167985 baseEnd_6167985 := by
    simpa [prefixWord, tailWord_6167985, baseEnd_6167985] using wordTrace_append hprefix tailTrace_6167985
  have hstable : (prefixWord ++ tailWord_6167985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167985).length < 2 ^ (prefixWord ++ tailWord_6167985).sum := by decide
  have hdescent : baseEnd_6167985 < baseStart_6167985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167989 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6167989 : Nat := 118140960795 + 6167989 * 2 ^ 59
def prefixEnd_6167989 : Nat := 4983230072969 + 3 ^ 40 * 6167989 * 2
def baseEnd_6167989 : Nat := 1055714342881591149457147

theorem tailTrace_6167989 : CollatzResearch.WordTrace tailWord_6167989 prefixEnd_6167989 1055714342881591149457147 := by
  unfold tailWord_6167989
  simp only [CollatzResearch.WordTrace]
  refine ⟨224965040451436736500163021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149976693634291157666775347 224965040451436736500163021)
  ·
    refine ⟨84361890169288776187561133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224965040451436736500163021 84361890169288776187561133)
    ·
      refine ⟨31635708813483291070335425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84361890169288776187561133 31635708813483291070335425)
      ·
        refine ⟨23726781610112468302751569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31635708813483291070335425 23726781610112468302751569)
        ·
          refine ⟨17795086207584351227063677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23726781610112468302751569 17795086207584351227063677)
          ·
            refine ⟨6673157327844131710148879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17795086207584351227063677 6673157327844131710148879)
            ·
              refine ⟨10009735991766197565223319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6673157327844131710148879 10009735991766197565223319)
              ·
                refine ⟨15014603987649296347834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10009735991766197565223319 15014603987649296347834979)
                ·
                  refine ⟨22521905981473944521752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15014603987649296347834979 22521905981473944521752469)
                  ·
                    refine ⟨1055714342881591149457147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22521905981473944521752469 1055714342881591149457147)
                    ·
                      rfl

theorem cell23_6167989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6167989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167989 prefixEnd_6167989 := by exact prefixLift 6167989
  have htrace : WordTrace (prefixWord ++ tailWord_6167989) baseStart_6167989 baseEnd_6167989 := by
    simpa [prefixWord, tailWord_6167989, baseEnd_6167989] using wordTrace_append hprefix tailTrace_6167989
  have hstable : (prefixWord ++ tailWord_6167989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167989).length < 2 ^ (prefixWord ++ tailWord_6167989).sum := by decide
  have hdescent : baseEnd_6167989 < baseStart_6167989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167992 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_6167992 : Nat := 118140960795 + 6167992 * 2 ^ 59
def prefixEnd_6167992 : Nat := 4983230072969 + 3 ^ 40 * 6167992 * 2
def baseEnd_6167992 : Nat := 3167144569086736936633927

theorem tailTrace_6167992 : CollatzResearch.WordTrace tailWord_6167992 prefixEnd_6167992 3167144569086736936633927 := by
  unfold tailWord_6167992
  simp only [CollatzResearch.WordTrace]
  refine ⟨112482574935212934006261115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149976766580283912008348153 112482574935212934006261115)
  ·
    refine ⟨168723862402819401009391673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112482574935212934006261115 168723862402819401009391673)
    ·
      refine ⟨126542896802114550757043755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168723862402819401009391673 126542896802114550757043755)
      ·
        refine ⟨189814345203171826135565633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126542896802114550757043755 189814345203171826135565633)
        ·
          refine ⟨142360758902378869601674225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189814345203171826135565633 142360758902378869601674225)
          ·
            refine ⟨106770569176784152201255669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142360758902378869601674225 106770569176784152201255669)
            ·
              refine ⟨10009740860323514268867719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106770569176784152201255669 10009740860323514268867719)
              ·
                refine ⟨15014611290485271403301579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10009740860323514268867719 15014611290485271403301579)
                ·
                  refine ⟨22521916935727907104952369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15014611290485271403301579 22521916935727907104952369)
                  ·
                    refine ⟨16891437701795930328714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22521916935727907104952369 16891437701795930328714277)
                    ·
                      refine ⟨3167144569086736936633927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16891437701795930328714277 3167144569086736936633927)
                      ·
                        rfl

theorem cell23_6167992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_6167992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167992 prefixEnd_6167992 := by exact prefixLift 6167992
  have htrace : WordTrace (prefixWord ++ tailWord_6167992) baseStart_6167992 baseEnd_6167992 := by
    simpa [prefixWord, tailWord_6167992, baseEnd_6167992] using wordTrace_append hprefix tailTrace_6167992
  have hstable : (prefixWord ++ tailWord_6167992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167992).length < 2 ^ (prefixWord ++ tailWord_6167992).sum := by decide
  have hdescent : baseEnd_6167992 < baseStart_6167992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6167996 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6167996 : Nat := 118140960795 + 6167996 * 2 ^ 59
def prefixEnd_6167996 : Nat := 4983230072969 + 3 ^ 40 * 6167996 * 2
def baseEnd_6167996 : Nat := 3167146623009354920983909

theorem tailTrace_6167996 : CollatzResearch.WordTrace tailWord_6167996 prefixEnd_6167996 3167146623009354920983909 := by
  unfold tailWord_6167996
  simp only [CollatzResearch.WordTrace]
  refine ⟨112482647881205688347833921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149976863841607584463778561 112482647881205688347833921)
  ·
    refine ⟨84361985910904266260875441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112482647881205688347833921 84361985910904266260875441)
    ·
      refine ⟨63271489433178199695656581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84361985910904266260875441 63271489433178199695656581)
      ·
        refine ⟨11863404268720912442935609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63271489433178199695656581 11863404268720912442935609)
        ·
          refine ⟨8897553201540684332201707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11863404268720912442935609 8897553201540684332201707)
          ·
            refine ⟨13346329802311026498302561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8897553201540684332201707 13346329802311026498302561)
            ·
              refine ⟨10009747351733269873726921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13346329802311026498302561 10009747351733269873726921)
              ·
                refine ⟨7507310513799952405295191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10009747351733269873726921 7507310513799952405295191)
                ·
                  refine ⟨11260965770699928607942787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507310513799952405295191 11260965770699928607942787)
                  ·
                    refine ⟨16891448656049892911914181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11260965770699928607942787 16891448656049892911914181)
                    ·
                      refine ⟨3167146623009354920983909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16891448656049892911914181 3167146623009354920983909)
                      ·
                        rfl

theorem cell23_6167996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6167996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6167996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6167996 prefixEnd_6167996 := by exact prefixLift 6167996
  have htrace : WordTrace (prefixWord ++ tailWord_6167996) baseStart_6167996 baseEnd_6167996 := by
    simpa [prefixWord, tailWord_6167996, baseEnd_6167996] using wordTrace_append hprefix tailTrace_6167996
  have hstable : (prefixWord ++ tailWord_6167996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6167996).length < 2 ^ (prefixWord ++ tailWord_6167996).sum := by decide
  have hdescent : baseEnd_6167996 < baseStart_6167996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6167996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168046 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_6168046 : Nat := 118140960795 + 6168046 * 2 ^ 59
def prefixEnd_6168046 : Nat := 4983230072969 + 3 ^ 40 * 6168046 * 2
def baseEnd_6168046 : Nat := 3167172297042079725358679

theorem tailTrace_6168046 : CollatzResearch.WordTrace tailWord_6168046 prefixEnd_6168046 3167172297042079725358679 := by
  unfold tailWord_6168046
  simp only [CollatzResearch.WordTrace]
  refine ⟨28120889926528779404373499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149978079608153490156658661 28120889926528779404373499)
  ·
    refine ⟨42181334889793169106560249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28120889926528779404373499 42181334889793169106560249)
    ·
      refine ⟨31636001167344876829920187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42181334889793169106560249 31636001167344876829920187)
      ·
        refine ⟨47454001751017315244880281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31636001167344876829920187 47454001751017315244880281)
        ·
          refine ⟨35590501313262986433660211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47454001751017315244880281 35590501313262986433660211)
          ·
            refine ⟨53385751969894479650490317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35590501313262986433660211 53385751969894479650490317)
            ·
              refine ⟨20019656988710429868933869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53385751969894479650490317 20019656988710429868933869)
              ·
                refine ⟨7507371370766411200850201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20019656988710429868933869 7507371370766411200850201)
                ·
                  refine ⟨5630528528074808400637651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7507371370766411200850201 5630528528074808400637651)
                  ·
                    refine ⟨8445792792112212600956477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630528528074808400637651 8445792792112212600956477)
                    ·
                      refine ⟨3167172297042079725358679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8445792792112212600956477 3167172297042079725358679)
                      ·
                        rfl

theorem cell23_6168046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_6168046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168046 prefixEnd_6168046 := by exact prefixLift 6168046
  have htrace : WordTrace (prefixWord ++ tailWord_6168046) baseStart_6168046 baseEnd_6168046 := by
    simpa [prefixWord, tailWord_6168046, baseEnd_6168046] using wordTrace_append hprefix tailTrace_6168046
  have hstable : (prefixWord ++ tailWord_6168046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168046).length < 2 ^ (prefixWord ++ tailWord_6168046).sum := by decide
  have hdescent : baseEnd_6168046 < baseStart_6168046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168056 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_6168056 : Nat := 118140960795 + 6168056 * 2 ^ 59
def prefixEnd_6168056 : Nat := 4983230072969 + 3 ^ 40 * 6168056 * 2
def baseEnd_6168056 : Nat := 3167177431848624686233633

theorem tailTrace_6168056 : CollatzResearch.WordTrace tailWord_6168056 prefixEnd_6168056 3167177431848624686233633 := by
  unfold tailWord_6168056
  simp only [CollatzResearch.WordTrace]
  refine ⟨112483742071097003471426011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149978322761462671295234681 112483742071097003471426011)
  ·
    refine ⟨168725613106645505207139017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112483742071097003471426011 168725613106645505207139017)
    ·
      refine ⟨126544209829984128905354263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168725613106645505207139017 126544209829984128905354263)
      ·
        refine ⟨189816314744976193358031395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126544209829984128905354263 189816314744976193358031395)
        ·
          refine ⟨284724472117464290037047093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189816314744976193358031395 284724472117464290037047093)
          ·
            refine ⟨26692919261012277190973165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284724472117464290037047093 26692919261012277190973165)
            ·
              refine ⟨10009844722879603946614937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26692919261012277190973165 10009844722879603946614937)
              ·
                refine ⟨7507383542159702959961203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10009844722879603946614937 7507383542159702959961203)
                ·
                  refine ⟨11261075313239554439941805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507383542159702959961203 11261075313239554439941805)
                  ·
                    refine ⟨4222903242464832914978177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11261075313239554439941805 4222903242464832914978177)
                    ·
                      refine ⟨3167177431848624686233633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4222903242464832914978177 3167177431848624686233633)
                      ·
                        rfl

theorem cell23_6168056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_6168056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168056 prefixEnd_6168056 := by exact prefixLift 6168056
  have htrace : WordTrace (prefixWord ++ tailWord_6168056) baseStart_6168056 baseEnd_6168056 := by
    simpa [prefixWord, tailWord_6168056, baseEnd_6168056] using wordTrace_append hprefix tailTrace_6168056
  have hstable : (prefixWord ++ tailWord_6168056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168056).length < 2 ^ (prefixWord ++ tailWord_6168056).sum := by decide
  have hdescent : baseEnd_6168056 < baseStart_6168056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168072 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6168072 : Nat := 118140960795 + 6168072 * 2 ^ 59
def prefixEnd_6168072 : Nat := 4983230072969 + 3 ^ 40 * 6168072 * 2
def baseEnd_6168072 : Nat := 3167185647539096623633559

theorem tailTrace_6168072 : CollatzResearch.WordTrace tailWord_6168072 prefixEnd_6168072 3167185647539096623633559 := by
  unfold tailWord_6168072
  simp only [CollatzResearch.WordTrace]
  refine ⟨112484033855068020837717235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149978711806757361116956313 112484033855068020837717235)
  ·
    refine ⟨168726050782602031256575853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112484033855068020837717235 168726050782602031256575853)
    ·
      refine ⟨63272269043475761721215945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168726050782602031256575853 63272269043475761721215945)
      ·
        refine ⟨47454201782606821290911959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63272269043475761721215945 47454201782606821290911959)
        ·
          refine ⟨71181302673910231936367939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47454201782606821290911959 71181302673910231936367939)
          ·
            refine ⟨106771954010865347904551909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71181302673910231936367939 106771954010865347904551909)
            ·
              refine ⟨20019741377037252732103483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106771954010865347904551909 20019741377037252732103483)
              ·
                refine ⟨30029612065555879098155225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20019741377037252732103483 30029612065555879098155225)
                ·
                  refine ⟨22522209049166909323616419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30029612065555879098155225 22522209049166909323616419)
                  ·
                    refine ⟨33783313573750363985424629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22522209049166909323616419 33783313573750363985424629)
                    ·
                      refine ⟨3167185647539096623633559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33783313573750363985424629 3167185647539096623633559)
                      ·
                        rfl

theorem cell23_6168072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6168072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168072 prefixEnd_6168072 := by exact prefixLift 6168072
  have htrace : WordTrace (prefixWord ++ tailWord_6168072) baseStart_6168072 baseEnd_6168072 := by
    simpa [prefixWord, tailWord_6168072, baseEnd_6168072] using wordTrace_append hprefix tailTrace_6168072
  have hstable : (prefixWord ++ tailWord_6168072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168072).length < 2 ^ (prefixWord ++ tailWord_6168072).sum := by decide
  have hdescent : baseEnd_6168072 < baseStart_6168072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168092 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 7]
def baseStart_6168092 : Nat := 118140960795 + 6168092 * 2 ^ 59
def prefixEnd_6168092 : Nat := 4983230072969 + 3 ^ 40 * 6168092 * 2
def baseEnd_6168092 : Nat := 351910657461354060598163

theorem tailTrace_6168092 : CollatzResearch.WordTrace tailWord_6168092 prefixEnd_6168092 351910657461354060598163 := by
  unfold tailWord_6168092
  simp only [CollatzResearch.WordTrace]
  refine ⟨112484398585031792545581265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149979198113375723394108353 112484398585031792545581265)
  ·
    refine ⟨84363298938773844409185949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112484398585031792545581265 84363298938773844409185949)
    ·
      refine ⟨31636237102040191653444731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84363298938773844409185949 31636237102040191653444731)
      ·
        refine ⟨47454355653060287480167097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31636237102040191653444731 47454355653060287480167097)
        ·
          refine ⟨35590766739795215610125323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47454355653060287480167097 35590766739795215610125323)
          ·
            refine ⟨53386150109692823415187985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35590766739795215610125323 53386150109692823415187985)
            ·
              refine ⟨40039612582269617561390989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53386150109692823415187985 40039612582269617561390989)
              ·
                refine ⟨15014854718351106585521621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40039612582269617561390989 15014854718351106585521621)
                ·
                  refine ⟨351910657461354060598163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15014854718351106585521621 351910657461354060598163)
                  ·
                    rfl

theorem cell23_6168092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_6168092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168092 prefixEnd_6168092 := by exact prefixLift 6168092
  have htrace : WordTrace (prefixWord ++ tailWord_6168092) baseStart_6168092 baseEnd_6168092 := by
    simpa [prefixWord, tailWord_6168092, baseEnd_6168092] using wordTrace_append hprefix tailTrace_6168092
  have hstable : (prefixWord ++ tailWord_6168092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168092).length < 2 ^ (prefixWord ++ tailWord_6168092).sum := by decide
  have hdescent : baseEnd_6168092 < baseStart_6168092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168099 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4]
def baseStart_6168099 : Nat := 118140960795 + 6168099 * 2 ^ 59
def prefixEnd_6168099 : Nat := 4983230072969 + 3 ^ 40 * 6168099 * 2
def baseEnd_6168099 : Nat := 3167199511516768017995935

theorem tailTrace_6168099 : CollatzResearch.WordTrace tailWord_6168099 prefixEnd_6168099 3167199511516768017995935 := by
  unfold tailWord_6168099
  simp only [CollatzResearch.WordTrace]
  refine ⟨224969052481038225286667351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149979368320692150191111567 224969052481038225286667351)
  ·
    refine ⟨337453578721557337930001027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224969052481038225286667351 337453578721557337930001027)
    ·
      refine ⟨506180368082336006895001541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337453578721557337930001027 506180368082336006895001541)
      ·
        refine ⟨94908819015438001292812789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506180368082336006895001541 94908819015438001292812789)
        ·
          refine ⟨8897701782697312621201199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94908819015438001292812789 8897701782697312621201199)
          ·
            refine ⟨13346552674045968931801799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8897701782697312621201199 13346552674045968931801799)
            ·
              refine ⟨20019829011068953397702699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13346552674045968931801799 20019829011068953397702699)
              ·
                refine ⟨30029743516603430096554049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20019829011068953397702699 30029743516603430096554049)
                ·
                  refine ⟨22522307637452572572415537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30029743516603430096554049 22522307637452572572415537)
                  ·
                    refine ⟨16891730728089429429311653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22522307637452572572415537 16891730728089429429311653)
                    ·
                      refine ⟨3167199511516768017995935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16891730728089429429311653 3167199511516768017995935)
                      ·
                        rfl

theorem cell23_6168099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_6168099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168099 prefixEnd_6168099 := by exact prefixLift 6168099
  have htrace : WordTrace (prefixWord ++ tailWord_6168099) baseStart_6168099 baseEnd_6168099 := by
    simpa [prefixWord, tailWord_6168099, baseEnd_6168099] using wordTrace_append hprefix tailTrace_6168099
  have hstable : (prefixWord ++ tailWord_6168099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168099).length < 2 ^ (prefixWord ++ tailWord_6168099).sum := by decide
  have hdescent : baseEnd_6168099 < baseStart_6168099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168122 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_6168122 : Nat := 118140960795 + 6168122 * 2 ^ 59
def prefixEnd_6168122 : Nat := 4983230072969 + 3 ^ 40 * 6168122 * 2
def baseEnd_6168122 : Nat := 1055737107190607142669443

theorem tailTrace_6168122 : CollatzResearch.WordTrace tailWord_6168122 prefixEnd_6168122 1055737107190607142669443 := by
  unfold tailWord_6168122
  simp only [CollatzResearch.WordTrace]
  refine ⟨56242472839988725053688655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149979927573303266809836413 56242472839988725053688655)
  ·
    refine ⟨84363709259983087580532983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56242472839988725053688655 84363709259983087580532983)
    ·
      refine ⟨126545563889974631370799475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84363709259983087580532983 126545563889974631370799475)
      ·
        refine ⟨189818345834961947056199213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126545563889974631370799475 189818345834961947056199213)
        ·
          refine ⟨71181879688110730146074705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189818345834961947056199213 71181879688110730146074705)
          ·
            refine ⟨53386409766083047609556029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71181879688110730146074705 53386409766083047609556029)
            ·
              refine ⟨20019903662281142853583511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53386409766083047609556029 20019903662281142853583511)
              ·
                refine ⟨30029855493421714280375267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20019903662281142853583511 30029855493421714280375267)
                ·
                  refine ⟨45044783240132571420562901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30029855493421714280375267 45044783240132571420562901)
                  ·
                    refine ⟨1055737107190607142669443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45044783240132571420562901 1055737107190607142669443)
                    ·
                      rfl

theorem cell23_6168122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_6168122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168122 prefixEnd_6168122 := by exact prefixLift 6168122
  have htrace : WordTrace (prefixWord ++ tailWord_6168122) baseStart_6168122 baseEnd_6168122 := by
    simpa [prefixWord, tailWord_6168122, baseEnd_6168122] using wordTrace_append hprefix tailTrace_6168122
  have hstable : (prefixWord ++ tailWord_6168122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168122).length < 2 ^ (prefixWord ++ tailWord_6168122).sum := by decide
  have hdescent : baseEnd_6168122 < baseStart_6168122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168169 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_6168169 : Nat := 118140960795 + 6168169 * 2 ^ 59
def prefixEnd_6168169 : Nat := 4983230072969 + 3 ^ 40 * 6168169 * 2
def baseEnd_6168169 : Nat := 1055745151720860914706871

theorem tailTrace_6168169 : CollatzResearch.WordTrace tailWord_6168169 prefixEnd_6168169 1055745151720860914706871 := by
  unfold tailWord_6168169
  simp only [CollatzResearch.WordTrace]
  refine ⟨224971605590784627241715561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149981070393856418161143707 224971605590784627241715561)
  ·
    refine ⟨168728704193088470431286671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224971605590784627241715561 168728704193088470431286671)
    ·
      refine ⟨253093056289632705646930007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168728704193088470431286671 253093056289632705646930007)
      ·
        refine ⟨379639584434449058470395011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253093056289632705646930007 379639584434449058470395011)
        ·
          refine ⟨569459376651673587705592517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379639584434449058470395011 569459376651673587705592517)
          ·
            refine ⟨106773633122188797694798597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 569459376651673587705592517 106773633122188797694798597)
            ·
              refine ⟨20020056210410399567774737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106773633122188797694798597 20020056210410399567774737)
              ·
                refine ⟨15015042157807799675831053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20020056210410399567774737 15015042157807799675831053)
                ·
                  refine ⟨5630640809177924878436645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15015042157807799675831053 5630640809177924878436645)
                  ·
                    refine ⟨1055745151720860914706871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630640809177924878436645 1055745151720860914706871)
                    ·
                      rfl

theorem cell23_6168169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_6168169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168169 prefixEnd_6168169 := by exact prefixLift 6168169
  have htrace : WordTrace (prefixWord ++ tailWord_6168169) baseStart_6168169 baseEnd_6168169 := by
    simpa [prefixWord, tailWord_6168169, baseEnd_6168169] using wordTrace_append hprefix tailTrace_6168169
  have hstable : (prefixWord ++ tailWord_6168169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168169).length < 2 ^ (prefixWord ++ tailWord_6168169).sum := by decide
  have hdescent : baseEnd_6168169 < baseStart_6168169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168172 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_6168172 : Nat := 118140960795 + 6168172 * 2 ^ 59
def prefixEnd_6168172 : Nat := 4983230072969 + 3 ^ 40 * 6168172 * 2
def baseEnd_6168172 : Nat := 3167236995604546232383099

theorem tailTrace_6168172 : CollatzResearch.WordTrace tailWord_6168172 prefixEnd_6168172 3167236995604546232383099 := by
  unfold tailWord_6168172
  simp only [CollatzResearch.WordTrace]
  refine ⟨112485857504886879377037385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149981143339849172502716513 112485857504886879377037385)
  ·
    refine ⟨84364393128665159532778039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112485857504886879377037385 84364393128665159532778039)
    ·
      refine ⟨126546589692997739299167059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84364393128665159532778039 126546589692997739299167059)
      ·
        refine ⟨189819884539496608948750589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126546589692997739299167059 189819884539496608948750589)
        ·
          refine ⟨71182456702311228355781471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189819884539496608948750589 71182456702311228355781471)
          ·
            refine ⟨106773685053466842533672207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71182456702311228355781471 106773685053466842533672207)
            ·
              refine ⟨160160527580200263800508311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106773685053466842533672207 160160527580200263800508311)
              ·
                refine ⟨240240791370300395700762467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160160527580200263800508311 240240791370300395700762467)
                ·
                  refine ⟨360361187055450593551143701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240240791370300395700762467 360361187055450593551143701)
                  ·
                    refine ⟨16891930643224246572709861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360361187055450593551143701 16891930643224246572709861)
                    ·
                      refine ⟨3167236995604546232383099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16891930643224246572709861 3167236995604546232383099)
                      ·
                        rfl

theorem cell23_6168172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_6168172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168172 prefixEnd_6168172 := by exact prefixLift 6168172
  have htrace : WordTrace (prefixWord ++ tailWord_6168172) baseStart_6168172 baseEnd_6168172 := by
    simpa [prefixWord, tailWord_6168172, baseEnd_6168172] using wordTrace_append hprefix tailTrace_6168172
  have hstable : (prefixWord ++ tailWord_6168172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168172).length < 2 ^ (prefixWord ++ tailWord_6168172).sum := by decide
  have hdescent : baseEnd_6168172 < baseStart_6168172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168186 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_6168186 : Nat := 118140960795 + 6168186 * 2 ^ 59
def prefixEnd_6168186 : Nat := 4983230072969 + 3 ^ 40 * 6168186 * 2
def baseEnd_6168186 : Nat := 1055748061444569725869345

theorem tailTrace_6168186 : CollatzResearch.WordTrace tailWord_6168186 prefixEnd_6168186 1055748061444569725869345 := by
  unfold tailWord_6168186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56243056407930759786271103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149981483754482026096722941 56243056407930759786271103)
  ·
    refine ⟨84364584611896139679406655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56243056407930759786271103 84364584611896139679406655)
    ·
      refine ⟨126546876917844209519109983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84364584611896139679406655 126546876917844209519109983)
      ·
        refine ⟨189820315376766314278664975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126546876917844209519109983 189820315376766314278664975)
        ·
          refine ⟨284730473065149471417997463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189820315376766314278664975 284730473065149471417997463)
          ·
            refine ⟨427095709597724207126996195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284730473065149471417997463 427095709597724207126996195)
            ·
              refine ⟨640643564396586310690494293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427095709597724207126996195 640643564396586310690494293)
              ·
                refine ⟨3753770885136247914202115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 640643564396586310690494293 3753770885136247914202115)
                ·
                  refine ⟨5630656327704371871303173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753770885136247914202115 5630656327704371871303173)
                  ·
                    refine ⟨1055748061444569725869345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630656327704371871303173 1055748061444569725869345)
                    ·
                      rfl

theorem cell23_6168186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_6168186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168186 prefixEnd_6168186 := by exact prefixLift 6168186
  have htrace : WordTrace (prefixWord ++ tailWord_6168186) baseStart_6168186 baseEnd_6168186 := by
    simpa [prefixWord, tailWord_6168186, baseEnd_6168186] using wordTrace_append hprefix tailTrace_6168186
  have hstable : (prefixWord ++ tailWord_6168186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168186).length < 2 ^ (prefixWord ++ tailWord_6168186).sum := by decide
  have hdescent : baseEnd_6168186 < baseStart_6168186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168203 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 1, 4]
def baseStart_6168203 : Nat := 118140960795 + 6168203 * 2 ^ 59
def prefixEnd_6168203 : Nat := 4983230072969 + 3 ^ 40 * 6168203 * 2
def baseEnd_6168203 : Nat := 1055750971168278537031819

theorem tailTrace_6168203 : CollatzResearch.WordTrace tailWord_6168203 prefixEnd_6168203 1055750971168278537031819 := by
  unfold tailWord_6168203
  simp only [CollatzResearch.WordTrace]
  refine ⟨224972845672661451048453263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149981897115107634032302175 224972845672661451048453263)
  ·
    refine ⟨337459268508992176572679895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224972845672661451048453263 337459268508992176572679895)
    ·
      refine ⟨506188902763488264859019843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337459268508992176572679895 506188902763488264859019843)
      ·
        refine ⟨759283354145232397288529765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506188902763488264859019843 759283354145232397288529765)
        ·
          refine ⟨142365628902231074491599331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 759283354145232397288529765 142365628902231074491599331)
          ·
            refine ⟨213548443353346611737398997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142365628902231074491599331 213548443353346611737398997)
            ·
              refine ⟨5005041641094061212595289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213548443353346611737398997 5005041641094061212595289)
              ·
                refine ⟨3753781230820545909446467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5005041641094061212595289 3753781230820545909446467)
                ·
                  refine ⟨5630671846230818864169701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753781230820545909446467 5630671846230818864169701)
                  ·
                    refine ⟨1055750971168278537031819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630671846230818864169701 1055750971168278537031819)
                    ·
                      rfl

theorem cell23_6168203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 1, 4].length) (baseStart_6168203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168203 prefixEnd_6168203 := by exact prefixLift 6168203
  have htrace : WordTrace (prefixWord ++ tailWord_6168203) baseStart_6168203 baseEnd_6168203 := by
    simpa [prefixWord, tailWord_6168203, baseEnd_6168203] using wordTrace_append hprefix tailTrace_6168203
  have hstable : (prefixWord ++ tailWord_6168203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168203).length < 2 ^ (prefixWord ++ tailWord_6168203).sum := by decide
  have hdescent : baseEnd_6168203 < baseStart_6168203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168216 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 6]
def baseStart_6168216 : Nat := 118140960795 + 6168216 * 2 ^ 59
def prefixEnd_6168216 : Nat := 4983230072969 + 3 ^ 40 * 6168216 * 2
def baseEnd_6168216 : Nat := 351917732083704895581433

theorem tailTrace_6168216 : CollatzResearch.WordTrace tailWord_6168216 prefixEnd_6168216 351917732083704895581433 := by
  unfold tailWord_6168216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112486659910807177134338251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149982213214409569512451001 112486659910807177134338251)
  ·
    refine ⟨168729989866210765701507377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112486659910807177134338251 168729989866210765701507377)
    ·
      refine ⟨126547492399658074276130533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168729989866210765701507377 126547492399658074276130533)
      ·
        refine ⟨23727654824935888926774475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126547492399658074276130533 23727654824935888926774475)
        ·
          refine ⟨35591482237403833390161713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23727654824935888926774475 35591482237403833390161713)
          ·
            refine ⟨26693611678052875042621285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35591482237403833390161713 26693611678052875042621285)
            ·
              refine ⟨5005052189634914070491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26693611678052875042621285 5005052189634914070491491)
              ·
                refine ⟨7507578284452371105737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005052189634914070491491 7507578284452371105737237)
                ·
                  refine ⟨351917732083704895581433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7507578284452371105737237 351917732083704895581433)
                  ·
                    rfl

theorem cell23_6168216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_6168216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168216 prefixEnd_6168216 := by exact prefixLift 6168216
  have htrace : WordTrace (prefixWord ++ tailWord_6168216) baseStart_6168216 baseEnd_6168216 := by
    simpa [prefixWord, tailWord_6168216, baseEnd_6168216] using wordTrace_append hprefix tailTrace_6168216
  have hstable : (prefixWord ++ tailWord_6168216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168216).length < 2 ^ (prefixWord ++ tailWord_6168216).sum := by decide
  have hdescent : baseEnd_6168216 < baseStart_6168216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168243 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 1, 1, 3]
def baseStart_6168243 : Nat := 118140960795 + 6168243 * 2 ^ 59
def prefixEnd_6168243 : Nat := 4983230072969 + 3 ^ 40 * 6168243 * 2
def baseEnd_6168243 : Nat := 3167273452731015454595273

theorem tailTrace_6168243 : CollatzResearch.WordTrace tailWord_6168243 prefixEnd_6168243 3167273452731015454595273 := by
  unfold tailWord_6168243
  simp only [CollatzResearch.WordTrace]
  refine ⟨224974304592516537879909383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149982869728344358586606255 224974304592516537879909383)
  ·
    refine ⟨337461456888774806819864075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224974304592516537879909383 337461456888774806819864075)
    ·
      refine ⟨506192185333162210229796113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337461456888774806819864075 506192185333162210229796113)
      ·
        refine ⟨379644138999871657672347085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506192185333162210229796113 379644138999871657672347085)
        ·
          refine ⟨142366552124951871627130157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379644138999871657672347085 142366552124951871627130157)
          ·
            refine ⟨53387457046856951860173809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142366552124951871627130157 53387457046856951860173809)
            ·
              refine ⟨40040592785142713895130357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53387457046856951860173809 40040592785142713895130357)
              ·
                refine ⟨3753805573607129427668471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40040592785142713895130357 3753805573607129427668471)
                ·
                  refine ⟨5630708360410694141502707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753805573607129427668471 5630708360410694141502707)
                  ·
                    refine ⟨8446062540616041212254061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630708360410694141502707 8446062540616041212254061)
                    ·
                      refine ⟨3167273452731015454595273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446062540616041212254061 3167273452731015454595273)
                      ·
                        rfl

theorem cell23_6168243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 1, 3].length) (baseStart_6168243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168243 prefixEnd_6168243 := by exact prefixLift 6168243
  have htrace : WordTrace (prefixWord ++ tailWord_6168243) baseStart_6168243 baseEnd_6168243 := by
    simpa [prefixWord, tailWord_6168243, baseEnd_6168243] using wordTrace_append hprefix tailTrace_6168243
  have hstable : (prefixWord ++ tailWord_6168243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168243).length < 2 ^ (prefixWord ++ tailWord_6168243).sum := by decide
  have hdescent : baseEnd_6168243 < baseStart_6168243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168260 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6168260 : Nat := 118140960795 + 6168260 * 2 ^ 59
def prefixEnd_6168260 : Nat := 4983230072969 + 3 ^ 40 * 6168260 * 2
def baseEnd_6168260 : Nat := 3167282181902141888082695

theorem tailTrace_6168260 : CollatzResearch.WordTrace tailWord_6168260 prefixEnd_6168260 3167282181902141888082695 := by
  unfold tailWord_6168260
  simp only [CollatzResearch.WordTrace]
  refine ⟨112487462316727474891639117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149983283088969966522185489 112487462316727474891639117)
  ·
    refine ⟨42182798368772803084364669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112487462316727474891639117 42182798368772803084364669)
    ·
      refine ⟨15818549388289801156636751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42182798368772803084364669 15818549388289801156636751)
      ·
        refine ⟨23727824082434701734955127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15818549388289801156636751 23727824082434701734955127)
        ·
          refine ⟨35591736123652052602432691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23727824082434701734955127 35591736123652052602432691)
          ·
            refine ⟨53387604185478078903649037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35591736123652052602432691 53387604185478078903649037)
            ·
              refine ⟨20020351569554279588868389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53387604185478078903649037 20020351569554279588868389)
              ·
                refine ⟨3753815919291427422912823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20020351569554279588868389 3753815919291427422912823)
                ·
                  refine ⟨5630723878937141134369235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753815919291427422912823 5630723878937141134369235)
                  ·
                    refine ⟨8446085818405711701553853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630723878937141134369235 8446085818405711701553853)
                    ·
                      refine ⟨3167282181902141888082695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446085818405711701553853 3167282181902141888082695)
                      ·
                        rfl

theorem cell23_6168260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6168260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168260 prefixEnd_6168260 := by exact prefixLift 6168260
  have htrace : WordTrace (prefixWord ++ tailWord_6168260) baseStart_6168260 baseEnd_6168260 := by
    simpa [prefixWord, tailWord_6168260, baseEnd_6168260] using wordTrace_append hprefix tailTrace_6168260
  have hstable : (prefixWord ++ tailWord_6168260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168260).length < 2 ^ (prefixWord ++ tailWord_6168260).sum := by decide
  have hdescent : baseEnd_6168260 < baseStart_6168260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168272 : List Nat := [2, 1, 1, 1, 1, 2, 1, 14]
def baseStart_6168272 : Nat := 118140960795 + 6168272 * 2 ^ 59
def prefixEnd_6168272 : Nat := 4983230072969 + 3 ^ 40 * 6168272 * 2
def baseEnd_6168272 : Nat := 117306975691481327449357

theorem tailTrace_6168272 : CollatzResearch.WordTrace tailWord_6168272 prefixEnd_6168272 117306975691481327449357 := by
  unfold tailWord_6168272
  simp only [CollatzResearch.WordTrace]
  refine ⟨112487681154705737916357535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149983574872940983888476713 112487681154705737916357535)
  ·
    refine ⟨168731521732058606874536303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112487681154705737916357535 168731521732058606874536303)
    ·
      refine ⟨253097282598087910311804455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168731521732058606874536303 253097282598087910311804455)
      ·
        refine ⟨379645923897131865467706683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253097282598087910311804455 379645923897131865467706683)
        ·
          refine ⟨569468885845697798201560025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379645923897131865467706683 569468885845697798201560025)
          ·
            refine ⟨427101664384273348651170019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569468885845697798201560025 427101664384273348651170019)
            ·
              refine ⟨640652496576410022976755029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427101664384273348651170019 640652496576410022976755029)
              ·
                refine ⟨117306975691481327449357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 640652496576410022976755029 117306975691481327449357)
                ·
                  rfl

theorem cell23_6168272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_6168272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168272 prefixEnd_6168272 := by exact prefixLift 6168272
  have htrace : WordTrace (prefixWord ++ tailWord_6168272) baseStart_6168272 baseEnd_6168272 := by
    simpa [prefixWord, tailWord_6168272, baseEnd_6168272] using wordTrace_append hprefix tailTrace_6168272
  have hstable : (prefixWord ++ tailWord_6168272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168272).length < 2 ^ (prefixWord ++ tailWord_6168272).sum := by decide
  have hdescent : baseEnd_6168272 < baseStart_6168272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168276 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6168276 : Nat := 118140960795 + 6168276 * 2 ^ 59
def prefixEnd_6168276 : Nat := 4983230072969 + 3 ^ 40 * 6168276 * 2
def baseEnd_6168276 : Nat := 1055763465864204608494207

theorem tailTrace_6168276 : CollatzResearch.WordTrace tailWord_6168276 prefixEnd_6168276 1055763465864204608494207 := by
  unfold tailWord_6168276
  simp only [CollatzResearch.WordTrace]
  refine ⟨112487754100698492257930341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149983672134264656343907121 112487754100698492257930341)
  ·
    refine ⟨21091453893880967298361939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112487754100698492257930341 21091453893880967298361939)
    ·
      refine ⟨31637180840821450947542909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21091453893880967298361939 31637180840821450947542909)
      ·
        refine ⟨11863942815308044105328591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31637180840821450947542909 11863942815308044105328591)
        ·
          refine ⟨17795914222962066157992887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11863942815308044105328591 17795914222962066157992887)
          ·
            refine ⟨26693871334443099236989331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17795914222962066157992887 26693871334443099236989331)
            ·
              refine ⟨40040807001664648855483997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26693871334443099236989331 40040807001664648855483997)
              ·
                refine ⟨15015302625624243320806499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40040807001664648855483997 15015302625624243320806499)
                ·
                  refine ⟨22522953938436364981209749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15015302625624243320806499 22522953938436364981209749)
                  ·
                    refine ⟨1055763465864204608494207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22522953938436364981209749 1055763465864204608494207)
                    ·
                      rfl

theorem cell23_6168276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6168276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168276 prefixEnd_6168276 := by exact prefixLift 6168276
  have htrace : WordTrace (prefixWord ++ tailWord_6168276) baseStart_6168276 baseEnd_6168276 := by
    simpa [prefixWord, tailWord_6168276, baseEnd_6168276] using wordTrace_append hprefix tailTrace_6168276
  have hstable : (prefixWord ++ tailWord_6168276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168276).length < 2 ^ (prefixWord ++ tailWord_6168276).sum := by decide
  have hdescent : baseEnd_6168276 < baseStart_6168276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168296 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6168296 : Nat := 118140960795 + 6168296 * 2 ^ 59
def prefixEnd_6168296 : Nat := 4983230072969 + 3 ^ 40 * 6168296 * 2
def baseEnd_6168296 : Nat := 3167300667205703747232529

theorem tailTrace_6168296 : CollatzResearch.WordTrace tailWord_6168296 prefixEnd_6168296 3167300667205703747232529 := by
  unfold tailWord_6168296
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488118830662263965794371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149984158440883018621059161 112488118830662263965794371)
  ·
    refine ⟨168732178245993395948691557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112488118830662263965794371 168732178245993395948691557)
    ·
      refine ⟨31637283421123761740379667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168732178245993395948691557 31637283421123761740379667)
      ·
        refine ⟨47455925131685642610569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31637283421123761740379667 47455925131685642610569501)
        ·
          refine ⟨17795971924382115978963563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47455925131685642610569501 17795971924382115978963563)
          ·
            refine ⟨26693957886573173968445345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17795971924382115978963563 26693957886573173968445345)
            ·
              refine ⟨20020468414929880476334009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26693957886573173968445345 20020468414929880476334009)
              ·
                refine ⟨15015351311197410357250507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20020468414929880476334009 15015351311197410357250507)
                ·
                  refine ⟨22523026966796115535875761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15015351311197410357250507 22523026966796115535875761)
                  ·
                    refine ⟨16892270225097086651906821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22523026966796115535875761 16892270225097086651906821)
                    ·
                      refine ⟨3167300667205703747232529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16892270225097086651906821 3167300667205703747232529)
                      ·
                        rfl

theorem cell23_6168296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6168296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168296 prefixEnd_6168296 := by exact prefixLift 6168296
  have htrace : WordTrace (prefixWord ++ tailWord_6168296) baseStart_6168296 baseEnd_6168296 := by
    simpa [prefixWord, tailWord_6168296, baseEnd_6168296] using wordTrace_append hprefix tailTrace_6168296
  have hstable : (prefixWord ++ tailWord_6168296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168296).length < 2 ^ (prefixWord ++ tailWord_6168296).sum := by decide
  have hdescent : baseEnd_6168296 < baseStart_6168296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168300 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_6168300 : Nat := 118140960795 + 6168300 * 2 ^ 59
def prefixEnd_6168300 : Nat := 4983230072969 + 3 ^ 40 * 6168300 * 2
def baseEnd_6168300 : Nat := 3167302721128321731582511

theorem tailTrace_6168300 : CollatzResearch.WordTrace tailWord_6168300 prefixEnd_6168300 3167302721128321731582511 := by
  unfold tailWord_6168300
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488191776655018307367177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149984255702206691076489569 112488191776655018307367177)
  ·
    refine ⟨84366143832491263730525383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112488191776655018307367177 84366143832491263730525383)
    ·
      refine ⟨126549215748736895595788075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84366143832491263730525383 126549215748736895595788075)
      ·
        refine ⟨189823823623105343393682113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126549215748736895595788075 189823823623105343393682113)
        ·
          refine ⟨142367867717329007545261585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189823823623105343393682113 142367867717329007545261585)
          ·
            refine ⟨106775900787996755658946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142367867717329007545261585 106775900787996755658946189)
            ·
              refine ⟨40040962795498783372104821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106775900787996755658946189 40040962795498783372104821)
              ·
                refine ⟨3753840262078010941134827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40040962795498783372104821 3753840262078010941134827)
                ·
                  refine ⟨5630760393117016411702241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753840262078010941134827 5630760393117016411702241)
                  ·
                    refine ⟨4223070294837762308776681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5630760393117016411702241 4223070294837762308776681)
                    ·
                      refine ⟨3167302721128321731582511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223070294837762308776681 3167302721128321731582511)
                      ·
                        rfl

theorem cell23_6168300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_6168300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168300 prefixEnd_6168300 := by exact prefixLift 6168300
  have htrace : WordTrace (prefixWord ++ tailWord_6168300) baseStart_6168300 baseEnd_6168300 := by
    simpa [prefixWord, tailWord_6168300, baseEnd_6168300] using wordTrace_append hprefix tailTrace_6168300
  have hstable : (prefixWord ++ tailWord_6168300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168300).length < 2 ^ (prefixWord ++ tailWord_6168300).sum := by decide
  have hdescent : baseEnd_6168300 < baseStart_6168300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168310 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6168310 : Nat := 118140960795 + 6168310 * 2 ^ 59
def prefixEnd_6168310 : Nat := 4983230072969 + 3 ^ 40 * 6168310 * 2
def baseEnd_6168310 : Nat := 1055769285311622230819155

theorem tailTrace_6168310 : CollatzResearch.WordTrace tailWord_6168310 prefixEnd_6168310 1055769285311622230819155 := by
  unfold tailWord_6168310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061046767704613020162399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149984498855515872215065589 14061046767704613020162399)
  ·
    refine ⟨21091570151556919530243599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14061046767704613020162399 21091570151556919530243599)
    ·
      refine ⟨31637355227335379295365399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21091570151556919530243599 31637355227335379295365399)
      ·
        refine ⟨47456032841003068943048099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31637355227335379295365399 47456032841003068943048099)
        ·
          refine ⟨71184049261504603414572149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47456032841003068943048099 71184049261504603414572149)
          ·
            refine ⟨6673504618266056570116139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71184049261504603414572149 6673504618266056570116139)
            ·
              refine ⟨10010256927399084855174209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6673504618266056570116139 10010256927399084855174209)
              ·
                refine ⟨7507692695549313641380657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010256927399084855174209 7507692695549313641380657)
                ·
                  refine ⟨5630769521661985231035493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7507692695549313641380657 5630769521661985231035493)
                  ·
                    refine ⟨1055769285311622230819155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5630769521661985231035493 1055769285311622230819155)
                    ·
                      rfl

theorem cell23_6168310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6168310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168310 prefixEnd_6168310 := by exact prefixLift 6168310
  have htrace : WordTrace (prefixWord ++ tailWord_6168310) baseStart_6168310 baseEnd_6168310 := by
    simpa [prefixWord, tailWord_6168310, baseEnd_6168310] using wordTrace_append hprefix tailTrace_6168310
  have hstable : (prefixWord ++ tailWord_6168310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168310).length < 2 ^ (prefixWord ++ tailWord_6168310).sum := by decide
  have hdescent : baseEnd_6168310 < baseStart_6168310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168340 : List Nat := [2, 4, 4, 1, 1, 1, 1, 9]
def baseStart_6168340 : Nat := 118140960795 + 6168340 * 2 ^ 59
def prefixEnd_6168340 : Nat := 4983230072969 + 3 ^ 40 * 6168340 * 2
def baseEnd_6168340 : Nat := 117308268902018576854901

theorem tailTrace_6168340 : CollatzResearch.WordTrace tailWord_6168340 prefixEnd_6168340 117308268902018576854901 := by
  unfold tailWord_6168340
  simp only [CollatzResearch.WordTrace]
  refine ⟨112488921236582561723095237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149985228315443415630793649 112488921236582561723095237)
  ·
    refine ⟨21091672731859230323080357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112488921236582561723095237 21091672731859230323080357)
    ·
      refine ⟨3954688637223605685577567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21091672731859230323080357 3954688637223605685577567)
      ·
        refine ⟨5932032955835408528366351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954688637223605685577567 5932032955835408528366351)
        ·
          refine ⟨8898049433753112792549527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932032955835408528366351 8898049433753112792549527)
          ·
            refine ⟨13347074150629669188824291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898049433753112792549527 13347074150629669188824291)
            ·
              refine ⟨20020611225944503783236437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13347074150629669188824291 20020611225944503783236437)
              ·
                refine ⟨117308268902018576854901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20020611225944503783236437 117308268902018576854901)
                ·
                  rfl

theorem cell23_6168340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 9].length) (baseStart_6168340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168340 prefixEnd_6168340 := by exact prefixLift 6168340
  have htrace : WordTrace (prefixWord ++ tailWord_6168340) baseStart_6168340 baseEnd_6168340 := by
    simpa [prefixWord, tailWord_6168340, baseEnd_6168340] using wordTrace_append hprefix tailTrace_6168340
  have hstable : (prefixWord ++ tailWord_6168340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168340).length < 2 ^ (prefixWord ++ tailWord_6168340).sum := by decide
  have hdescent : baseEnd_6168340 < baseStart_6168340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
