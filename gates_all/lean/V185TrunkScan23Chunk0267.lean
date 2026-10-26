import V185TrunkScan23Chunk0266

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1579628 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_1579628 : Nat := 118140960795 + 1579628 * 2 ^ 59
def prefixEnd_1579628 : Nat := 4983230072969 + 3 ^ 40 * 1579628 * 2
def baseEnd_1579628 : Nat := 811108419300450931885429

theorem tailTrace_1579628 : CollatzResearch.WordTrace tailWord_1579628 prefixEnd_1579628 811108419300450931885429 := by
  unfold tailWord_1579628
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806883160642504914653769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38409177547523339886205025 28806883160642504914653769)
  ·
    refine ⟨21605162370481878685990327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28806883160642504914653769 21605162370481878685990327)
    ·
      refine ⟨32407743555722818028985491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21605162370481878685990327 32407743555722818028985491)
      ·
        refine ⟨48611615333584227043478237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32407743555722818028985491 48611615333584227043478237)
        ·
          refine ⟨18229355750094085141304339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48611615333584227043478237 18229355750094085141304339)
          ·
            refine ⟨27344033625141127711956509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229355750094085141304339 27344033625141127711956509)
            ·
              refine ⟨10254012609427922891983691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27344033625141127711956509 10254012609427922891983691)
              ·
                refine ⟨15381018914141884337975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254012609427922891983691 15381018914141884337975537)
                ·
                  refine ⟨11535764185606413253481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15381018914141884337975537 11535764185606413253481653)
                  ·
                    refine ⟨1081477892400601242513905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11535764185606413253481653 1081477892400601242513905)
                    ·
                      refine ⟨811108419300450931885429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081477892400601242513905 811108419300450931885429)
                      ·
                        rfl

theorem cell23_1579628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_1579628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579628 prefixEnd_1579628 := by exact prefixLift 1579628
  have htrace : WordTrace (prefixWord ++ tailWord_1579628) baseStart_1579628 baseEnd_1579628 := by
    simpa [prefixWord, tailWord_1579628, baseEnd_1579628] using wordTrace_append hprefix tailTrace_1579628
  have hstable : (prefixWord ++ tailWord_1579628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579628).length < 2 ^ (prefixWord ++ tailWord_1579628).sum := by decide
  have hdescent : baseEnd_1579628 < baseStart_1579628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579631 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_1579631 : Nat := 118140960795 + 1579631 * 2 ^ 59
def prefixEnd_1579631 : Nat := 4983230072969 + 3 ^ 40 * 1579631 * 2
def baseEnd_1579631 : Nat := 811109959742414420147915

theorem tailTrace_1579631 : CollatzResearch.WordTrace tailWord_1579631 prefixEnd_1579631 811109959742414420147915 := by
  unfold tailWord_1579631
  simp only [CollatzResearch.WordTrace]
  refine ⟨57613875740274141341666747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38409250493516094227777831 57613875740274141341666747)
  ·
    refine ⟨86420813610411212012500121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57613875740274141341666747 86420813610411212012500121)
    ·
      refine ⟨64815610207808409009375091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86420813610411212012500121 64815610207808409009375091)
      ·
        refine ⟨97223415311712613514062637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64815610207808409009375091 97223415311712613514062637)
        ·
          refine ⟨36458780741892230067773489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97223415311712613514062637 36458780741892230067773489)
          ·
            refine ⟨27344085556419172550830117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36458780741892230067773489 27344085556419172550830117)
            ·
              refine ⟨5127016041828594853280647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27344085556419172550830117 5127016041828594853280647)
              ·
                refine ⟨7690524062742892279920971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127016041828594853280647 7690524062742892279920971)
                ·
                  refine ⟨11535786094114338419881457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690524062742892279920971 11535786094114338419881457)
                  ·
                    refine ⟨8651839570585753814911093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11535786094114338419881457 8651839570585753814911093)
                    ·
                      refine ⟨811109959742414420147915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8651839570585753814911093 811109959742414420147915)
                      ·
                        rfl

theorem cell23_1579631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_1579631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579631 prefixEnd_1579631 := by exact prefixLift 1579631
  have htrace : WordTrace (prefixWord ++ tailWord_1579631) baseStart_1579631 baseEnd_1579631 := by
    simpa [prefixWord, tailWord_1579631, baseEnd_1579631] using wordTrace_append hprefix tailTrace_1579631
  have hstable : (prefixWord ++ tailWord_1579631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579631).length < 2 ^ (prefixWord ++ tailWord_1579631).sum := by decide
  have hdescent : baseEnd_1579631 < baseStart_1579631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579671 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1579671 : Nat := 118140960795 + 1579671 * 2 ^ 59
def prefixEnd_1579671 : Nat := 4983230072969 + 3 ^ 40 * 1579671 * 2
def baseEnd_1579671 : Nat := 811130498968594263647731

theorem tailTrace_1579671 : CollatzResearch.WordTrace tailWord_1579671 prefixEnd_1579671 811130498968594263647731 := by
  unfold tailWord_1579671
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615334660129228173122867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38410223106752818782081911 57615334660129228173122867)
  ·
    refine ⟨86423001990193842259684301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57615334660129228173122867 86423001990193842259684301)
    ·
      refine ⟨32408625746322690847381613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86423001990193842259684301 32408625746322690847381613)
      ·
        refine ⟨12153234654871009067768105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32408625746322690847381613 12153234654871009067768105)
        ·
          refine ⟨9114925991153256800826079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12153234654871009067768105 9114925991153256800826079)
          ·
            refine ⟨13672388986729885201239119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114925991153256800826079 13672388986729885201239119)
            ·
              refine ⟨20508583480094827801858679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672388986729885201239119 20508583480094827801858679)
              ·
                refine ⟨30762875220142241702788019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20508583480094827801858679 30762875220142241702788019)
                ·
                  refine ⟨46144312830213362554182029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30762875220142241702788019 46144312830213362554182029)
                  ·
                    refine ⟨17304117311330010957818261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46144312830213362554182029 17304117311330010957818261)
                    ·
                      refine ⟨811130498968594263647731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17304117311330010957818261 811130498968594263647731)
                      ·
                        rfl

theorem cell23_1579671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1579671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579671 prefixEnd_1579671 := by exact prefixLift 1579671
  have htrace : WordTrace (prefixWord ++ tailWord_1579671) baseStart_1579671 baseEnd_1579671 := by
    simpa [prefixWord, tailWord_1579671, baseEnd_1579671] using wordTrace_append hprefix tailTrace_1579671
  have hstable : (prefixWord ++ tailWord_1579671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579671).length < 2 ^ (prefixWord ++ tailWord_1579671).sum := by decide
  have hdescent : baseEnd_1579671 < baseStart_1579671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579708 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1579708 : Nat := 118140960795 + 1579708 * 2 ^ 59
def prefixEnd_1579708 : Nat := 4983230072969 + 3 ^ 40 * 1579708 * 2
def baseEnd_1579708 : Nat := 811149497752810618885061

theorem tailTrace_1579708 : CollatzResearch.WordTrace tailWord_1579708 prefixEnd_1579708 811149497752810618885061 := by
  unfold tailWord_1579708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808342080497591746109889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38411122773996788994813185 28808342080497591746109889)
  ·
    refine ⟨21606256560373193809582417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28808342080497591746109889 21606256560373193809582417)
    ·
      refine ⟨16204692420279895357186813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21606256560373193809582417 16204692420279895357186813)
      ·
        refine ⟨6076759657604960758945055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16204692420279895357186813 6076759657604960758945055)
        ·
          refine ⟨9115139486407441138417583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076759657604960758945055 9115139486407441138417583)
          ·
            refine ⟨13672709229611161707626375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115139486407441138417583 13672709229611161707626375)
            ·
              refine ⟨20509063844416742561439563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672709229611161707626375 20509063844416742561439563)
              ·
                refine ⟨30763595766625113842159345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20509063844416742561439563 30763595766625113842159345)
                ·
                  refine ⟨23072696824968835381619509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30763595766625113842159345 23072696824968835381619509)
                  ·
                    refine ⟨2163065327340828317026829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23072696824968835381619509 2163065327340828317026829)
                    ·
                      refine ⟨811149497752810618885061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2163065327340828317026829 811149497752810618885061)
                      ·
                        rfl

theorem cell23_1579708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1579708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579708 prefixEnd_1579708 := by exact prefixLift 1579708
  have htrace : WordTrace (prefixWord ++ tailWord_1579708) baseStart_1579708 baseEnd_1579708 := by
    simpa [prefixWord, tailWord_1579708, baseEnd_1579708] using wordTrace_append hprefix tailTrace_1579708
  have hstable : (prefixWord ++ tailWord_1579708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579708).length < 2 ^ (prefixWord ++ tailWord_1579708).sum := by decide
  have hdescent : baseEnd_1579708 < baseStart_1579708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579735 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 4, 3, 2]
def baseStart_1579735 : Nat := 118140960795 + 1579735 * 2 ^ 59
def prefixEnd_1579735 : Nat := 4983230072969 + 3 ^ 40 * 1579735 * 2
def baseEnd_1579735 : Nat := 811163361730482013247437

theorem tailTrace_1579735 : CollatzResearch.WordTrace tailWord_1579735 prefixEnd_1579735 811163361730482013247437 := by
  unfold tailWord_1579735
  simp only [CollatzResearch.WordTrace]
  refine ⟨57617668931897367103452659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38411779287931578068968439 57617668931897367103452659)
  ·
    refine ⟨86426503397846050655178989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57617668931897367103452659 86426503397846050655178989)
    ·
      refine ⟨32409938774192268995692121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86426503397846050655178989 32409938774192268995692121)
      ·
        refine ⟨24307454080644201746769091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32409938774192268995692121 24307454080644201746769091)
        ·
          refine ⟨36461181120966302620153637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24307454080644201746769091 36461181120966302620153637)
          ·
            refine ⟨6836471460181181741278807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36461181120966302620153637 6836471460181181741278807)
            ·
              refine ⟨10254707190271772611918211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836471460181181741278807 10254707190271772611918211)
              ·
                refine ⟨15382060785407658917877317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254707190271772611918211 15382060785407658917877317)
                ·
                  refine ⟨2884136397263936047101997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15382060785407658917877317 2884136397263936047101997)
                  ·
                    refine ⟨1081551148973976017663249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2884136397263936047101997 1081551148973976017663249)
                    ·
                      refine ⟨811163361730482013247437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081551148973976017663249 811163361730482013247437)
                      ·
                        rfl

theorem cell23_1579735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_1579735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579735 prefixEnd_1579735 := by exact prefixLift 1579735
  have htrace : WordTrace (prefixWord ++ tailWord_1579735) baseStart_1579735 baseEnd_1579735 := by
    simpa [prefixWord, tailWord_1579735, baseEnd_1579735] using wordTrace_append hprefix tailTrace_1579735
  have hstable : (prefixWord ++ tailWord_1579735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579735).length < 2 ^ (prefixWord ++ tailWord_1579735).sum := by decide
  have hdescent : baseEnd_1579735 < baseStart_1579735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579762 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1579762 : Nat := 118140960795 + 1579762 * 2 ^ 59
def prefixEnd_1579762 : Nat := 4983230072969 + 3 ^ 40 * 1579762 * 2
def baseEnd_1579762 : Nat := 270392408569384469203271

theorem tailTrace_1579762 : CollatzResearch.WordTrace tailWord_1579762 prefixEnd_1579762 270392408569384469203271 := by
  unfold tailWord_1579762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14404663425699887678671385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38412435801866367143123693 14404663425699887678671385)
  ·
    refine ⟨10803497569274915759003539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14404663425699887678671385 10803497569274915759003539)
    ·
      refine ⟨16205246353912373638505309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10803497569274915759003539 16205246353912373638505309)
      ·
        refine ⟨6076967382717140114439491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16205246353912373638505309 6076967382717140114439491)
        ·
          refine ⟨9115451074075710171659237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076967382717140114439491 9115451074075710171659237)
          ·
            refine ⟨1709147076389195657186107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9115451074075710171659237 1709147076389195657186107)
            ·
              refine ⟨2563720614583793485779161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709147076389195657186107 2563720614583793485779161)
              ·
                refine ⟨1922790460937845114334371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563720614583793485779161 1922790460937845114334371)
                ·
                  refine ⟨2884185691406767671501557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922790460937845114334371 2884185691406767671501557)
                  ·
                    refine ⟨270392408569384469203271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2884185691406767671501557 270392408569384469203271)
                    ·
                      rfl

theorem cell23_1579762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1579762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579762 prefixEnd_1579762 := by exact prefixLift 1579762
  have htrace : WordTrace (prefixWord ++ tailWord_1579762) baseStart_1579762 baseEnd_1579762 := by
    simpa [prefixWord, tailWord_1579762, baseEnd_1579762] using wordTrace_append hprefix tailTrace_1579762
  have hstable : (prefixWord ++ tailWord_1579762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579762).length < 2 ^ (prefixWord ++ tailWord_1579762).sum := by decide
  have hdescent : baseEnd_1579762 < baseStart_1579762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579785 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_1579785 : Nat := 118140960795 + 1579785 * 2 ^ 59
def prefixEnd_1579785 : Nat := 4983230072969 + 3 ^ 40 * 1579785 * 2
def baseEnd_1579785 : Nat := 811189035763206817622207

theorem tailTrace_1579785 : CollatzResearch.WordTrace tailWord_1579785 prefixEnd_1579785 811189035763206817622207 := by
  unfold tailWord_1579785
  simp only [CollatzResearch.WordTrace]
  refine ⟨57619492581716225642772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38412995054477483761848539 57619492581716225642772809)
  ·
    refine ⟨43214619436287169232079607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57619492581716225642772809 43214619436287169232079607)
    ·
      refine ⟨64821929154430753848119411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43214619436287169232079607 64821929154430753848119411)
      ·
        refine ⟨97232893731646130772179117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64821929154430753848119411 97232893731646130772179117)
        ·
          refine ⟨36462335149367299039567169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97232893731646130772179117 36462335149367299039567169)
          ·
            refine ⟨27346751362025474279675377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36462335149367299039567169 27346751362025474279675377)
            ·
              refine ⟨20510063521519105709756533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27346751362025474279675377 20510063521519105709756533)
              ·
                refine ⟨1922818455142416160289675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20510063521519105709756533 1922818455142416160289675)
                ·
                  refine ⟨2884227682713624240434513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922818455142416160289675 2884227682713624240434513)
                  ·
                    refine ⟨2163170762035218180325885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2884227682713624240434513 2163170762035218180325885)
                    ·
                      refine ⟨811189035763206817622207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2163170762035218180325885 811189035763206817622207)
                      ·
                        rfl

theorem cell23_1579785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_1579785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579785 prefixEnd_1579785 := by exact prefixLift 1579785
  have htrace : WordTrace (prefixWord ++ tailWord_1579785) baseStart_1579785 baseEnd_1579785 := by
    simpa [prefixWord, tailWord_1579785, baseEnd_1579785] using wordTrace_append hprefix tailTrace_1579785
  have hstable : (prefixWord ++ tailWord_1579785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579785).length < 2 ^ (prefixWord ++ tailWord_1579785).sum := by decide
  have hdescent : baseEnd_1579785 < baseStart_1579785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579812 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1579812 : Nat := 118140960795 + 1579812 * 2 ^ 59
def prefixEnd_1579812 : Nat := 4983230072969 + 3 ^ 40 * 1579812 * 2
def baseEnd_1579812 : Nat := 811202899740878211984583

theorem tailTrace_1579812 : CollatzResearch.WordTrace tailWord_1579812 prefixEnd_1579812 811202899740878211984583 := by
  unfold tailWord_1579812
  simp only [CollatzResearch.WordTrace]
  refine ⟨28810238676309204627002845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38413651568412272836003793 28810238676309204627002845)
  ·
    refine ⟨10803839503615951735126067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28810238676309204627002845 10803839503615951735126067)
    ·
      refine ⟨16205759255423927602689101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10803839503615951735126067 16205759255423927602689101)
      ·
        refine ⟨6077159720783972851008413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16205759255423927602689101 6077159720783972851008413)
        ·
          refine ⟨2278934895293989819128155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6077159720783972851008413 2278934895293989819128155)
          ·
            refine ⟨3418402342940984728692233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278934895293989819128155 3418402342940984728692233)
            ·
              refine ⟨2563801757205738546519175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418402342940984728692233 2563801757205738546519175)
              ·
                refine ⟨3845702635808607819778763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563801757205738546519175 3845702635808607819778763)
                ·
                  refine ⟨5768553953712911729668145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845702635808607819778763 5768553953712911729668145)
                  ·
                    refine ⟨4326415465284683797251109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768553953712911729668145 4326415465284683797251109)
                    ·
                      refine ⟨811202899740878211984583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4326415465284683797251109 811202899740878211984583)
                      ·
                        rfl

theorem cell23_1579812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1579812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579812 prefixEnd_1579812 := by exact prefixLift 1579812
  have htrace : WordTrace (prefixWord ++ tailWord_1579812) baseStart_1579812 baseEnd_1579812 := by
    simpa [prefixWord, tailWord_1579812, baseEnd_1579812] using wordTrace_append hprefix tailTrace_1579812
  have hstable : (prefixWord ++ tailWord_1579812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579812).length < 2 ^ (prefixWord ++ tailWord_1579812).sum := by decide
  have hdescent : baseEnd_1579812 < baseStart_1579812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579822 : List Nat := [4, 1, 3, 2, 1, 2, 3, 7]
def baseStart_1579822 : Nat := 118140960795 + 1579822 * 2 ^ 59
def prefixEnd_1579822 : Nat := 4983230072969 + 3 ^ 40 * 1579822 * 2
def baseEnd_1579822 : Nat := 30044742020274932328131

theorem tailTrace_1579822 : CollatzResearch.WordTrace tailWord_1579822 prefixEnd_1579822 30044742020274932328131 := by
  unfold tailWord_1579822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202605260322772620233715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38413894721721453974579813 7202605260322772620233715)
  ·
    refine ⟨10803907890484158930350573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202605260322772620233715 10803907890484158930350573)
    ·
      refine ⟨4051465458931559598881465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10803907890484158930350573 4051465458931559598881465)
      ·
        refine ⟨3038599094198669699161099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051465458931559598881465 3038599094198669699161099)
        ·
          refine ⟨4557898641298004548741649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038599094198669699161099 4557898641298004548741649)
          ·
            refine ⟨3418423980973503411556237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557898641298004548741649 3418423980973503411556237)
            ·
              refine ⟨1281908992865063779333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3418423980973503411556237 1281908992865063779333589)
              ·
                refine ⟨30044742020274932328131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1281908992865063779333589 30044742020274932328131)
                ·
                  rfl

theorem cell23_1579822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_1579822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579822 prefixEnd_1579822 := by exact prefixLift 1579822
  have htrace : WordTrace (prefixWord ++ tailWord_1579822) baseStart_1579822 baseEnd_1579822 := by
    simpa [prefixWord, tailWord_1579822, baseEnd_1579822] using wordTrace_append hprefix tailTrace_1579822
  have hstable : (prefixWord ++ tailWord_1579822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579822).length < 2 ^ (prefixWord ++ tailWord_1579822).sum := by decide
  have hdescent : baseEnd_1579822 < baseStart_1579822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579848 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1579848 : Nat := 118140960795 + 1579848 * 2 ^ 59
def prefixEnd_1579848 : Nat := 4983230072969 + 3 ^ 40 * 1579848 * 2
def baseEnd_1579848 : Nat := 270407128348146690378139

theorem tailTrace_1579848 : CollatzResearch.WordTrace tailWord_1579848 prefixEnd_1579848 270407128348146690378139 := by
  unfold tailWord_1579848
  simp only [CollatzResearch.WordTrace]
  refine ⟨28810895190243993701158099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38414526920325324934877465 28810895190243993701158099)
  ·
    refine ⟨43216342785365990551737149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28810895190243993701158099 43216342785365990551737149)
    ·
      refine ⟨16206128544512246456901431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43216342785365990551737149 16206128544512246456901431)
      ·
        refine ⟨24309192816768369685352147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16206128544512246456901431 24309192816768369685352147)
        ·
          refine ⟨36463789225152554528028221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24309192816768369685352147 36463789225152554528028221)
          ·
            refine ⟨13673920959432207948010583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36463789225152554528028221 13673920959432207948010583)
            ·
              refine ⟨20510881439148311922015875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13673920959432207948010583 20510881439148311922015875)
              ·
                refine ⟨30766322158722467883023813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20510881439148311922015875 30766322158722467883023813)
                ·
                  refine ⟨5768685404760462728066965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30766322158722467883023813 5768685404760462728066965)
                  ·
                    refine ⟨270407128348146690378139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5768685404760462728066965 270407128348146690378139)
                    ·
                      rfl

theorem cell23_1579848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1579848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579848 prefixEnd_1579848 := by exact prefixLift 1579848
  have htrace : WordTrace (prefixWord ++ tailWord_1579848) baseStart_1579848 baseEnd_1579848 := by
    simpa [prefixWord, tailWord_1579848, baseEnd_1579848] using wordTrace_append hprefix tailTrace_1579848
  have hstable : (prefixWord ++ tailWord_1579848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579848).length < 2 ^ (prefixWord ++ tailWord_1579848).sum := by decide
  have hdescent : baseEnd_1579848 < baseStart_1579848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579849 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_1579849 : Nat := 118140960795 + 1579849 * 2 ^ 59
def prefixEnd_1579849 : Nat := 4983230072969 + 3 ^ 40 * 1579849 * 2
def baseEnd_1579849 : Nat := 811221898525094567221913

theorem tailTrace_1579849 : CollatzResearch.WordTrace tailWord_1579849 prefixEnd_1579849 811221898525094567221913 := by
  unfold tailWord_1579849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57621826853484364573102601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38414551235656243048735067 57621826853484364573102601)
  ·
    refine ⟨43216370140113273429826951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57621826853484364573102601 43216370140113273429826951)
    ·
      refine ⟨64824555210169910144740427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43216370140113273429826951 64824555210169910144740427)
      ·
        refine ⟨97236832815254865217110641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64824555210169910144740427 97236832815254865217110641)
        ·
          refine ⟨72927624611441148912832981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97236832815254865217110641 72927624611441148912832981)
          ·
            refine ⟨1709241201830651927644523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 72927624611441148912832981 1709241201830651927644523)
            ·
              refine ⟨2563861802745977891466785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709241201830651927644523 2563861802745977891466785)
              ·
                refine ⟨1922896352059483418600089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563861802745977891466785 1922896352059483418600089)
                ·
                  refine ⟨1442172264044612563950067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922896352059483418600089 1442172264044612563950067)
                  ·
                    refine ⟨2163258396066918845925101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442172264044612563950067 2163258396066918845925101)
                    ·
                      refine ⟨811221898525094567221913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2163258396066918845925101 811221898525094567221913)
                      ·
                        rfl

theorem cell23_1579849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_1579849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579849 prefixEnd_1579849 := by exact prefixLift 1579849
  have htrace : WordTrace (prefixWord ++ tailWord_1579849) baseStart_1579849 baseEnd_1579849 := by
    simpa [prefixWord, tailWord_1579849, baseEnd_1579849] using wordTrace_append hprefix tailTrace_1579849
  have hstable : (prefixWord ++ tailWord_1579849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579849).length < 2 ^ (prefixWord ++ tailWord_1579849).sum := by decide
  have hdescent : baseEnd_1579849 < baseStart_1579849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579912 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 7]
def baseStart_1579912 : Nat := 118140960795 + 1579912 * 2 ^ 59
def prefixEnd_1579912 : Nat := 4983230072969 + 3 ^ 40 * 1579912 * 2
def baseEnd_1579912 : Nat := 90139360867369757859347

theorem tailTrace_1579912 : CollatzResearch.WordTrace tailWord_1579912 prefixEnd_1579912 90139360867369757859347 := by
  unfold tailWord_1579912
  simp only [CollatzResearch.WordTrace]
  refine ⟨28812062326128063166322995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38416083101504084221763993 28812062326128063166322995)
  ·
    refine ⟨43218093489192094749484493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28812062326128063166322995 43218093489192094749484493)
    ·
      refine ⟨16206785058447035531056685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43218093489192094749484493 16206785058447035531056685)
      ·
        refine ⟨6077544396917638324146257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16206785058447035531056685 6077544396917638324146257)
        ·
          refine ⟨4558158297688228743109693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6077544396917638324146257 4558158297688228743109693)
          ·
            refine ⟨1709309361633085778666135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4558158297688228743109693 1709309361633085778666135)
            ·
              refine ⟨2563964042449628667999203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709309361633085778666135 2563964042449628667999203)
              ·
                refine ⟨3845946063674443001998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563964042449628667999203 3845946063674443001998805)
                ·
                  refine ⟨90139360867369757859347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3845946063674443001998805 90139360867369757859347)
                  ·
                    rfl

theorem cell23_1579912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_1579912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579912 prefixEnd_1579912 := by exact prefixLift 1579912
  have htrace : WordTrace (prefixWord ++ tailWord_1579912) baseStart_1579912 baseEnd_1579912 := by
    simpa [prefixWord, tailWord_1579912, baseEnd_1579912] using wordTrace_append hprefix tailTrace_1579912
  have hstable : (prefixWord ++ tailWord_1579912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579912).length < 2 ^ (prefixWord ++ tailWord_1579912).sum := by decide
  have hdescent : baseEnd_1579912 < baseStart_1579912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579955 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 7, 4]
def baseStart_1579955 : Nat := 118140960795 + 1579955 * 2 ^ 59
def prefixEnd_1579955 : Nat := 4983230072969 + 3 ^ 40 * 1579955 * 2
def baseEnd_1579955 : Nat := 270425442491490384165475

theorem tailTrace_1579955 : CollatzResearch.WordTrace tailWord_1579955 prefixEnd_1579955 270425442491490384165475 := by
  unfold tailWord_1579955
  simp only [CollatzResearch.WordTrace]
  refine ⟨57625692991100344676461319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38417128660733563117640879 57625692991100344676461319)
  ·
    refine ⟨86438539486650517014691979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57625692991100344676461319 86438539486650517014691979)
    ·
      refine ⟨129657809229975775522037969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86438539486650517014691979 129657809229975775522037969)
      ·
        refine ⟨97243356922481831641528477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129657809229975775522037969 97243356922481831641528477)
        ·
          refine ⟨36466258845930686865573179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97243356922481831641528477 36466258845930686865573179)
          ·
            refine ⟨54699388268896030298359769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36466258845930686865573179 54699388268896030298359769)
            ·
              refine ⟨41024541201672022723769827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54699388268896030298359769 41024541201672022723769827)
              ·
                refine ⟨61536811802508034085654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41024541201672022723769827 61536811802508034085654741)
                ·
                  refine ⟨1442269026621282048882533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61536811802508034085654741 1442269026621282048882533)
                  ·
                    refine ⟨270425442491490384165475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442269026621282048882533 270425442491490384165475)
                    ·
                      rfl

theorem cell23_1579955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 4].length) (baseStart_1579955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579955 prefixEnd_1579955 := by exact prefixLift 1579955
  have htrace : WordTrace (prefixWord ++ tailWord_1579955) baseStart_1579955 baseEnd_1579955 := by
    simpa [prefixWord, tailWord_1579955, baseEnd_1579955] using wordTrace_append hprefix tailTrace_1579955
  have hstable : (prefixWord ++ tailWord_1579955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579955).length < 2 ^ (prefixWord ++ tailWord_1579955).sum := by decide
  have hdescent : baseEnd_1579955 < baseStart_1579955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579962 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_1579962 : Nat := 118140960795 + 1579962 * 2 ^ 59
def prefixEnd_1579962 : Nat := 4983230072969 + 3 ^ 40 * 1579962 * 2
def baseEnd_1579962 : Nat := 811279921839052625108893

theorem tailTrace_1579962 : CollatzResearch.WordTrace tailWord_1579962 prefixEnd_1579962 811279921839052625108893 := by
  unfold tailWord_1579962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14406487075518746217991535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38417298868049989914644093 14406487075518746217991535)
  ·
    refine ⟨21609730613278119326987303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14406487075518746217991535 21609730613278119326987303)
    ·
      refine ⟨32414595919917178990480955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21609730613278119326987303 32414595919917178990480955)
      ·
        refine ⟨48621893879875768485721433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32414595919917178990480955 48621893879875768485721433)
        ·
          refine ⟨36466420409906826364291075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48621893879875768485721433 36466420409906826364291075)
          ·
            refine ⟨54699630614860239546436613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36466420409906826364291075 54699630614860239546436613)
            ·
              refine ⟨10256180740286294914956865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54699630614860239546436613 10256180740286294914956865)
              ·
                refine ⟨7692135555214721186217649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10256180740286294914956865 7692135555214721186217649)
                ·
                  refine ⟨5769101666411040889663237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7692135555214721186217649 5769101666411040889663237)
                  ·
                    refine ⟨1081706562452070166811857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769101666411040889663237 1081706562452070166811857)
                    ·
                      refine ⟨811279921839052625108893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081706562452070166811857 811279921839052625108893)
                      ·
                        rfl

theorem cell23_1579962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_1579962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579962 prefixEnd_1579962 := by exact prefixLift 1579962
  have htrace : WordTrace (prefixWord ++ tailWord_1579962) baseStart_1579962 baseEnd_1579962 := by
    simpa [prefixWord, tailWord_1579962, baseEnd_1579962] using wordTrace_append hprefix tailTrace_1579962
  have hstable : (prefixWord ++ tailWord_1579962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579962).length < 2 ^ (prefixWord ++ tailWord_1579962).sum := by decide
  have hdescent : baseEnd_1579962 < baseStart_1579962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579985 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 6]
def baseStart_1579985 : Nat := 118140960795 + 1579985 * 2 ^ 59
def prefixEnd_1579985 : Nat := 4983230072969 + 3 ^ 40 * 1579985 * 2
def baseEnd_1579985 : Nat := 90143525766011781680143

theorem tailTrace_1579985 : CollatzResearch.WordTrace tailWord_1579985 prefixEnd_1579985 90143525766011781680143 := by
  unfold tailWord_1579985
  simp only [CollatzResearch.WordTrace]
  refine ⟨57626787180991659800053409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38417858120661106533368939 57626787180991659800053409)
  ·
    refine ⟨43220090385743744850040057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57626787180991659800053409 43220090385743744850040057)
    ·
      refine ⟨32415067789307808637530043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43220090385743744850040057 32415067789307808637530043)
      ·
        refine ⟨48622601683961712956295065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32415067789307808637530043 48622601683961712956295065)
        ·
          refine ⟨36466951262971284717221299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48622601683961712956295065 36466951262971284717221299)
          ·
            refine ⟨54700426894456927075831949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36466951262971284717221299 54700426894456927075831949)
            ·
              refine ⟨20512660085421347653436981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54700426894456927075831949 20512660085421347653436981)
              ·
                refine ⟨1923061883008251342509717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20512660085421347653436981 1923061883008251342509717)
                ·
                  refine ⟨90143525766011781680143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1923061883008251342509717 90143525766011781680143)
                  ·
                    rfl

theorem cell23_1579985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_1579985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579985 prefixEnd_1579985 := by exact prefixLift 1579985
  have htrace : WordTrace (prefixWord ++ tailWord_1579985) baseStart_1579985 baseEnd_1579985 := by
    simpa [prefixWord, tailWord_1579985, baseEnd_1579985] using wordTrace_append hprefix tailTrace_1579985
  have hstable : (prefixWord ++ tailWord_1579985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579985).length < 2 ^ (prefixWord ++ tailWord_1579985).sum := by decide
  have hdescent : baseEnd_1579985 < baseStart_1579985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579989 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1579989 : Nat := 118140960795 + 1579989 * 2 ^ 59
def prefixEnd_1579989 : Nat := 4983230072969 + 3 ^ 40 * 1579989 * 2
def baseEnd_1579989 : Nat := 270431261938908006490423

theorem tailTrace_1579989 : CollatzResearch.WordTrace tailWord_1579989 prefixEnd_1579989 270431261938908006490423 := by
  unfold tailWord_1579989
  simp only [CollatzResearch.WordTrace]
  refine ⟨57626933072977168483199021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38417955381984778988799347 57626933072977168483199021)
  ·
    refine ⟨21610099902366438181199633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57626933072977168483199021 21610099902366438181199633)
    ·
      refine ⟨16207574926774828635899725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21610099902366438181199633 16207574926774828635899725)
      ·
        refine ⟨6077840597540560738462397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16207574926774828635899725 6077840597540560738462397)
        ·
          refine ⟨2279190224077710276923399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6077840597540560738462397 2279190224077710276923399)
          ·
            refine ⟨3418785336116565415385099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279190224077710276923399 3418785336116565415385099)
            ·
              refine ⟨5128178004174848123077649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418785336116565415385099 5128178004174848123077649)
              ·
                refine ⟨3846133503131136092308237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128178004174848123077649 3846133503131136092308237)
                ·
                  refine ⟨1442300063674176034615589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3846133503131136092308237 1442300063674176034615589)
                  ·
                    refine ⟨270431261938908006490423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442300063674176034615589 270431261938908006490423)
                    ·
                      rfl

theorem cell23_1579989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1579989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1579989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1579989 prefixEnd_1579989 := by exact prefixLift 1579989
  have htrace : WordTrace (prefixWord ++ tailWord_1579989) baseStart_1579989 baseEnd_1579989 := by
    simpa [prefixWord, tailWord_1579989, baseEnd_1579989] using wordTrace_append hprefix tailTrace_1579989
  have hstable : (prefixWord ++ tailWord_1579989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579989).length < 2 ^ (prefixWord ++ tailWord_1579989).sum := by decide
  have hdescent : baseEnd_1579989 < baseStart_1579989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580022 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1580022 : Nat := 118140960795 + 1580022 * 2 ^ 59
def prefixEnd_1580022 : Nat := 4983230072969 + 3 ^ 40 * 1580022 * 2
def baseEnd_1580022 : Nat := 811310730678322390358617

theorem tailTrace_1580022 : CollatzResearch.WordTrace tailWord_1580022 prefixEnd_1580022 811310730678322390358617 := by
  unfold tailWord_1580022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601758542616100944946895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38418757787905076746100213 3601758542616100944946895)
  ·
    refine ⟨5402637813924151417420343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601758542616100944946895 5402637813924151417420343)
    ·
      refine ⟨8103956720886227126130515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5402637813924151417420343 8103956720886227126130515)
      ·
        refine ⟨12155935081329340689195773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8103956720886227126130515 12155935081329340689195773)
        ·
          refine ⟨4558475655498502758448415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12155935081329340689195773 4558475655498502758448415)
          ·
            refine ⟨6837713483247754137672623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558475655498502758448415 6837713483247754137672623)
            ·
              refine ⟨10256570224871631206508935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837713483247754137672623 10256570224871631206508935)
              ·
                refine ⟨15384855337307446809763403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256570224871631206508935 15384855337307446809763403)
                ·
                  refine ⟨23077283005961170214645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15384855337307446809763403 23077283005961170214645105)
                  ·
                    refine ⟨17307962254470877660983829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23077283005961170214645105 17307962254470877660983829)
                    ·
                      refine ⟨811310730678322390358617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17307962254470877660983829 811310730678322390358617)
                      ·
                        rfl

theorem cell23_1580022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1580022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580022 prefixEnd_1580022 := by exact prefixLift 1580022
  have htrace : WordTrace (prefixWord ++ tailWord_1580022) baseStart_1580022 baseEnd_1580022 := by
    simpa [prefixWord, tailWord_1580022, baseEnd_1580022] using wordTrace_append hprefix tailTrace_1580022
  have hstable : (prefixWord ++ tailWord_1580022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580022).length < 2 ^ (prefixWord ++ tailWord_1580022).sum := by decide
  have hdescent : baseEnd_1580022 < baseStart_1580022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580063 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 1, 1, 3]
def baseStart_1580063 : Nat := 118140960795 + 1580063 * 2 ^ 59
def prefixEnd_1580063 : Nat := 4983230072969 + 3 ^ 40 * 1580063 * 2
def baseEnd_1580063 : Nat := 811331783385156729945929

theorem tailTrace_1580063 : CollatzResearch.WordTrace tailWord_1580063 prefixEnd_1580063 811331783385156729945929 := by
  unfold tailWord_1580063
  simp only [CollatzResearch.WordTrace]
  refine ⟨57629632074709079121392843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38419754716472719414261895 57629632074709079121392843)
  ·
    refine ⟨86444448112063618682089265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57629632074709079121392843 86444448112063618682089265)
    ·
      refine ⟨64833336084047714011566949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86444448112063618682089265 64833336084047714011566949)
      ·
        refine ⟨12156250515758946377168803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64833336084047714011566949 12156250515758946377168803)
        ·
          refine ⟨18234375773638419565753205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156250515758946377168803 18234375773638419565753205)
          ·
            refine ⟨1709472728778601834289363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18234375773638419565753205 1709472728778601834289363)
            ·
              refine ⟨2564209093167902751434045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709472728778601834289363 2564209093167902751434045)
              ·
                refine ⟨961578409937963531787767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2564209093167902751434045 961578409937963531787767)
                ·
                  refine ⟨1442367614906945297681651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961578409937963531787767 1442367614906945297681651)
                  ·
                    refine ⟨2163551422360417946522477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442367614906945297681651 2163551422360417946522477)
                    ·
                      refine ⟨811331783385156729945929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2163551422360417946522477 811331783385156729945929)
                      ·
                        rfl

theorem cell23_1580063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_1580063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580063 prefixEnd_1580063 := by exact prefixLift 1580063
  have htrace : WordTrace (prefixWord ++ tailWord_1580063) baseStart_1580063 baseEnd_1580063 := by
    simpa [prefixWord, tailWord_1580063, baseEnd_1580063] using wordTrace_append hprefix tailTrace_1580063
  have hstable : (prefixWord ++ tailWord_1580063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580063).length < 2 ^ (prefixWord ++ tailWord_1580063).sum := by decide
  have hdescent : baseEnd_1580063 < baseStart_1580063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580092 : List Nat := [2, 2, 2, 2, 2, 3, 2, 8]
def baseStart_1580092 : Nat := 118140960795 + 1580092 * 2 ^ 59
def prefixEnd_1580092 : Nat := 4983230072969 + 3 ^ 40 * 1580092 * 2
def baseEnd_1580092 : Nat := 30049876826819893203085

theorem tailTrace_1580092 : CollatzResearch.WordTrace tailWord_1580092 prefixEnd_1580092 30049876826819893203085 := by
  unfold tailWord_1580092
  simp only [CollatzResearch.WordTrace]
  refine ⟨28815344895802008537099265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38420459861069344716132353 28815344895802008537099265)
  ·
    refine ⟨21611508671851506402824449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28815344895802008537099265 21611508671851506402824449)
    ·
      refine ⟨16208631503888629802118337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21611508671851506402824449 16208631503888629802118337)
      ·
        refine ⟨12156473627916472351588753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16208631503888629802118337 12156473627916472351588753)
        ·
          refine ⟨9117355220937354263691565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12156473627916472351588753 9117355220937354263691565)
          ·
            refine ⟨3419008207851507848884337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9117355220937354263691565 3419008207851507848884337)
            ·
              refine ⟨2564256155888630886663253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3419008207851507848884337 2564256155888630886663253)
              ·
                refine ⟨30049876826819893203085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2564256155888630886663253 30049876826819893203085)
                ·
                  rfl

theorem cell23_1580092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 8].length) (baseStart_1580092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580092 prefixEnd_1580092 := by exact prefixLift 1580092
  have htrace : WordTrace (prefixWord ++ tailWord_1580092) baseStart_1580092 baseEnd_1580092 := by
    simpa [prefixWord, tailWord_1580092, baseEnd_1580092] using wordTrace_append hprefix tailTrace_1580092
  have hstable : (prefixWord ++ tailWord_1580092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580092).length < 2 ^ (prefixWord ++ tailWord_1580092).sum := by decide
  have hdescent : baseEnd_1580092 < baseStart_1580092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580095 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1580095 : Nat := 118140960795 + 1580095 * 2 ^ 59
def prefixEnd_1580095 : Nat := 4983230072969 + 3 ^ 40 * 1580095 * 2
def baseEnd_1580095 : Nat := 811348214766100604745781

theorem tailTrace_1580095 : CollatzResearch.WordTrace tailWord_1580095 prefixEnd_1580095 811348214766100604745781 := by
  unfold tailWord_1580095
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630799210593148586557739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38420532807062099057705159 57630799210593148586557739)
  ·
    refine ⟨86446198815889722879836609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57630799210593148586557739 86446198815889722879836609)
    ·
      refine ⟨64834649111917292159877457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86446198815889722879836609 64834649111917292159877457)
      ·
        refine ⟨48625986833937969119908093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64834649111917292159877457 48625986833937969119908093)
        ·
          refine ⟨18234745062726738419965535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48625986833937969119908093 18234745062726738419965535)
          ·
            refine ⟨27352117594090107629948303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234745062726738419965535 27352117594090107629948303)
            ·
              refine ⟨41028176391135161444922455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27352117594090107629948303 41028176391135161444922455)
              ·
                refine ⟨61542264586702742167383683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41028176391135161444922455 61542264586702742167383683)
                ·
                  refine ⟨92313396880054113251075525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61542264586702742167383683 92313396880054113251075525)
                  ·
                    refine ⟨17308761915010146234576661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92313396880054113251075525 17308761915010146234576661)
                    ·
                      refine ⟨811348214766100604745781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17308761915010146234576661 811348214766100604745781)
                      ·
                        rfl

theorem cell23_1580095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1580095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580095 prefixEnd_1580095 := by exact prefixLift 1580095
  have htrace : WordTrace (prefixWord ++ tailWord_1580095) baseStart_1580095 baseEnd_1580095 := by
    simpa [prefixWord, tailWord_1580095, baseEnd_1580095] using wordTrace_append hprefix tailTrace_1580095
  have hstable : (prefixWord ++ tailWord_1580095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580095).length < 2 ^ (prefixWord ++ tailWord_1580095).sum := by decide
  have hdescent : baseEnd_1580095 < baseStart_1580095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580105 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_1580105 : Nat := 118140960795 + 1580105 * 2 ^ 59
def prefixEnd_1580105 : Nat := 4983230072969 + 3 ^ 40 * 1580105 * 2
def baseEnd_1580105 : Nat := 270451116524215188540245

theorem tailTrace_1580105 : CollatzResearch.WordTrace tailWord_1580105 prefixEnd_1580105 270451116524215188540245 := by
  unfold tailWord_1580105
  simp only [CollatzResearch.WordTrace]
  refine ⟨57631163940556920294421769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38420775960371280196281179 57631163940556920294421769)
  ·
    refine ⟨43223372955417690220816327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57631163940556920294421769 43223372955417690220816327)
    ·
      refine ⟨64835059433126535331224491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43223372955417690220816327 64835059433126535331224491)
      ·
        refine ⟨97252589149689802996836737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64835059433126535331224491 97252589149689802996836737)
        ·
          refine ⟨72939441862267352247627553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97252589149689802996836737 72939441862267352247627553)
          ·
            refine ⟨54704581396700514185720665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72939441862267352247627553 54704581396700514185720665)
            ·
              refine ⟨41028436047525385639290499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54704581396700514185720665 41028436047525385639290499)
              ·
                refine ⟨61542654071288078458935749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41028436047525385639290499 61542654071288078458935749)
                ·
                  refine ⟨11539247638366514711050453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61542654071288078458935749 11539247638366514711050453)
                  ·
                    refine ⟨270451116524215188540245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11539247638366514711050453 270451116524215188540245)
                    ·
                      rfl

theorem cell23_1580105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_1580105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580105 prefixEnd_1580105 := by exact prefixLift 1580105
  have htrace : WordTrace (prefixWord ++ tailWord_1580105) baseStart_1580105 baseEnd_1580105 := by
    simpa [prefixWord, tailWord_1580105, baseEnd_1580105] using wordTrace_append hprefix tailTrace_1580105
  have hstable : (prefixWord ++ tailWord_1580105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580105).length < 2 ^ (prefixWord ++ tailWord_1580105).sum := by decide
  have hdescent : baseEnd_1580105 < baseStart_1580105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580199 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 7]
def baseStart_1580199 : Nat := 118140960795 + 1580199 * 2 ^ 59
def prefixEnd_1580199 : Nat := 4983230072969 + 3 ^ 40 * 1580199 * 2
def baseEnd_1580199 : Nat := 90155735194907577538367

theorem tailTrace_1580199 : CollatzResearch.WordTrace tailWord_1580199 prefixEnd_1580199 90155735194907577538367 := by
  unfold tailWord_1580199
  simp only [CollatzResearch.WordTrace]
  refine ⟨57634592402216374348343651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38423061601477582898895767 57634592402216374348343651)
  ·
    refine ⟨86451888603324561522515477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57634592402216374348343651 86451888603324561522515477)
    ·
      refine ⟨4052432278280838821367913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86451888603324561522515477 4052432278280838821367913)
      ·
        refine ⟨3039324208710629116025935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4052432278280838821367913 3039324208710629116025935)
        ·
          refine ⟨4558986313065943674038903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039324208710629116025935 4558986313065943674038903)
          ·
            refine ⟨6838479469598915511058355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558986313065943674038903 6838479469598915511058355)
            ·
              refine ⟨10257719204398373266587533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838479469598915511058355 10257719204398373266587533)
              ·
                refine ⟨3846644701649389974970325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10257719204398373266587533 3846644701649389974970325)
                ·
                  refine ⟨90155735194907577538367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3846644701649389974970325 90155735194907577538367)
                  ·
                    rfl

theorem cell23_1580199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 7].length) (baseStart_1580199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580199 prefixEnd_1580199 := by exact prefixLift 1580199
  have htrace : WordTrace (prefixWord ++ tailWord_1580199) baseStart_1580199 baseEnd_1580199 := by
    simpa [prefixWord, tailWord_1580199, baseEnd_1580199] using wordTrace_append hprefix tailTrace_1580199
  have hstable : (prefixWord ++ tailWord_1580199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580199).length < 2 ^ (prefixWord ++ tailWord_1580199).sum := by decide
  have hdescent : baseEnd_1580199 < baseStart_1580199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580210 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_1580210 : Nat := 118140960795 + 1580210 * 2 ^ 59
def prefixEnd_1580210 : Nat := 4983230072969 + 3 ^ 40 * 1580210 * 2
def baseEnd_1580210 : Nat := 811407265041367654807753

theorem tailTrace_1580210 : CollatzResearch.WordTrace tailWord_1580210 prefixEnd_1580210 811407265041367654807753 := by
  unfold tailWord_1580210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408748401294130806748521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38423329070117682151329389 14408748401294130806748521)
  ·
    refine ⟨10806561300970598105061391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14408748401294130806748521 10806561300970598105061391)
    ·
      refine ⟨16209841951455897157592087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806561300970598105061391 16209841951455897157592087)
      ·
        refine ⟨24314762927183845736388131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16209841951455897157592087 24314762927183845736388131)
        ·
          refine ⟨36472144390775768604582197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24314762927183845736388131 36472144390775768604582197)
          ·
            refine ⟨3419263536635228306679581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36472144390775768604582197 3419263536635228306679581)
            ·
              refine ⟨1282223826238210615004843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419263536635228306679581 1282223826238210615004843)
              ·
                refine ⟨1923335739357315922507265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282223826238210615004843 1923335739357315922507265)
                ·
                  refine ⟨1442501804517986941880449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923335739357315922507265 1442501804517986941880449)
                  ·
                    refine ⟨1081876353388490206410337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442501804517986941880449 1081876353388490206410337)
                    ·
                      refine ⟨811407265041367654807753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1081876353388490206410337 811407265041367654807753)
                      ·
                        rfl

theorem cell23_1580210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_1580210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580210 prefixEnd_1580210 := by exact prefixLift 1580210
  have htrace : WordTrace (prefixWord ++ tailWord_1580210) baseStart_1580210 baseEnd_1580210 := by
    simpa [prefixWord, tailWord_1580210, baseEnd_1580210] using wordTrace_append hprefix tailTrace_1580210
  have hstable : (prefixWord ++ tailWord_1580210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580210).length < 2 ^ (prefixWord ++ tailWord_1580210).sum := by decide
  have hdescent : baseEnd_1580210 < baseStart_1580210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580230 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1580230 : Nat := 118140960795 + 1580230 * 2 ^ 59
def prefixEnd_1580230 : Nat := 4983230072969 + 3 ^ 40 * 1580230 * 2
def baseEnd_1580230 : Nat := 811417534654457576557661

theorem tailTrace_1580230 : CollatzResearch.WordTrace tailWord_1580230 prefixEnd_1580230 811417534654457576557661 := by
  unfold tailWord_1580230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801116345784502082585067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38423815376736044428481429 1801116345784502082585067)
  ·
    refine ⟨2701674518676753123877601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801116345784502082585067 2701674518676753123877601)
    ·
      refine ⟨2026255889007564842908201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701674518676753123877601 2026255889007564842908201)
      ·
        refine ⟨1519691916755673632181151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026255889007564842908201 1519691916755673632181151)
        ·
          refine ⟨2279537875133510448271727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519691916755673632181151 2279537875133510448271727)
          ·
            refine ⟨3419306812700265672407591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279537875133510448271727 3419306812700265672407591)
            ·
              refine ⟨5128960219050398508611387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419306812700265672407591 5128960219050398508611387)
              ·
                refine ⟨7693440328575597762917081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5128960219050398508611387 7693440328575597762917081)
                ·
                  refine ⟨5770080246431698322187811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7693440328575597762917081 5770080246431698322187811)
                  ·
                    refine ⟨8655120369647547483281717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770080246431698322187811 8655120369647547483281717)
                    ·
                      refine ⟨811417534654457576557661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8655120369647547483281717 811417534654457576557661)
                      ·
                        rfl

theorem cell23_1580230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1580230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580230 prefixEnd_1580230 := by exact prefixLift 1580230
  have htrace : WordTrace (prefixWord ++ tailWord_1580230) baseStart_1580230 baseEnd_1580230 := by
    simpa [prefixWord, tailWord_1580230, baseEnd_1580230] using wordTrace_append hprefix tailTrace_1580230
  have hstable : (prefixWord ++ tailWord_1580230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580230).length < 2 ^ (prefixWord ++ tailWord_1580230).sum := by decide
  have hdescent : baseEnd_1580230 < baseStart_1580230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580353 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1580353 : Nat := 118140960795 + 1580353 * 2 ^ 59
def prefixEnd_1580353 : Nat := 4983230072969 + 3 ^ 40 * 1580353 * 2
def baseEnd_1580353 : Nat := 270493564258320198439865

theorem tailTrace_1580353 : CollatzResearch.WordTrace tailWord_1580353 prefixEnd_1580353 270493564258320198439865 := by
  unfold tailWord_1580353
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640209243658458649449713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38426806162438972432966475 57640209243658458649449713)
  ·
    refine ⟨43230156932743843987087285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57640209243658458649449713 43230156932743843987087285)
    ·
      refine ⟨4052827212444735373789433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43230156932743843987087285 4052827212444735373789433)
      ·
        refine ⟨3039620409333551530342075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4052827212444735373789433 3039620409333551530342075)
        ·
          refine ⟨4559430614000327295513113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039620409333551530342075 4559430614000327295513113)
          ·
            refine ⟨3419572960500245471634835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4559430614000327295513113 3419572960500245471634835)
            ·
              refine ⟨5129359440750368207452253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419572960500245471634835 5129359440750368207452253)
              ·
                refine ⟨1923509790281388077794595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5129359440750368207452253 1923509790281388077794595)
                ·
                  refine ⟨2885264685422082116691893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923509790281388077794595 2885264685422082116691893)
                  ·
                    refine ⟨270493564258320198439865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2885264685422082116691893 270493564258320198439865)
                    ·
                      rfl

theorem cell23_1580353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1580353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580353 prefixEnd_1580353 := by exact prefixLift 1580353
  have htrace : WordTrace (prefixWord ++ tailWord_1580353) baseStart_1580353 baseEnd_1580353 := by
    simpa [prefixWord, tailWord_1580353, baseEnd_1580353] using wordTrace_append hprefix tailTrace_1580353
  have hstable : (prefixWord ++ tailWord_1580353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580353).length < 2 ^ (prefixWord ++ tailWord_1580353).sum := by decide
  have hdescent : baseEnd_1580353 < baseStart_1580353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580366 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1580366 : Nat := 118140960795 + 1580366 * 2 ^ 59
def prefixEnd_1580366 : Nat := 4983230072969 + 3 ^ 40 * 1580366 * 2
def baseEnd_1580366 : Nat := 270495789341156348152345

theorem tailTrace_1580366 : CollatzResearch.WordTrace tailWord_1580366 prefixEnd_1580366 270495789341156348152345 := by
  unfold tailWord_1580366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205085424076420233709119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38427122261740907913115301 7205085424076420233709119)
  ·
    refine ⟨10807628136114630350563679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205085424076420233709119 10807628136114630350563679)
    ·
      refine ⟨16211442204171945525845519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807628136114630350563679 16211442204171945525845519)
      ·
        refine ⟨24317163306257918288768279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211442204171945525845519 24317163306257918288768279)
        ·
          refine ⟨36475744959386877433152419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24317163306257918288768279 36475744959386877433152419)
          ·
            refine ⟨54713617439080316149728629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36475744959386877433152419 54713617439080316149728629)
            ·
              refine ⟨5129401634913779639037059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54713617439080316149728629 5129401634913779639037059)
              ·
                refine ⟨7694102452370669458555589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129401634913779639037059 7694102452370669458555589)
                ·
                  refine ⟨1442644209819500523479173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7694102452370669458555589 1442644209819500523479173)
                  ·
                    refine ⟨270495789341156348152345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442644209819500523479173 270495789341156348152345)
                    ·
                      rfl

theorem cell23_1580366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1580366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580366 prefixEnd_1580366 := by exact prefixLift 1580366
  have htrace : WordTrace (prefixWord ++ tailWord_1580366) baseStart_1580366 baseEnd_1580366 := by
    simpa [prefixWord, tailWord_1580366, baseEnd_1580366] using wordTrace_append hprefix tailTrace_1580366
  have hstable : (prefixWord ++ tailWord_1580366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580366).length < 2 ^ (prefixWord ++ tailWord_1580366).sum := by decide
  have hdescent : baseEnd_1580366 < baseStart_1580366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580369 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1580369 : Nat := 118140960795 + 1580369 * 2 ^ 59
def prefixEnd_1580369 : Nat := 4983230072969 + 3 ^ 40 * 1580369 * 2
def baseEnd_1580369 : Nat := 811488908465432532719521

theorem tailTrace_1580369 : CollatzResearch.WordTrace tailWord_1580369 prefixEnd_1580369 811488908465432532719521 := by
  unfold tailWord_1580369
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640792811600493382032161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38427195207733662254688107 57640792811600493382032161)
  ·
    refine ⟨43230594608700370036524121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57640792811600493382032161 43230594608700370036524121)
    ·
      refine ⟨32422945956525277527393091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43230594608700370036524121 32422945956525277527393091)
      ·
        refine ⟨48634418934787916291089637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32422945956525277527393091 48634418934787916291089637)
        ·
          refine ⟨9118953550272734304579307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48634418934787916291089637 9118953550272734304579307)
          ·
            refine ⟨13678430325409101456868961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118953550272734304579307 13678430325409101456868961)
            ·
              refine ⟨10258822744056826092651721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13678430325409101456868961 10258822744056826092651721)
              ·
                refine ⟨7694117058042619569488791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10258822744056826092651721 7694117058042619569488791)
                ·
                  refine ⟨11541175587063929354233187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694117058042619569488791 11541175587063929354233187)
                  ·
                    refine ⟨17311763380595894031349781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11541175587063929354233187 17311763380595894031349781)
                    ·
                      refine ⟨811488908465432532719521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17311763380595894031349781 811488908465432532719521)
                      ·
                        rfl

theorem cell23_1580369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1580369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580369 prefixEnd_1580369 := by exact prefixLift 1580369
  have htrace : WordTrace (prefixWord ++ tailWord_1580369) baseStart_1580369 baseEnd_1580369 := by
    simpa [prefixWord, tailWord_1580369, baseEnd_1580369] using wordTrace_append hprefix tailTrace_1580369
  have hstable : (prefixWord ++ tailWord_1580369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580369).length < 2 ^ (prefixWord ++ tailWord_1580369).sum := by decide
  have hdescent : baseEnd_1580369 < baseStart_1580369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580374 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1580374 : Nat := 118140960795 + 1580374 * 2 ^ 59
def prefixEnd_1580374 : Nat := 4983230072969 + 3 ^ 40 * 1580374 * 2
def baseEnd_1580374 : Nat := 90165719540967223684111

theorem tailTrace_1580374 : CollatzResearch.WordTrace tailWord_1580374 prefixEnd_1580374 90165719540967223684111 := by
  unfold tailWord_1580374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602560948536398702247761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38427316784388252823976117 3602560948536398702247761)
  ·
    refine ⟨2701920711402299026685821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3602560948536398702247761 2701920711402299026685821)
    ·
      refine ⟨1013220266775862135007183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2701920711402299026685821 1013220266775862135007183)
      ·
        refine ⟨1519830400163793202510775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013220266775862135007183 1519830400163793202510775)
        ·
          refine ⟨2279745600245689803766163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519830400163793202510775 2279745600245689803766163)
          ·
            refine ⟨3419618400368534705649245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279745600245689803766163 3419618400368534705649245)
            ·
              refine ⟨1282356900138200514618467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419618400368534705649245 1282356900138200514618467)
              ·
                refine ⟨1923535350207300771927701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282356900138200514618467 1923535350207300771927701)
                ·
                  refine ⟨90165719540967223684111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1923535350207300771927701 90165719540967223684111)
                  ·
                    rfl

theorem cell23_1580374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1580374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580374 prefixEnd_1580374 := by exact prefixLift 1580374
  have htrace : WordTrace (prefixWord ++ tailWord_1580374) baseStart_1580374 baseEnd_1580374 := by
    simpa [prefixWord, tailWord_1580374, baseEnd_1580374] using wordTrace_append hprefix tailTrace_1580374
  have hstable : (prefixWord ++ tailWord_1580374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580374).length < 2 ^ (prefixWord ++ tailWord_1580374).sum := by decide
  have hdescent : baseEnd_1580374 < baseStart_1580374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580386 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1580386 : Nat := 118140960795 + 1580386 * 2 ^ 59
def prefixEnd_1580386 : Nat := 4983230072969 + 3 ^ 40 * 1580386 * 2
def baseEnd_1580386 : Nat := 811497637636558966206943

theorem tailTrace_1580386 : CollatzResearch.WordTrace tailWord_1580386 prefixEnd_1580386 811497637636558966206943 := by
  unfold tailWord_1580386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410353213134726321350253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38427608568359270190267341 14410353213134726321350253)
  ·
    refine ⟨5403882454925522370506345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14410353213134726321350253 5403882454925522370506345)
    ·
      refine ⟨4052911841194141777879759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5403882454925522370506345 4052911841194141777879759)
      ·
        refine ⟨6079367761791212666819639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052911841194141777879759 6079367761791212666819639)
        ·
          refine ⟨9119051642686819000229459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079367761791212666819639 9119051642686819000229459)
          ·
            refine ⟨13678577464030228500344189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119051642686819000229459 13678577464030228500344189)
            ·
              refine ⟨5129466549011335687629071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13678577464030228500344189 5129466549011335687629071)
              ·
                refine ⟨7694199823517003531443607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129466549011335687629071 7694199823517003531443607)
                ·
                  refine ⟨11541299735275505297165411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694199823517003531443607 11541299735275505297165411)
                  ·
                    refine ⟨17311949602913257945748117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11541299735275505297165411 17311949602913257945748117)
                    ·
                      refine ⟨811497637636558966206943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17311949602913257945748117 811497637636558966206943)
                      ·
                        rfl

theorem cell23_1580386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1580386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580386 prefixEnd_1580386 := by exact prefixLift 1580386
  have htrace : WordTrace (prefixWord ++ tailWord_1580386) baseStart_1580386 baseEnd_1580386 := by
    simpa [prefixWord, tailWord_1580386, baseEnd_1580386] using wordTrace_append hprefix tailTrace_1580386
  have hstable : (prefixWord ++ tailWord_1580386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580386).length < 2 ^ (prefixWord ++ tailWord_1580386).sum := by decide
  have hdescent : baseEnd_1580386 < baseStart_1580386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580396 : List Nat := [2, 2, 1, 1, 5, 1, 4, 7]
def baseStart_1580396 : Nat := 118140960795 + 1580396 * 2 ^ 59
def prefixEnd_1580396 : Nat := 4983230072969 + 3 ^ 40 * 1580396 * 2
def baseEnd_1580396 : Nat := 30055658238633478780811

theorem tailTrace_1580396 : CollatzResearch.WordTrace tailWord_1580396 prefixEnd_1580396 30055658238633478780811 := by
  unfold tailWord_1580396
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820888791251338496632521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38427851721668451328843361 28820888791251338496632521)
  ·
    refine ⟨21615666593438503872474391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28820888791251338496632521 21615666593438503872474391)
    ·
      refine ⟨32423499890157755808711587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21615666593438503872474391 32423499890157755808711587)
      ·
        refine ⟨48635249835236633713067381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32423499890157755808711587 48635249835236633713067381)
        ·
          refine ⟨4559554672053434410600067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48635249835236633713067381 4559554672053434410600067)
          ·
            refine ⟨6839332008080151615900101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559554672053434410600067 6839332008080151615900101)
            ·
              refine ⟨1282374751515028427981269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6839332008080151615900101 1282374751515028427981269)
              ·
                refine ⟨30055658238633478780811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1282374751515028427981269 30055658238633478780811)
                ·
                  rfl

theorem cell23_1580396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 7].length) (baseStart_1580396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580396 prefixEnd_1580396 := by exact prefixLift 1580396
  have htrace : WordTrace (prefixWord ++ tailWord_1580396) baseStart_1580396 baseEnd_1580396 := by
    simpa [prefixWord, tailWord_1580396, baseEnd_1580396] using wordTrace_append hprefix tailTrace_1580396
  have hstable : (prefixWord ++ tailWord_1580396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580396).length < 2 ^ (prefixWord ++ tailWord_1580396).sum := by decide
  have hdescent : baseEnd_1580396 < baseStart_1580396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580423 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1580423 : Nat := 118140960795 + 1580423 * 2 ^ 59
def prefixEnd_1580423 : Nat := 4983230072969 + 3 ^ 40 * 1580423 * 2
def baseEnd_1580423 : Nat := 811516636420775321444273

theorem tailTrace_1580423 : CollatzResearch.WordTrace tailWord_1580423 prefixEnd_1580423 811516636420775321444273 := by
  unfold tailWord_1580423
  simp only [CollatzResearch.WordTrace]
  refine ⟨57642762353404860604497923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38428508235603240402998615 57642762353404860604497923)
  ·
    refine ⟨86464143530107290906746885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57642762353404860604497923 86464143530107290906746885)
    ·
      refine ⟨16212026911895117045015041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86464143530107290906746885 16212026911895117045015041)
      ·
        refine ⟨12159020183921337783761281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16212026911895117045015041 12159020183921337783761281)
        ·
          refine ⟨9119265137941003337820961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12159020183921337783761281 9119265137941003337820961)
          ·
            refine ⟨6839448853455752503365721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9119265137941003337820961 6839448853455752503365721)
            ·
              refine ⟨5129586640091814377524291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839448853455752503365721 5129586640091814377524291)
              ·
                refine ⟨7694379960137721566286437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129586640091814377524291 7694379960137721566286437)
                ·
                  refine ⟨1442696242525822793678707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7694379960137721566286437 1442696242525822793678707)
                  ·
                    refine ⟨2164044363788734190518061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442696242525822793678707 2164044363788734190518061)
                    ·
                      refine ⟨811516636420775321444273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164044363788734190518061 811516636420775321444273)
                      ·
                        rfl

theorem cell23_1580423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1580423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580423 prefixEnd_1580423 := by exact prefixLift 1580423
  have htrace : WordTrace (prefixWord ++ tailWord_1580423) baseStart_1580423 baseEnd_1580423 := by
    simpa [prefixWord, tailWord_1580423, baseEnd_1580423] using wordTrace_append hprefix tailTrace_1580423
  have hstable : (prefixWord ++ tailWord_1580423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580423).length < 2 ^ (prefixWord ++ tailWord_1580423).sum := by decide
  have hdescent : baseEnd_1580423 < baseStart_1580423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580424 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1580424 : Nat := 118140960795 + 1580424 * 2 ^ 59
def prefixEnd_1580424 : Nat := 4983230072969 + 3 ^ 40 * 1580424 * 2
def baseEnd_1580424 : Nat := 811517149901429817531769

theorem tailTrace_1580424 : CollatzResearch.WordTrace tailWord_1580424 prefixEnd_1580424 811517149901429817531769 := by
  unfold tailWord_1580424
  simp only [CollatzResearch.WordTrace]
  refine ⟨28821399413200618887642163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38428532550934158516856217 28821399413200618887642163)
  ·
    refine ⟨43232099119800928331463245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28821399413200618887642163 43232099119800928331463245)
    ·
      refine ⟨16212037169925348124298717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43232099119800928331463245 16212037169925348124298717)
      ·
        refine ⟨6079513938722005546612019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16212037169925348124298717 6079513938722005546612019)
        ·
          refine ⟨9119270908083008319918029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079513938722005546612019 9119270908083008319918029)
          ·
            refine ⟨3419726590531128119969261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9119270908083008319918029 3419726590531128119969261)
            ·
              refine ⟨1282397471449173044988473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419726590531128119969261 1282397471449173044988473)
              ·
                refine ⟨961798103586879783741355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282397471449173044988473 961798103586879783741355)
                ·
                  refine ⟨1442697155380319675612033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961798103586879783741355 1442697155380319675612033)
                  ·
                    refine ⟨1082022866535239756709025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442697155380319675612033 1082022866535239756709025)
                    ·
                      refine ⟨811517149901429817531769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082022866535239756709025 811517149901429817531769)
                      ·
                        rfl

theorem cell23_1580424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1580424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580424 prefixEnd_1580424 := by exact prefixLift 1580424
  have htrace : WordTrace (prefixWord ++ tailWord_1580424) baseStart_1580424 baseEnd_1580424 := by
    simpa [prefixWord, tailWord_1580424, baseEnd_1580424] using wordTrace_append hprefix tailTrace_1580424
  have hstable : (prefixWord ++ tailWord_1580424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580424).length < 2 ^ (prefixWord ++ tailWord_1580424).sum := by decide
  have hdescent : baseEnd_1580424 < baseStart_1580424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580434 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1580434 : Nat := 118140960795 + 1580434 * 2 ^ 59
def prefixEnd_1580434 : Nat := 4983230072969 + 3 ^ 40 * 1580434 * 2
def baseEnd_1580434 : Nat := 270507428235991592802241

theorem tailTrace_1580434 : CollatzResearch.WordTrace tailWord_1580434 prefixEnd_1580434 270507428235991592802241 := by
  unfold tailWord_1580434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410790889091252370787089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38428775704243339655432237 14410790889091252370787089)
  ·
    refine ⟨10808093166818439278090317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14410790889091252370787089 10808093166818439278090317)
    ·
      refine ⟨4053034937556914729283869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10808093166818439278090317 4053034937556914729283869)
      ·
        refine ⟨1519888101583843023481451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4053034937556914729283869 1519888101583843023481451)
        ·
          refine ⟨2279832152375764535222177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519888101583843023481451 2279832152375764535222177)
          ·
            refine ⟨1709874114281823401416633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279832152375764535222177 1709874114281823401416633)
            ·
              refine ⟨1282405585711367551062475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709874114281823401416633 1282405585711367551062475)
              ·
                refine ⟨1923608378567051326593713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282405585711367551062475 1923608378567051326593713)
                ·
                  refine ⟨1442706283925288494945285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923608378567051326593713 1442706283925288494945285)
                  ·
                    refine ⟨270507428235991592802241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442706283925288494945285 270507428235991592802241)
                    ·
                      rfl

theorem cell23_1580434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1580434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580434 prefixEnd_1580434 := by exact prefixLift 1580434
  have htrace : WordTrace (prefixWord ++ tailWord_1580434) baseStart_1580434 baseEnd_1580434 := by
    simpa [prefixWord, tailWord_1580434, baseEnd_1580434] using wordTrace_append hprefix tailTrace_1580434
  have hstable : (prefixWord ++ tailWord_1580434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580434).length < 2 ^ (prefixWord ++ tailWord_1580434).sum := by decide
  have hdescent : baseEnd_1580434 < baseStart_1580434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580439 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 8]
def baseStart_1580439 : Nat := 118140960795 + 1580439 * 2 ^ 59
def prefixEnd_1580439 : Nat := 4983230072969 + 3 ^ 40 * 1580439 * 2
def baseEnd_1580439 : Nat := 270508284037082419614733

theorem tailTrace_1580439 : CollatzResearch.WordTrace tailWord_1580439 prefixEnd_1580439 270508284037082419614733 := by
  unfold tailWord_1580439
  simp only [CollatzResearch.WordTrace]
  refine ⟨57643345921346895337080371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38428897280897930224720247 57643345921346895337080371)
  ·
    refine ⟨86465018882020343005620557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57643345921346895337080371 86465018882020343005620557)
    ·
      refine ⟨32424382080757628627107709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86465018882020343005620557 32424382080757628627107709)
      ·
        refine ⟨12159143280284110735165391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32424382080757628627107709 12159143280284110735165391)
        ·
          refine ⟨18238714920426166102748087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12159143280284110735165391 18238714920426166102748087)
          ·
            refine ⟨27358072380639249154122131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18238714920426166102748087 27358072380639249154122131)
            ·
              refine ⟨41037108570958873731183197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27358072380639249154122131 41037108570958873731183197)
              ·
                refine ⟨15388915714109577649193699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41037108570958873731183197 15388915714109577649193699)
                ·
                  refine ⟨23083373571164366473790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15388915714109577649193699 23083373571164366473790549)
                  ·
                    refine ⟨270508284037082419614733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23083373571164366473790549 270508284037082419614733)
                    ·
                      rfl

theorem cell23_1580439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_1580439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580439 prefixEnd_1580439 := by exact prefixLift 1580439
  have htrace : WordTrace (prefixWord ++ tailWord_1580439) baseStart_1580439 baseEnd_1580439 := by
    simpa [prefixWord, tailWord_1580439, baseEnd_1580439] using wordTrace_append hprefix tailTrace_1580439
  have hstable : (prefixWord ++ tailWord_1580439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580439).length < 2 ^ (prefixWord ++ tailWord_1580439).sum := by decide
  have hdescent : baseEnd_1580439 < baseStart_1580439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580444 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1580444 : Nat := 118140960795 + 1580444 * 2 ^ 59
def prefixEnd_1580444 : Nat := 4983230072969 + 3 ^ 40 * 1580444 * 2
def baseEnd_1580444 : Nat := 811527419514519739281677

theorem tailTrace_1580444 : CollatzResearch.WordTrace tailWord_1580444 prefixEnd_1580444 811527419514519739281677 := by
  unfold tailWord_1580444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28821764143164390595506193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38429018857552520794008257 28821764143164390595506193)
  ·
    refine ⟨21616323107373292946629645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28821764143164390595506193 21616323107373292946629645)
    ·
      refine ⟨8106121165264984854986117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21616323107373292946629645 8106121165264984854986117)
      ·
        refine ⟨1519897718487184660309897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8106121165264984854986117 1519897718487184660309897)
        ·
          refine ⟨1139923288865388495232423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519897718487184660309897 1139923288865388495232423)
          ·
            refine ⟨1709884933298082742848635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139923288865388495232423 1709884933298082742848635)
            ·
              refine ⟨2564827399947124114272953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709884933298082742848635 2564827399947124114272953)
              ·
                refine ⟨1923620549960343085704715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564827399947124114272953 1923620549960343085704715)
                ·
                  refine ⟨2885430824940514628557073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923620549960343085704715 2885430824940514628557073)
                  ·
                    refine ⟨2164073118705385971417805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885430824940514628557073 2164073118705385971417805)
                    ·
                      refine ⟨811527419514519739281677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164073118705385971417805 811527419514519739281677)
                      ·
                        rfl

theorem cell23_1580444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1580444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580444 prefixEnd_1580444 := by exact prefixLift 1580444
  have htrace : WordTrace (prefixWord ++ tailWord_1580444) baseStart_1580444 baseEnd_1580444 := by
    simpa [prefixWord, tailWord_1580444, baseEnd_1580444] using wordTrace_append hprefix tailTrace_1580444
  have hstable : (prefixWord ++ tailWord_1580444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580444).length < 2 ^ (prefixWord ++ tailWord_1580444).sum := by decide
  have hdescent : baseEnd_1580444 < baseStart_1580444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580450 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1580450 : Nat := 118140960795 + 1580450 * 2 ^ 59
def prefixEnd_1580450 : Nat := 4983230072969 + 3 ^ 40 * 1580450 * 2
def baseEnd_1580450 : Nat := 811530500398446715806649

theorem tailTrace_1580450 : CollatzResearch.WordTrace tailWord_1580450 prefixEnd_1580450 811530500398446715806649 := by
  unfold tailWord_1580450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410936781076761053932701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38429164749538029477153869 14410936781076761053932701)
  ·
    refine ⟨5404101292903785395224763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14410936781076761053932701 5404101292903785395224763)
    ·
      refine ⟨8106151939355678092837145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404101292903785395224763 8106151939355678092837145)
      ·
        refine ⟨6079613954516758569627859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8106151939355678092837145 6079613954516758569627859)
        ·
          refine ⟨9119420931775137854441789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079613954516758569627859 9119420931775137854441789)
          ·
            refine ⟨3419782849415676695415671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9119420931775137854441789 3419782849415676695415671)
            ·
              refine ⟨5129674274123515043123507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419782849415676695415671 5129674274123515043123507)
              ·
                refine ⟨7694511411185272564685261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129674274123515043123507 7694511411185272564685261)
                ·
                  refine ⟨2885441779194477211756973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7694511411185272564685261 2885441779194477211756973)
                  ·
                    refine ⟨1082040667197928954408865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885441779194477211756973 1082040667197928954408865)
                    ·
                      refine ⟨811530500398446715806649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082040667197928954408865 811530500398446715806649)
                      ·
                        rfl

theorem cell23_1580450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1580450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580450 prefixEnd_1580450 := by exact prefixLift 1580450
  have htrace : WordTrace (prefixWord ++ tailWord_1580450) baseStart_1580450 baseEnd_1580450 := by
    simpa [prefixWord, tailWord_1580450, baseEnd_1580450] using wordTrace_append hprefix tailTrace_1580450
  have hstable : (prefixWord ++ tailWord_1580450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580450).length < 2 ^ (prefixWord ++ tailWord_1580450).sum := by decide
  have hdescent : baseEnd_1580450 < baseStart_1580450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580463 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 6, 2, 2]
def baseStart_1580463 : Nat := 118140960795 + 1580463 * 2 ^ 59
def prefixEnd_1580463 : Nat := 4983230072969 + 3 ^ 40 * 1580463 * 2
def baseEnd_1580463 : Nat := 811537175646955164944089

theorem tailTrace_1580463 : CollatzResearch.WordTrace tailWord_1580463 prefixEnd_1580463 811537175646955164944089 := by
  unfold tailWord_1580463
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644221273259947435954043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38429480848839964957302695 57644221273259947435954043)
  ·
    refine ⟨86466331909889921153931065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57644221273259947435954043 86466331909889921153931065)
    ·
      refine ⟨64849748932417440865448299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86466331909889921153931065 64849748932417440865448299)
      ·
        refine ⟨97274623398626161298172449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64849748932417440865448299 97274623398626161298172449)
        ·
          refine ⟨72955967548969620973629337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97274623398626161298172449 72955967548969620973629337)
          ·
            refine ⟨54716975661727215730222003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72955967548969620973629337 54716975661727215730222003)
            ·
              refine ⟨82075463492590823595333005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54716975661727215730222003 82075463492590823595333005)
              ·
                refine ⟨30778298809721558848249877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82075463492590823595333005 30778298809721558848249877)
                ·
                  refine ⟨1442732756705698071011713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30778298809721558848249877 1442732756705698071011713)
                  ·
                    refine ⟨1082049567529273553258785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442732756705698071011713 1082049567529273553258785)
                    ·
                      refine ⟨811537175646955164944089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082049567529273553258785 811537175646955164944089)
                      ·
                        rfl

theorem cell23_1580463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 2, 2].length) (baseStart_1580463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580463 prefixEnd_1580463 := by exact prefixLift 1580463
  have htrace : WordTrace (prefixWord ++ tailWord_1580463) baseStart_1580463 baseEnd_1580463 := by
    simpa [prefixWord, tailWord_1580463, baseEnd_1580463] using wordTrace_append hprefix tailTrace_1580463
  have hstable : (prefixWord ++ tailWord_1580463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580463).length < 2 ^ (prefixWord ++ tailWord_1580463).sum := by decide
  have hdescent : baseEnd_1580463 < baseStart_1580463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1580479 : Nat := 118140960795 + 1580479 * 2 ^ 59
def prefixEnd_1580479 : Nat := 4983230072969 + 3 ^ 40 * 1580479 * 2
def baseEnd_1580479 : Nat := 811545391337427102344015

theorem tailTrace_1580479 : CollatzResearch.WordTrace tailWord_1580479 prefixEnd_1580479 811545391337427102344015 := by
  unfold tailWord_1580479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644804841201982168536491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38429869894134654779024327 57644804841201982168536491)
  ·
    refine ⟨86467207261802973252804737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57644804841201982168536491 86467207261802973252804737)
    ·
      refine ⟨64850405446352229939603553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86467207261802973252804737 64850405446352229939603553)
      ·
        refine ⟨48637804084764172454702665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64850405446352229939603553 48637804084764172454702665)
        ·
          refine ⟨36478353063573129341026999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48637804084764172454702665 36478353063573129341026999)
          ·
            refine ⟨54717529595359694011540499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36478353063573129341026999 54717529595359694011540499)
            ·
              refine ⟨82076294393039541017310749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54717529595359694011540499 82076294393039541017310749)
              ·
                refine ⟨30778610397389827881491531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82076294393039541017310749 30778610397389827881491531)
                ·
                  refine ⟨46167915596084741822237297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30778610397389827881491531 46167915596084741822237297)
                  ·
                    refine ⟨34625936697063556366677973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46167915596084741822237297 34625936697063556366677973)
                    ·
                      refine ⟨811545391337427102344015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34625936697063556366677973 811545391337427102344015)
                      ·
                        rfl

theorem cell23_1580479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1580479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580479 prefixEnd_1580479 := by exact prefixLift 1580479
  have htrace : WordTrace (prefixWord ++ tailWord_1580479) baseStart_1580479 baseEnd_1580479 := by
    simpa [prefixWord, tailWord_1580479, baseEnd_1580479] using wordTrace_append hprefix tailTrace_1580479
  have hstable : (prefixWord ++ tailWord_1580479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580479).length < 2 ^ (prefixWord ++ tailWord_1580479).sum := by decide
  have hdescent : baseEnd_1580479 < baseStart_1580479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580480 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2]
def baseStart_1580480 : Nat := 118140960795 + 1580480 * 2 ^ 59
def prefixEnd_1580480 : Nat := 4983230072969 + 3 ^ 40 * 1580480 * 2
def baseEnd_1580480 : Nat := 811545904818081598431511

theorem tailTrace_1580480 : CollatzResearch.WordTrace tailWord_1580480 prefixEnd_1580480 811545904818081598431511 := by
  unfold tailWord_1580480
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822420657099179669661447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38429894209465572892881929 28822420657099179669661447)
  ·
    refine ⟨43233630985648769504492171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28822420657099179669661447 43233630985648769504492171)
    ·
      refine ⟨64850446478473154256738257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43233630985648769504492171 64850446478473154256738257)
      ·
        refine ⟨48637834858854865692553693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64850446478473154256738257 48637834858854865692553693)
        ·
          refine ⟨18239188072070574634707635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48637834858854865692553693 18239188072070574634707635)
          ·
            refine ⟨27358782108105861952061453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18239188072070574634707635 27358782108105861952061453)
            ·
              refine ⟨10259543290539698232023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27358782108105861952061453 10259543290539698232023045)
              ·
                refine ⟨1923664366976193418504321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10259543290539698232023045 1923664366976193418504321)
                ·
                  refine ⟨1442748275232145063878241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923664366976193418504321 1442748275232145063878241)
                  ·
                    refine ⟨1082061206424108797908681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442748275232145063878241 1082061206424108797908681)
                    ·
                      refine ⟨811545904818081598431511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082061206424108797908681 811545904818081598431511)
                      ·
                        rfl

theorem cell23_1580480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_1580480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580480 prefixEnd_1580480 := by exact prefixLift 1580480
  have htrace : WordTrace (prefixWord ++ tailWord_1580480) baseStart_1580480 baseEnd_1580480 := by
    simpa [prefixWord, tailWord_1580480, baseEnd_1580480] using wordTrace_append hprefix tailTrace_1580480
  have hstable : (prefixWord ++ tailWord_1580480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580480).length < 2 ^ (prefixWord ++ tailWord_1580480).sum := by decide
  have hdescent : baseEnd_1580480 < baseStart_1580480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580489 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1580489 : Nat := 118140960795 + 1580489 * 2 ^ 59
def prefixEnd_1580489 : Nat := 4983230072969 + 3 ^ 40 * 1580489 * 2
def baseEnd_1580489 : Nat := 811550526143972063218969

theorem tailTrace_1580489 : CollatzResearch.WordTrace tailWord_1580489 prefixEnd_1580489 811550526143972063218969 := by
  unfold tailWord_1580489
  simp only [CollatzResearch.WordTrace]
  refine ⟨57645169571165753876400521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38430113047443835917600347 57645169571165753876400521)
  ·
    refine ⟨43233877178374315407300391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57645169571165753876400521 43233877178374315407300391)
    ·
      refine ⟨64850815767561473110950587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43233877178374315407300391 64850815767561473110950587)
      ·
        refine ⟨97276223651342209666425881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64850815767561473110950587 97276223651342209666425881)
        ·
          refine ⟨72957167738506657249819411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97276223651342209666425881 72957167738506657249819411)
          ·
            refine ⟨109435751607759985874729117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72957167738506657249819411 109435751607759985874729117)
            ·
              refine ⟨41038406852909994703023419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109435751607759985874729117 41038406852909994703023419)
              ·
                refine ⟨61557610279364992054535129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41038406852909994703023419 61557610279364992054535129)
                ·
                  refine ⟨46168207709523744040901347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61557610279364992054535129 46168207709523744040901347)
                  ·
                    refine ⟨69252311564285616061352021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46168207709523744040901347 69252311564285616061352021)
                    ·
                      refine ⟨811550526143972063218969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69252311564285616061352021 811550526143972063218969)
                      ·
                        rfl

theorem cell23_1580489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1580489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580489 prefixEnd_1580489 := by exact prefixLift 1580489
  have htrace : WordTrace (prefixWord ++ tailWord_1580489) baseStart_1580489 baseEnd_1580489 := by
    simpa [prefixWord, tailWord_1580489, baseEnd_1580489] using wordTrace_append hprefix tailTrace_1580489
  have hstable : (prefixWord ++ tailWord_1580489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580489).length < 2 ^ (prefixWord ++ tailWord_1580489).sum := by decide
  have hdescent : baseEnd_1580489 < baseStart_1580489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580496 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_1580496 : Nat := 118140960795 + 1580496 * 2 ^ 59
def prefixEnd_1580496 : Nat := 4983230072969 + 3 ^ 40 * 1580496 * 2
def baseEnd_1580496 : Nat := 811554120508553535831437

theorem tailTrace_1580496 : CollatzResearch.WordTrace tailWord_1580496 prefixEnd_1580496 811554120508553535831437 := by
  unfold tailWord_1580496
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822712441070197035952671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38430283254760262714603561 28822712441070197035952671)
  ·
    refine ⟨43234068661605295553929007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28822712441070197035952671 43234068661605295553929007)
    ·
      refine ⟨64851102992407943330893511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43234068661605295553929007 64851102992407943330893511)
      ·
        refine ⟨97276654488611914996340267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64851102992407943330893511 97276654488611914996340267)
        ·
          refine ⟨145914981732917872494510401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97276654488611914996340267 145914981732917872494510401)
          ·
            refine ⟨109436236299688404370882801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145914981732917872494510401 109436236299688404370882801)
            ·
              refine ⟨82077177224766303278162101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109436236299688404370882801 82077177224766303278162101)
              ·
                refine ⟨7694735364821840932327697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82077177224766303278162101 7694735364821840932327697)
                ·
                  refine ⟨5771051523616380699245773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694735364821840932327697 5771051523616380699245773)
                  ·
                    refine ⟨2164144321356142762217165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5771051523616380699245773 2164144321356142762217165)
                    ·
                      refine ⟨811554120508553535831437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164144321356142762217165 811554120508553535831437)
                      ·
                        rfl

theorem cell23_1580496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_1580496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580496 prefixEnd_1580496 := by exact prefixLift 1580496
  have htrace : WordTrace (prefixWord ++ tailWord_1580496) baseStart_1580496 baseEnd_1580496 := by
    simpa [prefixWord, tailWord_1580496, baseEnd_1580496] using wordTrace_append hprefix tailTrace_1580496
  have hstable : (prefixWord ++ tailWord_1580496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580496).length < 2 ^ (prefixWord ++ tailWord_1580496).sum := by decide
  have hdescent : baseEnd_1580496 < baseStart_1580496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580553 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 4, 2]
def baseStart_1580553 : Nat := 118140960795 + 1580553 * 2 ^ 59
def prefixEnd_1580553 : Nat := 4983230072969 + 3 ^ 40 * 1580553 * 2
def baseEnd_1580553 : Nat := 811583388905859812818675

theorem tailTrace_1580553 : CollatzResearch.WordTrace tailWord_1580553 prefixEnd_1580553 811583388905859812818675 := by
  unfold tailWord_1580553
  simp only [CollatzResearch.WordTrace]
  refine ⟨57647503842933892806730313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38431669228622595204486875 57647503842933892806730313)
  ·
    refine ⟨43235627882200419605047735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57647503842933892806730313 43235627882200419605047735)
    ·
      refine ⟨64853441823300629407571603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43235627882200419605047735 64853441823300629407571603)
      ·
        refine ⟨97280162734950944111357405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64853441823300629407571603 97280162734950944111357405)
        ·
          refine ⟨36480061025606604041759027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97280162734950944111357405 36480061025606604041759027)
          ·
            refine ⟨54720091538409906062638541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36480061025606604041759027 54720091538409906062638541)
            ·
              refine ⟨20520034326903714773489453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54720091538409906062638541 20520034326903714773489453)
              ·
                refine ⟨7695012872588893040058545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20520034326903714773489453 7695012872588893040058545)
                ·
                  refine ⟨5771259654441669780043909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695012872588893040058545 5771259654441669780043909)
                  ·
                    refine ⟨1082111185207813083758233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771259654441669780043909 1082111185207813083758233)
                    ·
                      refine ⟨811583388905859812818675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082111185207813083758233 811583388905859812818675)
                      ·
                        rfl

theorem cell23_1580553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 4, 2].length) (baseStart_1580553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580553 prefixEnd_1580553 := by exact prefixLift 1580553
  have htrace : WordTrace (prefixWord ++ tailWord_1580553) baseStart_1580553 baseEnd_1580553 := by
    simpa [prefixWord, tailWord_1580553, baseEnd_1580553] using wordTrace_append hprefix tailTrace_1580553
  have hstable : (prefixWord ++ tailWord_1580553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580553).length < 2 ^ (prefixWord ++ tailWord_1580553).sum := by decide
  have hdescent : baseEnd_1580553 < baseStart_1580553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580563 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 3, 4]
def baseStart_1580563 : Nat := 118140960795 + 1580563 * 2 ^ 59
def prefixEnd_1580563 : Nat := 4983230072969 + 3 ^ 40 * 1580563 * 2
def baseEnd_1580563 : Nat := 270529507904134924564543

theorem tailTrace_1580563 : CollatzResearch.WordTrace tailWord_1580563 prefixEnd_1580563 270529507904134924564543 := by
  unfold tailWord_1580563
  simp only [CollatzResearch.WordTrace]
  refine ⟨57647868572897664514594343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38431912381931776343062895 57647868572897664514594343)
  ·
    refine ⟨86471802859346496771891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57647868572897664514594343 86471802859346496771891515)
    ·
      refine ⟨129707704289019745157837273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86471802859346496771891515 129707704289019745157837273)
      ·
        refine ⟨97280778216764808868377955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129707704289019745157837273 97280778216764808868377955)
        ·
          refine ⟨145921167325147213302566933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97280778216764808868377955 145921167325147213302566933)
          ·
            refine ⟨6840054718366275623557825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145921167325147213302566933 6840054718366275623557825)
            ·
              refine ⟨5130041038774706717668369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840054718366275623557825 5130041038774706717668369)
              ·
                refine ⟨3847530779081030038251277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130041038774706717668369 3847530779081030038251277)
                ·
                  refine ⟨1442824042155386264344229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3847530779081030038251277 1442824042155386264344229)
                  ·
                    refine ⟨270529507904134924564543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442824042155386264344229 270529507904134924564543)
                    ·
                      rfl

theorem cell23_1580563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 4].length) (baseStart_1580563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580563 prefixEnd_1580563 := by exact prefixLift 1580563
  have htrace : WordTrace (prefixWord ++ tailWord_1580563) baseStart_1580563 baseEnd_1580563 := by
    simpa [prefixWord, tailWord_1580563, baseEnd_1580563] using wordTrace_append hprefix tailTrace_1580563
  have hstable : (prefixWord ++ tailWord_1580563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580563).length < 2 ^ (prefixWord ++ tailWord_1580563).sum := by decide
  have hdescent : baseEnd_1580563 < baseStart_1580563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580573 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1580573 : Nat := 118140960795 + 1580573 * 2 ^ 59
def prefixEnd_1580573 : Nat := 4983230072969 + 3 ^ 40 * 1580573 * 2
def baseEnd_1580573 : Nat := 811593658518949734568583

theorem tailTrace_1580573 : CollatzResearch.WordTrace tailWord_1580573 prefixEnd_1580573 811593658518949734568583 := by
  unfold tailWord_1580573
  simp only [CollatzResearch.WordTrace]
  refine ⟨57648233302861436222458373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38432155535240957481638915 57648233302861436222458373)
  ·
    refine ⟨10809043744286519291710945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57648233302861436222458373 10809043744286519291710945)
    ·
      refine ⟨8106782808214889468783209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10809043744286519291710945 8106782808214889468783209)
      ·
        refine ⟨6080087106161167101587407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8106782808214889468783209 6080087106161167101587407)
        ·
          refine ⟨9120130659241750652381111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080087106161167101587407 9120130659241750652381111)
          ·
            refine ⟨13680195988862625978571667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120130659241750652381111 13680195988862625978571667)
            ·
              refine ⟨20520293983293938967857501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13680195988862625978571667 20520293983293938967857501)
              ·
                refine ⟨7695110243735227112946563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20520293983293938967857501 7695110243735227112946563)
                ·
                  refine ⟨11542665365602840669419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7695110243735227112946563 11542665365602840669419845)
                  ·
                    refine ⟨2164249756050532625516221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11542665365602840669419845 2164249756050532625516221)
                    ·
                      refine ⟨811593658518949734568583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164249756050532625516221 811593658518949734568583)
                      ·
                        rfl

theorem cell23_1580573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1580573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580573 prefixEnd_1580573 := by exact prefixLift 1580573
  have htrace : WordTrace (prefixWord ++ tailWord_1580573) baseStart_1580573 baseEnd_1580573 := by
    simpa [prefixWord, tailWord_1580573, baseEnd_1580573] using wordTrace_append hprefix tailTrace_1580573
  have hstable : (prefixWord ++ tailWord_1580573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580573).length < 2 ^ (prefixWord ++ tailWord_1580573).sum := by decide
  have hdescent : baseEnd_1580573 < baseStart_1580573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580590 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1580590 : Nat := 118140960795 + 1580590 * 2 ^ 59
def prefixEnd_1580590 : Nat := 4983230072969 + 3 ^ 40 * 1580590 * 2
def baseEnd_1580590 : Nat := 811602387690076168056005

theorem tailTrace_1580590 : CollatzResearch.WordTrace tailWord_1580590 prefixEnd_1580590 811602387690076168056005 := by
  unfold tailWord_1580590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206106667974981015728403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38432568895866565417218149 7206106667974981015728403)
  ·
    refine ⟨10809160001962471523592605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206106667974981015728403 10809160001962471523592605)
    ·
      refine ⟨4053435000735926821347227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10809160001962471523592605 4053435000735926821347227)
      ·
        refine ⟨6080152501103890232020841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053435000735926821347227 6080152501103890232020841)
        ·
          refine ⟨4560114375827917674015631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080152501103890232020841 4560114375827917674015631)
          ·
            refine ⟨6840171563741876511023447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560114375827917674015631 6840171563741876511023447)
            ·
              refine ⟨10260257345612814766535171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840171563741876511023447 10260257345612814766535171)
              ·
                refine ⟨15390386018419222149802757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260257345612814766535171 15390386018419222149802757)
                ·
                  refine ⟨2885697378453604153088017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15390386018419222149802757 2885697378453604153088017)
                  ·
                    refine ⟨2164273033840203114816013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885697378453604153088017 2164273033840203114816013)
                    ·
                      refine ⟨811602387690076168056005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164273033840203114816013 811602387690076168056005)
                      ·
                        rfl

theorem cell23_1580590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1580590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580590 prefixEnd_1580590 := by exact prefixLift 1580590
  have htrace : WordTrace (prefixWord ++ tailWord_1580590) baseStart_1580590 baseEnd_1580590 := by
    simpa [prefixWord, tailWord_1580590, baseEnd_1580590] using wordTrace_append hprefix tailTrace_1580590
  have hstable : (prefixWord ++ tailWord_1580590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580590).length < 2 ^ (prefixWord ++ tailWord_1580590).sum := by decide
  have hdescent : baseEnd_1580590 < baseStart_1580590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580666 : List Nat := [3, 1, 1, 1, 1, 1, 1, 14]
def baseStart_1580666 : Nat := 118140960795 + 1580666 * 2 ^ 59
def prefixEnd_1580666 : Nat := 4983230072969 + 3 ^ 40 * 1580666 * 2
def baseEnd_1580666 : Nat := 30060793045178439655765

theorem tailTrace_1580666 : CollatzResearch.WordTrace tailWord_1580666 prefixEnd_1580666 30060793045178439655765 := by
  unfold tailWord_1580666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412906322881128276398463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38434416861016342070395901 14412906322881128276398463)
  ·
    refine ⟨21619359484321692414597695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14412906322881128276398463 21619359484321692414597695)
    ·
      refine ⟨32429039226482538621896543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21619359484321692414597695 32429039226482538621896543)
      ·
        refine ⟨48643558839723807932844815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32429039226482538621896543 48643558839723807932844815)
        ·
          refine ⟨72965338259585711899267223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48643558839723807932844815 72965338259585711899267223)
          ·
            refine ⟨109448007389378567848900835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72965338259585711899267223 109448007389378567848900835)
            ·
              refine ⟨164172011084067851773351253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109448007389378567848900835 164172011084067851773351253)
              ·
                refine ⟨30060793045178439655765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 164172011084067851773351253 30060793045178439655765)
                ·
                  rfl

theorem cell23_1580666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_1580666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580666 prefixEnd_1580666 := by exact prefixLift 1580666
  have htrace : WordTrace (prefixWord ++ tailWord_1580666) baseStart_1580666 baseEnd_1580666 := by
    simpa [prefixWord, tailWord_1580666, baseEnd_1580666] using wordTrace_append hprefix tailTrace_1580666
  have hstable : (prefixWord ++ tailWord_1580666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580666).length < 2 ^ (prefixWord ++ tailWord_1580666).sum := by decide
  have hdescent : baseEnd_1580666 < baseStart_1580666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580677 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_1580677 : Nat := 118140960795 + 1580677 * 2 ^ 59
def prefixEnd_1580677 : Nat := 4983230072969 + 3 ^ 40 * 1580677 * 2
def baseEnd_1580677 : Nat := 811647060507017327668105

theorem tailTrace_1580677 : CollatzResearch.WordTrace tailWord_1580677 prefixEnd_1580677 811647060507017327668105 := by
  unfold tailWord_1580677
  simp only [CollatzResearch.WordTrace]
  refine ⟨57652026494484661984244285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38434684329656441322829523 57652026494484661984244285)
  ·
    refine ⟨21619509935431748244091607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57652026494484661984244285 21619509935431748244091607)
    ·
      refine ⟨32429264903147622366137411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21619509935431748244091607 32429264903147622366137411)
      ·
        refine ⟨48643897354721433549206117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32429264903147622366137411 48643897354721433549206117)
        ·
          refine ⟨9120730754010268790476147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48643897354721433549206117 9120730754010268790476147)
          ·
            refine ⟨13681096131015403185714221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120730754010268790476147 13681096131015403185714221)
            ·
              refine ⟨5130411049130776194642833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13681096131015403185714221 5130411049130776194642833)
              ·
                refine ⟨3847808286848082145982125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130411049130776194642833 3847808286848082145982125)
                ·
                  refine ⟨1442928107568030804743297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3847808286848082145982125 1442928107568030804743297)
                  ·
                    refine ⟨1082196080676023103557473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442928107568030804743297 1082196080676023103557473)
                    ·
                      refine ⟨811647060507017327668105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082196080676023103557473 811647060507017327668105)
                      ·
                        rfl

theorem cell23_1580677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_1580677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580677 prefixEnd_1580677 := by exact prefixLift 1580677
  have htrace : WordTrace (prefixWord ++ tailWord_1580677) baseStart_1580677 baseEnd_1580677 := by
    simpa [prefixWord, tailWord_1580677, baseEnd_1580677] using wordTrace_append hprefix tailTrace_1580677
  have hstable : (prefixWord ++ tailWord_1580677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580677).length < 2 ^ (prefixWord ++ tailWord_1580677).sum := by decide
  have hdescent : baseEnd_1580677 < baseStart_1580677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580683 : List Nat := [1, 1, 1, 1, 4, 1, 7, 7]
def baseStart_1580683 : Nat := 118140960795 + 1580683 * 2 ^ 59
def prefixEnd_1580683 : Nat := 4983230072969 + 3 ^ 40 * 1580683 * 2
def baseEnd_1580683 : Nat := 30061116347812752007151

theorem tailTrace_1580683 : CollatzResearch.WordTrace tailWord_1580683 prefixEnd_1580683 30061116347812752007151 := by
  unfold tailWord_1580683
  simp only [CollatzResearch.WordTrace]
  refine ⟨57652245332462925008962703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38434830221641950005975135 57652245332462925008962703)
  ·
    refine ⟨86478367998694387513444055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57652245332462925008962703 86478367998694387513444055)
    ·
      refine ⟨129717551998041581270166083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86478367998694387513444055 129717551998041581270166083)
      ·
        refine ⟨194576327997062371905249125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129717551998041581270166083 194576327997062371905249125)
        ·
          refine ⟨36483061499449194732234211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194576327997062371905249125 36483061499449194732234211)
          ·
            refine ⟨54724592249173792098351317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36483061499449194732234211 54724592249173792098351317)
            ·
              refine ⟨1282607630840010752305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54724592249173792098351317 1282607630840010752305109)
              ·
                refine ⟨30061116347812752007151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1282607630840010752305109 30061116347812752007151)
                ·
                  rfl

theorem cell23_1580683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 7].length) (baseStart_1580683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580683 prefixEnd_1580683 := by exact prefixLift 1580683
  have htrace : WordTrace (prefixWord ++ tailWord_1580683) baseStart_1580683 baseEnd_1580683 := by
    simpa [prefixWord, tailWord_1580683, baseEnd_1580683] using wordTrace_append hprefix tailTrace_1580683
  have hstable : (prefixWord ++ tailWord_1580683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580683).length < 2 ^ (prefixWord ++ tailWord_1580683).sum := by decide
  have hdescent : baseEnd_1580683 < baseStart_1580683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580720 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2]
def baseStart_1580720 : Nat := 118140960795 + 1580720 * 2 ^ 59
def prefixEnd_1580720 : Nat := 4983230072969 + 3 ^ 40 * 1580720 * 2
def baseEnd_1580720 : Nat := 811669140175160659430407

theorem tailTrace_1580720 : CollatzResearch.WordTrace tailWord_1580720 prefixEnd_1580720 811669140175160659430407 := by
  unfold tailWord_1580720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28826797416664440164029807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38435729888885920218706409 28826797416664440164029807)
  ·
    refine ⟨43240196124996660246044711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28826797416664440164029807 43240196124996660246044711)
    ·
      refine ⟨64860294187494990369067067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43240196124996660246044711 64860294187494990369067067)
      ·
        refine ⟨97290441281242485553600601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64860294187494990369067067 97290441281242485553600601)
        ·
          refine ⟨72967830960931864165200451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97290441281242485553600601 72967830960931864165200451)
          ·
            refine ⟨109451746441397796247800677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72967830960931864165200451 109451746441397796247800677)
            ·
              refine ⟨20522202457762086796462627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109451746441397796247800677 20522202457762086796462627)
              ·
                refine ⟨30783303686643130194693941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20522202457762086796462627 30783303686643130194693941)
                ·
                  refine ⟨2885934720622793455752557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30783303686643130194693941 2885934720622793455752557)
                  ·
                    refine ⟨1082225520233547545907209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885934720622793455752557 1082225520233547545907209)
                    ·
                      refine ⟨811669140175160659430407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082225520233547545907209 811669140175160659430407)
                      ·
                        rfl

theorem cell23_1580720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2].length) (baseStart_1580720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580720 prefixEnd_1580720 := by exact prefixLift 1580720
  have htrace : WordTrace (prefixWord ++ tailWord_1580720) baseStart_1580720 baseEnd_1580720 := by
    simpa [prefixWord, tailWord_1580720, baseEnd_1580720] using wordTrace_append hprefix tailTrace_1580720
  have hstable : (prefixWord ++ tailWord_1580720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580720).length < 2 ^ (prefixWord ++ tailWord_1580720).sum := by decide
  have hdescent : baseEnd_1580720 < baseStart_1580720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580727 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_1580727 : Nat := 118140960795 + 1580727 * 2 ^ 59
def prefixEnd_1580727 : Nat := 4983230072969 + 3 ^ 40 * 1580727 * 2
def baseEnd_1580727 : Nat := 811672734539742132042875

theorem tailTrace_1580727 : CollatzResearch.WordTrace tailWord_1580727 prefixEnd_1580727 811672734539742132042875 := by
  unfold tailWord_1580727
  simp only [CollatzResearch.WordTrace]
  refine ⟨57653850144303520523564435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38435900096202347015709623 57653850144303520523564435)
  ·
    refine ⟨86480775216455280785346653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57653850144303520523564435 86480775216455280785346653)
    ·
      refine ⟨32430290706170730294504995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86480775216455280785346653 32430290706170730294504995)
      ·
        refine ⟨48645436059256095441757493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32430290706170730294504995 48645436059256095441757493)
        ·
          refine ⟨4560509630555258947664765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48645436059256095441757493 4560509630555258947664765)
          ·
            refine ⟨1710191111458222105374287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4560509630555258947664765 1710191111458222105374287)
            ·
              refine ⟨2565286667187333158061431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710191111458222105374287 2565286667187333158061431)
              ·
                refine ⟨3847930000780999737092147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565286667187333158061431 3847930000780999737092147)
                ·
                  refine ⟨5771895001171499605638221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847930000780999737092147 5771895001171499605638221)
                  ·
                    refine ⟨2164460625439312352114333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5771895001171499605638221 2164460625439312352114333)
                    ·
                      refine ⟨811672734539742132042875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2164460625439312352114333 811672734539742132042875)
                      ·
                        rfl

theorem cell23_1580727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_1580727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580727 prefixEnd_1580727 := by exact prefixLift 1580727
  have htrace : WordTrace (prefixWord ++ tailWord_1580727) baseStart_1580727 baseEnd_1580727 := by
    simpa [prefixWord, tailWord_1580727, baseEnd_1580727] using wordTrace_append hprefix tailTrace_1580727
  have hstable : (prefixWord ++ tailWord_1580727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580727).length < 2 ^ (prefixWord ++ tailWord_1580727).sum := by decide
  have hdescent : baseEnd_1580727 < baseStart_1580727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580753 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1580753 : Nat := 118140960795 + 1580753 * 2 ^ 59
def prefixEnd_1580753 : Nat := 4983230072969 + 3 ^ 40 * 1580753 * 2
def baseEnd_1580753 : Nat := 811686085036759030317755

theorem tailTrace_1580753 : CollatzResearch.WordTrace tailWord_1580753 prefixEnd_1580753 811686085036759030317755 := by
  unfold tailWord_1580753
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654798442209326964010913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38436532294806217976007275 57654798442209326964010913)
  ·
    refine ⟨43241098831656995223008185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57654798442209326964010913 43241098831656995223008185)
    ·
      refine ⟨32430824123742746417256139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43241098831656995223008185 32430824123742746417256139)
      ·
        refine ⟨48646236185614119625884209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32430824123742746417256139 48646236185614119625884209)
        ·
          refine ⟨36484677139210589719413157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48646236185614119625884209 36484677139210589719413157)
          ·
            refine ⟨6840876963601985572389967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36484677139210589719413157 6840876963601985572389967)
            ·
              refine ⟨10261315445402978358584951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840876963601985572389967 10261315445402978358584951)
              ·
                refine ⟨15391973168104467537877427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261315445402978358584951 15391973168104467537877427)
                ·
                  refine ⟨23087959752156701306816141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15391973168104467537877427 23087959752156701306816141)
                  ·
                    refine ⟨8657984907058762990056053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23087959752156701306816141 8657984907058762990056053)
                    ·
                      refine ⟨811686085036759030317755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8657984907058762990056053 811686085036759030317755)
                      ·
                        rfl

theorem cell23_1580753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1580753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580753 prefixEnd_1580753 := by exact prefixLift 1580753
  have htrace : WordTrace (prefixWord ++ tailWord_1580753) baseStart_1580753 baseEnd_1580753 := by
    simpa [prefixWord, tailWord_1580753, baseEnd_1580753] using wordTrace_append hprefix tailTrace_1580753
  have hstable : (prefixWord ++ tailWord_1580753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580753).length < 2 ^ (prefixWord ++ tailWord_1580753).sum := by decide
  have hdescent : baseEnd_1580753 < baseStart_1580753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580754 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1580754 : Nat := 118140960795 + 1580754 * 2 ^ 59
def prefixEnd_1580754 : Nat := 4983230072969 + 3 ^ 40 * 1580754 * 2
def baseEnd_1580754 : Nat := 811686598517413526405251

theorem tailTrace_1580754 : CollatzResearch.WordTrace tailWord_1580754 prefixEnd_1580754 811686598517413526405251 := by
  unfold tailWord_1580754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413708728801426033699329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38436556610137136089864877 14413708728801426033699329)
  ·
    refine ⟨10810281546601069525274497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14413708728801426033699329 10810281546601069525274497)
    ·
      refine ⟨8107711159950802143955873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10810281546601069525274497 8107711159950802143955873)
      ·
        refine ⟨6080783369963101607966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8107711159950802143955873 6080783369963101607966905)
        ·
          refine ⟨4560587527472326205975179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080783369963101607966905 4560587527472326205975179)
          ·
            refine ⟨6840881291208489308962769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560587527472326205975179 6840881291208489308962769)
            ·
              refine ⟨5130660968406366981722077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840881291208489308962769 5130660968406366981722077)
              ·
                refine ⟨1923997863152387618145779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5130660968406366981722077 1923997863152387618145779)
                ·
                  refine ⟨2885996794728581427218669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923997863152387618145779 2885996794728581427218669)
                  ·
                    refine ⟨1082248798023218035207001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2885996794728581427218669 1082248798023218035207001)
                    ·
                      refine ⟨811686598517413526405251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082248798023218035207001 811686598517413526405251)
                      ·
                        rfl

theorem cell23_1580754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1580754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580754 prefixEnd_1580754 := by exact prefixLift 1580754
  have htrace : WordTrace (prefixWord ++ tailWord_1580754) baseStart_1580754 baseEnd_1580754 := by
    simpa [prefixWord, tailWord_1580754, baseEnd_1580754] using wordTrace_append hprefix tailTrace_1580754
  have hstable : (prefixWord ++ tailWord_1580754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580754).length < 2 ^ (prefixWord ++ tailWord_1580754).sum := by decide
  have hdescent : baseEnd_1580754 < baseStart_1580754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580767 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 4, 2, 2]
def baseStart_1580767 : Nat := 118140960795 + 1580767 * 2 ^ 59
def prefixEnd_1580767 : Nat := 4983230072969 + 3 ^ 40 * 1580767 * 2
def baseEnd_1580767 : Nat := 811693273765921975542691

theorem tailTrace_1580767 : CollatzResearch.WordTrace tailWord_1580767 prefixEnd_1580767 811693273765921975542691 := by
  unfold tailWord_1580767
  simp only [CollatzResearch.WordTrace]
  refine ⟨57655309064158607355020555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38436872709439071570013703 57655309064158607355020555)
  ·
    refine ⟨86482963596237911032530833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57655309064158607355020555 86482963596237911032530833)
    ·
      refine ⟨64862222697178433274398125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86482963596237911032530833 64862222697178433274398125)
      ·
        refine ⟨24323333511441912477899297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64862222697178433274398125 24323333511441912477899297)
        ·
          refine ⟨18242500133581434358424473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24323333511441912477899297 18242500133581434358424473)
          ·
            refine ⟨13681875100186075768818355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18242500133581434358424473 13681875100186075768818355)
            ·
              refine ⟨20522812650279113653227533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13681875100186075768818355 20522812650279113653227533)
              ·
                refine ⟨7696054743854667619960325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20522812650279113653227533 7696054743854667619960325)
                ·
                  refine ⟨1443010264472750178742561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7696054743854667619960325 1443010264472750178742561)
                  ·
                    refine ⟨1082257698354562634056921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1443010264472750178742561 1082257698354562634056921)
                    ·
                      refine ⟨811693273765921975542691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082257698354562634056921 811693273765921975542691)
                      ·
                        rfl

theorem cell23_1580767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_1580767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580767 prefixEnd_1580767 := by exact prefixLift 1580767
  have htrace : WordTrace (prefixWord ++ tailWord_1580767) baseStart_1580767 baseEnd_1580767 := by
    simpa [prefixWord, tailWord_1580767, baseEnd_1580767] using wordTrace_append hprefix tailTrace_1580767
  have hstable : (prefixWord ++ tailWord_1580767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580767).length < 2 ^ (prefixWord ++ tailWord_1580767).sum := by decide
  have hdescent : baseEnd_1580767 < baseStart_1580767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580788 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1580788 : Nat := 118140960795 + 1580788 * 2 ^ 59
def prefixEnd_1580788 : Nat := 4983230072969 + 3 ^ 40 * 1580788 * 2
def baseEnd_1580788 : Nat := 811704056859666393380095

theorem tailTrace_1580788 : CollatzResearch.WordTrace tailWord_1580788 prefixEnd_1580788 811704056859666393380095 := by
  unfold tailWord_1580788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828037498541263970767509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38437383331388351961023345 28828037498541263970767509)
  ·
    refine ⟨1351314257744121748629727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28828037498541263970767509 1351314257744121748629727)
    ·
      refine ⟨2026971386616182622944591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351314257744121748629727 2026971386616182622944591)
      ·
        refine ⟨3040457079924273934416887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026971386616182622944591 3040457079924273934416887)
        ·
          refine ⟨4560685619886410901625331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040457079924273934416887 4560685619886410901625331)
          ·
            refine ⟨6841028429829616352437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560685619886410901625331 6841028429829616352437997)
            ·
              refine ⟨2565385661186106132164249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841028429829616352437997 2565385661186106132164249)
              ·
                refine ⟨1924039245889579599123187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565385661186106132164249 1924039245889579599123187)
                ·
                  refine ⟨2886058868834369398684781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924039245889579599123187 2886058868834369398684781)
                  ·
                    refine ⟨1082272075812888524506793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886058868834369398684781 1082272075812888524506793)
                    ·
                      refine ⟨811704056859666393380095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082272075812888524506793 811704056859666393380095)
                      ·
                        rfl

theorem cell23_1580788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1580788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580788 prefixEnd_1580788 := by exact prefixLift 1580788
  have htrace : WordTrace (prefixWord ++ tailWord_1580788) baseStart_1580788 baseEnd_1580788 := by
    simpa [prefixWord, tailWord_1580788, baseEnd_1580788] using wordTrace_append hprefix tailTrace_1580788
  have hstable : (prefixWord ++ tailWord_1580788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580788).length < 2 ^ (prefixWord ++ tailWord_1580788).sum := by decide
  have hdescent : baseEnd_1580788 < baseStart_1580788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580803 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 7]
def baseStart_1580803 : Nat := 118140960795 + 1580803 * 2 ^ 59
def prefixEnd_1580803 : Nat := 4983230072969 + 3 ^ 40 * 1580803 * 2
def baseEnd_1580803 : Nat := 270570586356494611564175

theorem tailTrace_1580803 : CollatzResearch.WordTrace tailWord_1580803 prefixEnd_1580803 270570586356494611564175 := by
  unfold tailWord_1580803
  simp only [CollatzResearch.WordTrace]
  refine ⟨57656622092028185503331063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38437748061352123668887375 57656622092028185503331063)
  ·
    refine ⟨86484933138042278254996595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57656622092028185503331063 86484933138042278254996595)
    ·
      refine ⟨129727399707063417382494893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86484933138042278254996595 129727399707063417382494893)
      ·
        refine ⟨48647774890148781518435585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129727399707063417382494893 48647774890148781518435585)
        ·
          refine ⟨36485831167611586138826689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48647774890148781518435585 36485831167611586138826689)
          ·
            refine ⟨27364373375708689604120017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36485831167611586138826689 27364373375708689604120017)
            ·
              refine ⟨20523280031781517203090013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27364373375708689604120017 20523280031781517203090013)
              ·
                refine ⟨7696230011918068951158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20523280031781517203090013 7696230011918068951158755)
                ·
                  refine ⟨11544345017877103426738133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7696230011918068951158755 11544345017877103426738133)
                  ·
                    refine ⟨270570586356494611564175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11544345017877103426738133 270570586356494611564175)
                    ·
                      rfl

theorem cell23_1580803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_1580803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580803 prefixEnd_1580803 := by exact prefixLift 1580803
  have htrace : WordTrace (prefixWord ++ tailWord_1580803) baseStart_1580803 baseEnd_1580803 := by
    simpa [prefixWord, tailWord_1580803, baseEnd_1580803] using wordTrace_append hprefix tailTrace_1580803
  have hstable : (prefixWord ++ tailWord_1580803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580803).length < 2 ^ (prefixWord ++ tailWord_1580803).sum := by decide
  have hdescent : baseEnd_1580803 < baseStart_1580803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580818 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1580818 : Nat := 118140960795 + 1580818 * 2 ^ 59
def prefixEnd_1580818 : Nat := 4983230072969 + 3 ^ 40 * 1580818 * 2
def baseEnd_1580818 : Nat := 811719461279301276004957

theorem tailTrace_1580818 : CollatzResearch.WordTrace tailWord_1580818 prefixEnd_1580818 811719461279301276004957 := by
  unfold tailWord_1580818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414292296743460766281777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38438112791315895376751405 14414292296743460766281777)
  ·
    refine ⟨10810719222557595574711333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14414292296743460766281777 10810719222557595574711333)
    ·
      refine ⟨2027009854229549170258375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10810719222557595574711333 2027009854229549170258375)
      ·
        refine ⟨3040514781344323755387563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027009854229549170258375 3040514781344323755387563)
        ·
          refine ⟨4560772172016485633081345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040514781344323755387563 4560772172016485633081345)
          ·
            refine ⟨3420579129012364224811009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560772172016485633081345 3420579129012364224811009)
            ·
              refine ⟨2565434346759273168608257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420579129012364224811009 2565434346759273168608257)
              ·
                refine ⟨1924075760069454876456193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565434346759273168608257 1924075760069454876456193)
                ·
                  refine ⟨1443056820052091157342145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924075760069454876456193 1443056820052091157342145)
                  ·
                    refine ⟨1082292615039068368006609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1443056820052091157342145 1082292615039068368006609)
                    ·
                      refine ⟨811719461279301276004957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082292615039068368006609 811719461279301276004957)
                      ·
                        rfl

theorem cell23_1580818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1580818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580818 prefixEnd_1580818 := by exact prefixLift 1580818
  have htrace : WordTrace (prefixWord ++ tailWord_1580818) baseStart_1580818 baseEnd_1580818 := by
    simpa [prefixWord, tailWord_1580818, baseEnd_1580818] using wordTrace_append hprefix tailTrace_1580818
  have hstable : (prefixWord ++ tailWord_1580818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580818).length < 2 ^ (prefixWord ++ tailWord_1580818).sum := by decide
  have hdescent : baseEnd_1580818 < baseStart_1580818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580843 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_1580843 : Nat := 118140960795 + 1580843 * 2 ^ 59
def prefixEnd_1580843 : Nat := 4983230072969 + 3 ^ 40 * 1580843 * 2
def baseEnd_1580843 : Nat := 811732298295663678192341

theorem tailTrace_1580843 : CollatzResearch.WordTrace tailWord_1580843 prefixEnd_1580843 811732298295663678192341 := by
  unfold tailWord_1580843
  simp only [CollatzResearch.WordTrace]
  refine ⟨57658081011883272334787183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38438720674588848223191455 57658081011883272334787183)
  ·
    refine ⟨86487121517824908502180775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57658081011883272334787183 86487121517824908502180775)
    ·
      refine ⟨129730682276737362753271163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86487121517824908502180775 129730682276737362753271163)
      ·
        refine ⟨194596023415106044129906745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129730682276737362753271163 194596023415106044129906745)
        ·
          refine ⟨145947017561329533097430059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194596023415106044129906745 145947017561329533097430059)
          ·
            refine ⟨218920526341994299646145089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145947017561329533097430059 218920526341994299646145089)
            ·
              refine ⟨164190394756495724734608817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218920526341994299646145089 164190394756495724734608817)
              ·
                refine ⟨123142796067371793550956613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164190394756495724734608817 123142796067371793550956613)
                ·
                  refine ⟨23089274262632211290804365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123142796067371793550956613 23089274262632211290804365)
                  ·
                    refine ⟨8658477848487079234051637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23089274262632211290804365 8658477848487079234051637)
                    ·
                      refine ⟨811732298295663678192341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8658477848487079234051637 811732298295663678192341)
                      ·
                        rfl

theorem cell23_1580843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_1580843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580843 prefixEnd_1580843 := by exact prefixLift 1580843
  have htrace : WordTrace (prefixWord ++ tailWord_1580843) baseStart_1580843 baseEnd_1580843 := by
    simpa [prefixWord, tailWord_1580843, baseEnd_1580843] using wordTrace_append hprefix tailTrace_1580843
  have hstable : (prefixWord ++ tailWord_1580843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580843).length < 2 ^ (prefixWord ++ tailWord_1580843).sum := by decide
  have hdescent : baseEnd_1580843 < baseStart_1580843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580854 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1580854 : Nat := 118140960795 + 1580854 * 2 ^ 59
def prefixEnd_1580854 : Nat := 4983230072969 + 3 ^ 40 * 1580854 * 2
def baseEnd_1580854 : Nat := 270579315527621045051597

theorem tailTrace_1580854 : CollatzResearch.WordTrace tailWord_1580854 prefixEnd_1580854 270579315527621045051597 := by
  unfold tailWord_1580854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603655138427713825839851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38438988143228947475625077 3603655138427713825839851)
  ·
    refine ⟨5405482707641570738759777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603655138427713825839851 5405482707641570738759777)
    ·
      refine ⟨4054112030731178054069833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5405482707641570738759777 4054112030731178054069833)
      ·
        refine ⟨3040584023048383540552375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4054112030731178054069833 3040584023048383540552375)
        ·
          refine ⟨4560876034572575310828563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040584023048383540552375 4560876034572575310828563)
          ·
            refine ⟨6841314051858862966242845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560876034572575310828563 6841314051858862966242845)
            ·
              refine ⟨2565492769447073612341067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841314051858862966242845 2565492769447073612341067)
              ·
                refine ⟨3848239154170610418511601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565492769447073612341067 3848239154170610418511601)
                ·
                  refine ⟨2886179365627957813883701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848239154170610418511601 2886179365627957813883701)
                  ·
                    refine ⟨270579315527621045051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2886179365627957813883701 270579315527621045051597)
                    ·
                      rfl

theorem cell23_1580854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1580854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580854 prefixEnd_1580854 := by exact prefixLift 1580854
  have htrace : WordTrace (prefixWord ++ tailWord_1580854) baseStart_1580854 baseEnd_1580854 := by
    simpa [prefixWord, tailWord_1580854, baseEnd_1580854] using wordTrace_append hprefix tailTrace_1580854
  have hstable : (prefixWord ++ tailWord_1580854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580854).length < 2 ^ (prefixWord ++ tailWord_1580854).sum := by decide
  have hdescent : baseEnd_1580854 < baseStart_1580854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580884 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1580884 : Nat := 118140960795 + 1580884 * 2 ^ 59
def prefixEnd_1580884 : Nat := 4983230072969 + 3 ^ 40 * 1580884 * 2
def baseEnd_1580884 : Nat := 270584450334166005926551

theorem tailTrace_1580884 : CollatzResearch.WordTrace tailWord_1580884 prefixEnd_1580884 270584450334166005926551 := by
  unfold tailWord_1580884
  simp only [CollatzResearch.WordTrace]
  refine ⟨28829788202367368168514853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38439717603156490891353137 28829788202367368168514853)
  ·
    refine ⟨5405585287943881531596535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28829788202367368168514853 5405585287943881531596535)
    ·
      refine ⟨8108377931915822297394803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405585287943881531596535 8108377931915822297394803)
      ·
        refine ⟨12162566897873733446092205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108377931915822297394803 12162566897873733446092205)
        ·
          refine ⟨4560962586702650042284577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12162566897873733446092205 4560962586702650042284577)
          ·
            refine ⟨3420721940026987531713433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560962586702650042284577 3420721940026987531713433)
            ·
              refine ⟨2565541455020240648785075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420721940026987531713433 2565541455020240648785075)
              ·
                refine ⟨3848312182530360973177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565541455020240648785075 3848312182530360973177613)
                ·
                  refine ⟨1443117068448885364941605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3848312182530360973177613 1443117068448885364941605)
                  ·
                    refine ⟨270584450334166005926551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443117068448885364941605 270584450334166005926551)
                    ·
                      rfl

theorem cell23_1580884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1580884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580884 prefixEnd_1580884 := by exact prefixLift 1580884
  have htrace : WordTrace (prefixWord ++ tailWord_1580884) baseStart_1580884 baseEnd_1580884 := by
    simpa [prefixWord, tailWord_1580884, baseEnd_1580884] using wordTrace_append hprefix tailTrace_1580884
  have hstable : (prefixWord ++ tailWord_1580884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580884).length < 2 ^ (prefixWord ++ tailWord_1580884).sum := by decide
  have hdescent : baseEnd_1580884 < baseStart_1580884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580897 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 6]
def baseStart_1580897 : Nat := 118140960795 + 1580897 * 2 ^ 59
def prefixEnd_1580897 : Nat := 4983230072969 + 3 ^ 40 * 1580897 * 2
def baseEnd_1580897 : Nat := 90195558472334051879677

theorem tailTrace_1580897 : CollatzResearch.WordTrace tailWord_1580897 prefixEnd_1580897 90195558472334051879677 := by
  unfold tailWord_1580897
  simp only [CollatzResearch.WordTrace]
  refine ⟨57660050553687639557252945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38440033702458426371501963 57660050553687639557252945)
  ·
    refine ⟨43245037915265729667939709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57660050553687639557252945 43245037915265729667939709)
    ·
      refine ⟨16216889218224648625477391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43245037915265729667939709 16216889218224648625477391)
      ·
        refine ⟨24325333827336972938216087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16216889218224648625477391 24325333827336972938216087)
        ·
          refine ⟨36488000741005459407324131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24325333827336972938216087 36488000741005459407324131)
          ·
            refine ⟨54732001111508189110986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36488000741005459407324131 54732001111508189110986197)
            ·
              refine ⟨1282781276050973182288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54732001111508189110986197 1282781276050973182288739)
              ·
                refine ⟨1924171914076459773433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282781276050973182288739 1924171914076459773433109)
                ·
                  refine ⟨90195558472334051879677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1924171914076459773433109 90195558472334051879677)
                  ·
                    rfl

theorem cell23_1580897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_1580897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580897 prefixEnd_1580897 := by exact prefixLift 1580897
  have htrace : WordTrace (prefixWord ++ tailWord_1580897) baseStart_1580897 baseEnd_1580897 := by
    simpa [prefixWord, tailWord_1580897, baseEnd_1580897] using wordTrace_append hprefix tailTrace_1580897
  have hstable : (prefixWord ++ tailWord_1580897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580897).length < 2 ^ (prefixWord ++ tailWord_1580897).sum := by decide
  have hdescent : baseEnd_1580897 < baseStart_1580897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580961 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1580961 : Nat := 118140960795 + 1580961 * 2 ^ 59
def prefixEnd_1580961 : Nat := 4983230072969 + 3 ^ 40 * 1580961 * 2
def baseEnd_1580961 : Nat := 270597629670964738838933

theorem tailTrace_1580961 : CollatzResearch.WordTrace tailWord_1580961 prefixEnd_1580961 270597629670964738838933 := by
  unfold tailWord_1580961
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662384825455778487582737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38441589883637185658388491 57662384825455778487582737)
  ·
    refine ⟨43246788619091833865687053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57662384825455778487582737 43246788619091833865687053)
    ·
      refine ⟨16217545732159437699632645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43246788619091833865687053 16217545732159437699632645)
      ·
        refine ⟨3040789824779894568681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16217545732159437699632645 3040789824779894568681121)
        ·
          refine ⟨2280592368584920926510841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040789824779894568681121 2280592368584920926510841)
          ·
            refine ⟨1710444276438690694883131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280592368584920926510841 1710444276438690694883131)
            ·
              refine ⟨2565666414658036042324697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710444276438690694883131 2565666414658036042324697)
              ·
                refine ⟨1924249810993527031743523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565666414658036042324697 1924249810993527031743523)
                ·
                  refine ⟨2886374716490290547615285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924249810993527031743523 2886374716490290547615285)
                  ·
                    refine ⟨270597629670964738838933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2886374716490290547615285 270597629670964738838933)
                    ·
                      rfl

theorem cell23_1580961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1580961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580961 prefixEnd_1580961 := by exact prefixLift 1580961
  have htrace : WordTrace (prefixWord ++ tailWord_1580961) baseStart_1580961 baseEnd_1580961 := by
    simpa [prefixWord, tailWord_1580961, baseEnd_1580961] using wordTrace_append hprefix tailTrace_1580961
  have hstable : (prefixWord ++ tailWord_1580961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580961).length < 2 ^ (prefixWord ++ tailWord_1580961).sum := by decide
  have hdescent : baseEnd_1580961 < baseStart_1580961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580964 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_1580964 : Nat := 118140960795 + 1580964 * 2 ^ 59
def prefixEnd_1580964 : Nat := 4983230072969 + 3 ^ 40 * 1580964 * 2
def baseEnd_1580964 : Nat := 811794429454857704779285

theorem tailTrace_1580964 : CollatzResearch.WordTrace tailWord_1580964 prefixEnd_1580964 811794429454857704779285 := by
  unfold tailWord_1580964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28831247122222454999970973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38441662829629939999961297 28831247122222454999970973)
  ·
    refine ⟨10811717670833420624989115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28831247122222454999970973 10811717670833420624989115)
    ·
      refine ⟨16217576506250130937483673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811717670833420624989115 16217576506250130937483673)
      ·
        refine ⟨12163182379687598203112755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16217576506250130937483673 12163182379687598203112755)
        ·
          refine ⟨18244773569531397304669133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12163182379687598203112755 18244773569531397304669133)
          ·
            refine ⟨6841790088574273989250925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18244773569531397304669133 6841790088574273989250925)
            ·
              refine ⟨2565671283215352745969097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841790088574273989250925 2565671283215352745969097)
              ·
                refine ⟨1924253462411514559476823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565671283215352745969097 1924253462411514559476823)
                ·
                  refine ⟨2886380193617271839215235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924253462411514559476823 2886380193617271839215235)
                  ·
                    refine ⟨4329570290425907758822853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886380193617271839215235 4329570290425907758822853)
                    ·
                      refine ⟨811794429454857704779285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4329570290425907758822853 811794429454857704779285)
                      ·
                        rfl

theorem cell23_1580964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_1580964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580964 prefixEnd_1580964 := by exact prefixLift 1580964
  have htrace : WordTrace (prefixWord ++ tailWord_1580964) baseStart_1580964 baseEnd_1580964 := by
    simpa [prefixWord, tailWord_1580964, baseEnd_1580964] using wordTrace_append hprefix tailTrace_1580964
  have hstable : (prefixWord ++ tailWord_1580964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580964).length < 2 ^ (prefixWord ++ tailWord_1580964).sum := by decide
  have hdescent : baseEnd_1580964 < baseStart_1580964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580977 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1580977 : Nat := 118140960795 + 1580977 * 2 ^ 59
def prefixEnd_1580977 : Nat := 4983230072969 + 3 ^ 40 * 1580977 * 2
def baseEnd_1580977 : Nat := 811801104703366153916725

theorem tailTrace_1580977 : CollatzResearch.WordTrace tailWord_1580977 prefixEnd_1580977 811801104703366153916725 := by
  unfold tailWord_1580977
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662968393397813220165185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38441978928931875480110123 57662968393397813220165185)
  ·
    refine ⟨43247226295048359915123889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57662968393397813220165185 43247226295048359915123889)
    ·
      refine ⟨32435419721286269936342917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43247226295048359915123889 32435419721286269936342917)
      ·
        refine ⟨6081641197741175613064297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32435419721286269936342917 6081641197741175613064297)
        ·
          refine ⟨4561230898305881709798223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081641197741175613064297 4561230898305881709798223)
          ·
            refine ⟨6841846347458822564697335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561230898305881709798223 6841846347458822564697335)
            ·
              refine ⟨10262769521188233847046003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841846347458822564697335 10262769521188233847046003)
              ·
                refine ⟨15394154281782350770569005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262769521188233847046003 15394154281782350770569005)
                ·
                  refine ⟨5772807855668381538963377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15394154281782350770569005 5772807855668381538963377)
                  ·
                    refine ⟨4329605891751286154222533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5772807855668381538963377 4329605891751286154222533)
                    ·
                      refine ⟨811801104703366153916725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4329605891751286154222533 811801104703366153916725)
                      ·
                        rfl

theorem cell23_1580977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1580977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580977 prefixEnd_1580977 := by exact prefixLift 1580977
  have htrace : WordTrace (prefixWord ++ tailWord_1580977) baseStart_1580977 baseEnd_1580977 := by
    simpa [prefixWord, tailWord_1580977, baseEnd_1580977] using wordTrace_append hprefix tailTrace_1580977
  have hstable : (prefixWord ++ tailWord_1580977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580977).length < 2 ^ (prefixWord ++ tailWord_1580977).sum := by decide
  have hdescent : baseEnd_1580977 < baseStart_1580977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580981 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1580981 : Nat := 118140960795 + 1580981 * 2 ^ 59
def prefixEnd_1580981 : Nat := 4983230072969 + 3 ^ 40 * 1580981 * 2
def baseEnd_1580981 : Nat := 811803158625984138266707

theorem tailTrace_1580981 : CollatzResearch.WordTrace tailWord_1580981 prefixEnd_1580981 811803158625984138266707 := by
  unfold tailWord_1580981
  simp only [CollatzResearch.WordTrace]
  refine ⟨57663114285383321903310797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38442076190255547935540531 57663114285383321903310797)
  ·
    refine ⟨21623667857018745713741549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57663114285383321903310797 21623667857018745713741549)
    ·
      refine ⟨8108875446382029642653081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21623667857018745713741549 8108875446382029642653081)
      ·
        refine ⟨6081656584786522231989811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108875446382029642653081 6081656584786522231989811)
        ·
          refine ⟨9122484877179783347984717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081656584786522231989811 9122484877179783347984717)
          ·
            refine ⟨3420931828942418755494269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9122484877179783347984717 3420931828942418755494269)
            ·
              refine ⟨1282849435853407033310351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3420931828942418755494269 1282849435853407033310351)
              ·
                refine ⟨1924274153780110549965527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282849435853407033310351 1924274153780110549965527)
                ·
                  refine ⟨2886411230670165824948291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924274153780110549965527 2886411230670165824948291)
                  ·
                    refine ⟨4329616846005248737422437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886411230670165824948291 4329616846005248737422437)
                    ·
                      refine ⟨811803158625984138266707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4329616846005248737422437 811803158625984138266707)
                      ·
                        rfl

theorem cell23_1580981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1580981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1580981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1580981 prefixEnd_1580981 := by exact prefixLift 1580981
  have htrace : WordTrace (prefixWord ++ tailWord_1580981) baseStart_1580981 baseEnd_1580981 := by
    simpa [prefixWord, tailWord_1580981, baseEnd_1580981] using wordTrace_append hprefix tailTrace_1580981
  have hstable : (prefixWord ++ tailWord_1580981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580981).length < 2 ^ (prefixWord ++ tailWord_1580981).sum := by decide
  have hdescent : baseEnd_1580981 < baseStart_1580981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581062 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1581062 : Nat := 118140960795 + 1581062 * 2 ^ 59
def prefixEnd_1581062 : Nat := 4983230072969 + 3 ^ 40 * 1581062 * 2
def baseEnd_1581062 : Nat := 811844750558998321353835

theorem tailTrace_1581062 : CollatzResearch.WordTrace tailWord_1581062 prefixEnd_1581062 811844750558998321353835 := by
  unfold tailWord_1581062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802064643690308523031545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38444045732059915158006293 1802064643690308523031545)
  ·
    refine ⟨1351548482767731392273659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802064643690308523031545 1351548482767731392273659)
    ·
      refine ⟨2027322724151597088410489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351548482767731392273659 2027322724151597088410489)
      ·
        refine ⟨1520492043113697816307867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027322724151597088410489 1520492043113697816307867)
        ·
          refine ⟨2280738064670546724461801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520492043113697816307867 2280738064670546724461801)
          ·
            refine ⟨1710553548502910043346351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280738064670546724461801 1710553548502910043346351)
            ·
              refine ⟨2565830322754365065019527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710553548502910043346351 2565830322754365065019527)
              ·
                refine ⟨3848745484131547597529291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565830322754365065019527 3848745484131547597529291)
                ·
                  refine ⟨5773118226197321396293937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848745484131547597529291 5773118226197321396293937)
                  ·
                    refine ⟨4329838669647991047220453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773118226197321396293937 4329838669647991047220453)
                    ·
                      refine ⟨811844750558998321353835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4329838669647991047220453 811844750558998321353835)
                      ·
                        rfl

theorem cell23_1581062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1581062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581062 prefixEnd_1581062 := by exact prefixLift 1581062
  have htrace : WordTrace (prefixWord ++ tailWord_1581062) baseStart_1581062 baseEnd_1581062 := by
    simpa [prefixWord, tailWord_1581062, baseEnd_1581062] using wordTrace_append hprefix tailTrace_1581062
  have hstable : (prefixWord ++ tailWord_1581062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581062).length < 2 ^ (prefixWord ++ tailWord_1581062).sum := by decide
  have hdescent : baseEnd_1581062 < baseStart_1581062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581067 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_1581067 : Nat := 118140960795 + 1581067 * 2 ^ 59
def prefixEnd_1581067 : Nat := 4983230072969 + 3 ^ 40 * 1581067 * 2
def baseEnd_1581067 : Nat := 811847317962270801791311

theorem tailTrace_1581067 : CollatzResearch.WordTrace tailWord_1581067 prefixEnd_1581067 811847317962270801791311 := by
  unfold tailWord_1581067
  simp only [CollatzResearch.WordTrace]
  refine ⟨57666250963071758590941455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38444167308714505727294303 57666250963071758590941455)
  ·
    refine ⟨86499376444607637886412183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57666250963071758590941455 86499376444607637886412183)
    ·
      refine ⟨129749064666911456829618275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86499376444607637886412183 129749064666911456829618275)
      ·
        refine ⟨194623597000367185244427413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129749064666911456829618275 194623597000367185244427413)
        ·
          refine ⟨9122981109392211808332535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194623597000367185244427413 9122981109392211808332535)
          ·
            refine ⟨13684471664088317712498803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122981109392211808332535 13684471664088317712498803)
            ·
              refine ⟨20526707496132476568748205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13684471664088317712498803 20526707496132476568748205)
              ·
                refine ⟨7697515311049678713280577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20526707496132476568748205 7697515311049678713280577)
                ·
                  refine ⟨5773136483287259034960433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7697515311049678713280577 5773136483287259034960433)
                  ·
                    refine ⟨4329852362465444276220325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5773136483287259034960433 4329852362465444276220325)
                    ·
                      refine ⟨811847317962270801791311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4329852362465444276220325 811847317962270801791311)
                      ·
                        rfl

theorem cell23_1581067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_1581067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581067 prefixEnd_1581067 := by exact prefixLift 1581067
  have htrace : WordTrace (prefixWord ++ tailWord_1581067) baseStart_1581067 baseEnd_1581067 := by
    simpa [prefixWord, tailWord_1581067, baseEnd_1581067] using wordTrace_append hprefix tailTrace_1581067
  have hstable : (prefixWord ++ tailWord_1581067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581067).length < 2 ^ (prefixWord ++ tailWord_1581067).sum := by decide
  have hdescent : baseEnd_1581067 < baseStart_1581067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581107 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 4, 5]
def baseStart_1581107 : Nat := 118140960795 + 1581107 * 2 ^ 59
def prefixEnd_1581107 : Nat := 4983230072969 + 3 ^ 40 * 1581107 * 2
def baseEnd_1581107 : Nat := 270622619062816881763709

theorem tailTrace_1581107 : CollatzResearch.WordTrace tailWord_1581107 prefixEnd_1581107 270622619062816881763709 := by
  unfold tailWord_1581107
  simp only [CollatzResearch.WordTrace]
  refine ⟨57667709882926845422397575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38445139921951230281598383 57667709882926845422397575)
  ·
    refine ⟨86501564824390268133596363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57667709882926845422397575 86501564824390268133596363)
    ·
      refine ⟨129752347236585402200394545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86501564824390268133596363 129752347236585402200394545)
      ·
        refine ⟨97314260427439051650295909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129752347236585402200394545 97314260427439051650295909)
        ·
          refine ⟨18246423830144822184430483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97314260427439051650295909 18246423830144822184430483)
          ·
            refine ⟨27369635745217233276645725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18246423830144822184430483 27369635745217233276645725)
            ·
              refine ⟨10263613404456462478742147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27369635745217233276645725 10263613404456462478742147)
              ·
                refine ⟨15395420106684693718113221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10263613404456462478742147 15395420106684693718113221)
                ·
                  refine ⟨2886641270003380072146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15395420106684693718113221 2886641270003380072146229)
                  ·
                    refine ⟨270622619062816881763709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2886641270003380072146229 270622619062816881763709)
                    ·
                      rfl

theorem cell23_1581107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].length) (baseStart_1581107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581107 prefixEnd_1581107 := by exact prefixLift 1581107
  have htrace : WordTrace (prefixWord ++ tailWord_1581107) baseStart_1581107 baseEnd_1581107 := by
    simpa [prefixWord, tailWord_1581107, baseEnd_1581107] using wordTrace_append hprefix tailTrace_1581107
  have hstable : (prefixWord ++ tailWord_1581107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581107).length < 2 ^ (prefixWord ++ tailWord_1581107).sum := by decide
  have hdescent : baseEnd_1581107 < baseStart_1581107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581114 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_1581114 : Nat := 118140960795 + 1581114 * 2 ^ 59
def prefixEnd_1581114 : Nat := 4983230072969 + 3 ^ 40 * 1581114 * 2
def baseEnd_1581114 : Nat := 811871451553032117903595

theorem tailTrace_1581114 : CollatzResearch.WordTrace tailWord_1581114 prefixEnd_1581114 811871451553032117903595 := by
  unfold tailWord_1581114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416991298475371404475599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38445310129267657078601597 14416991298475371404475599)
  ·
    refine ⟨21625486947713057106713399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14416991298475371404475599 21625486947713057106713399)
    ·
      refine ⟨32438230421569585660070099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21625486947713057106713399 32438230421569585660070099)
      ·
        refine ⟨48657345632354378490105149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32438230421569585660070099 48657345632354378490105149)
        ·
          refine ⟨18246504612132891933789431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48657345632354378490105149 18246504612132891933789431)
          ·
            refine ⟨27369756918199337900684147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18246504612132891933789431 27369756918199337900684147)
            ·
              refine ⟨41054635377299006851026221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27369756918199337900684147 41054635377299006851026221)
              ·
                refine ⟨15395488266487127569134833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41054635377299006851026221 15395488266487127569134833)
                ·
                  refine ⟨11546616199865345676851125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15395488266487127569134833 11546616199865345676851125)
                  ·
                    refine ⟨1082495268737376157204793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11546616199865345676851125 1082495268737376157204793)
                    ·
                      refine ⟨811871451553032117903595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082495268737376157204793 811871451553032117903595)
                      ·
                        rfl

theorem cell23_1581114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_1581114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581114 prefixEnd_1581114 := by exact prefixLift 1581114
  have htrace : WordTrace (prefixWord ++ tailWord_1581114) baseStart_1581114 baseEnd_1581114 := by
    simpa [prefixWord, tailWord_1581114, baseEnd_1581114] using wordTrace_append hprefix tailTrace_1581114
  have hstable : (prefixWord ++ tailWord_1581114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581114).length < 2 ^ (prefixWord ++ tailWord_1581114).sum := by decide
  have hdescent : baseEnd_1581114 < baseStart_1581114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581144 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1581144 : Nat := 118140960795 + 1581144 * 2 ^ 59
def prefixEnd_1581144 : Nat := 4983230072969 + 3 ^ 40 * 1581144 * 2
def baseEnd_1581144 : Nat := 811886855972667000528457

theorem tailTrace_1581144 : CollatzResearch.WordTrace tailWord_1581144 prefixEnd_1581144 811886855972667000528457 := by
  unfold tailWord_1581144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834529691896400370747243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38446039589195200494329657 28834529691896400370747243)
  ·
    refine ⟨43251794537844600556120865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28834529691896400370747243 43251794537844600556120865)
    ·
      refine ⟨32438845903383450417090649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43251794537844600556120865 32438845903383450417090649)
      ·
        refine ⟨24329134427537587812817987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32438845903383450417090649 24329134427537587812817987)
        ·
          refine ⟨36493701641306381719226981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24329134427537587812817987 36493701641306381719226981)
          ·
            refine ⟨6842569057744946572355059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36493701641306381719226981 6842569057744946572355059)
            ·
              refine ⟨10263853586617419858532589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842569057744946572355059 10263853586617419858532589)
              ·
                refine ⟨3848945094981532446949721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10263853586617419858532589 3848945094981532446949721)
                ·
                  refine ⟨2886708821236149335212291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848945094981532446949721 2886708821236149335212291)
                  ·
                    refine ⟨4330063231854224002818437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886708821236149335212291 4330063231854224002818437)
                    ·
                      refine ⟨811886855972667000528457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4330063231854224002818437 811886855972667000528457)
                      ·
                        rfl

theorem cell23_1581144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1581144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581144 prefixEnd_1581144 := by exact prefixLift 1581144
  have htrace : WordTrace (prefixWord ++ tailWord_1581144) baseStart_1581144 baseEnd_1581144 := by
    simpa [prefixWord, tailWord_1581144, baseEnd_1581144] using wordTrace_append hprefix tailTrace_1581144
  have hstable : (prefixWord ++ tailWord_1581144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581144).length < 2 ^ (prefixWord ++ tailWord_1581144).sum := by decide
  have hdescent : baseEnd_1581144 < baseStart_1581144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581218 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1581218 : Nat := 118140960795 + 1581218 * 2 ^ 59
def prefixEnd_1581218 : Nat := 4983230072969 + 3 ^ 40 * 1581218 * 2
def baseEnd_1581218 : Nat := 90213872615677745667013

theorem tailTrace_1581218 : CollatzResearch.WordTrace tailWord_1581218 prefixEnd_1581218 90213872615677745667013 := by
  unfold tailWord_1581218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417939596381177844922077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38447838923683140919792205 14417939596381177844922077)
  ·
    refine ⟨5406727348642941691845779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14417939596381177844922077 5406727348642941691845779)
    ·
      refine ⟨8110091022964412537768669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406727348642941691845779 8110091022964412537768669)
      ·
        refine ⟨3041284133611654701663251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8110091022964412537768669 3041284133611654701663251)
        ·
          refine ⟨4561926200417482052494877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041284133611654701663251 4561926200417482052494877)
          ·
            refine ⟨1710722325156555769685579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4561926200417482052494877 1710722325156555769685579)
            ·
              refine ⟨2566083487734833654528369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710722325156555769685579 2566083487734833654528369)
              ·
                refine ⟨1924562615801125240896277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566083487734833654528369 1924562615801125240896277)
                ·
                  refine ⟨90213872615677745667013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1924562615801125240896277 90213872615677745667013)
                  ·
                    rfl

theorem cell23_1581218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1581218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581218 prefixEnd_1581218 := by exact prefixLift 1581218
  have htrace : WordTrace (prefixWord ++ tailWord_1581218) baseStart_1581218 baseEnd_1581218 := by
    simpa [prefixWord, tailWord_1581218, baseEnd_1581218] using wordTrace_append hprefix tailTrace_1581218
  have hstable : (prefixWord ++ tailWord_1581218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581218).length < 2 ^ (prefixWord ++ tailWord_1581218).sum := by decide
  have hdescent : baseEnd_1581218 < baseStart_1581218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581221 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_1581221 : Nat := 118140960795 + 1581221 * 2 ^ 59
def prefixEnd_1581221 : Nat := 4983230072969 + 3 ^ 40 * 1581221 * 2
def baseEnd_1581221 : Nat := 811926393983063199265603

theorem tailTrace_1581221 : CollatzResearch.WordTrace tailWord_1581221 prefixEnd_1581221 811926393983063199265603 := by
  unfold tailWord_1581221
  simp only [CollatzResearch.WordTrace]
  refine ⟨57671867804513842892047517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38447911869675895261365011 57671867804513842892047517)
  ·
    refine ⟨21626950426692691084517819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57671867804513842892047517 21626950426692691084517819)
    ·
      refine ⟨32440425640039036626776729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21626950426692691084517819 32440425640039036626776729)
      ·
        refine ⟨24330319230029277470082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32440425640039036626776729 24330319230029277470082547)
        ·
          refine ⟨36495478845043916205123821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330319230029277470082547 36495478845043916205123821)
          ·
            refine ⟨13685804566891468576921433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36495478845043916205123821 13685804566891468576921433)
            ·
              refine ⟨10264353425168601432691075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13685804566891468576921433 10264353425168601432691075)
              ·
                refine ⟨15396530137752902149036613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10264353425168601432691075 15396530137752902149036613)
                ·
                  refine ⟨2886849400828669152944365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15396530137752902149036613 2886849400828669152944365)
                  ·
                    refine ⟨1082568525310750932354137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2886849400828669152944365 1082568525310750932354137)
                    ·
                      refine ⟨811926393983063199265603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082568525310750932354137 811926393983063199265603)
                      ·
                        rfl

theorem cell23_1581221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_1581221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581221 prefixEnd_1581221 := by exact prefixLift 1581221
  have htrace : WordTrace (prefixWord ++ tailWord_1581221) baseStart_1581221 baseEnd_1581221 := by
    simpa [prefixWord, tailWord_1581221, baseEnd_1581221] using wordTrace_append hprefix tailTrace_1581221
  have hstable : (prefixWord ++ tailWord_1581221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581221).length < 2 ^ (prefixWord ++ tailWord_1581221).sum := by decide
  have hdescent : baseEnd_1581221 < baseStart_1581221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581262 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_1581262 : Nat := 118140960795 + 1581262 * 2 ^ 59
def prefixEnd_1581262 : Nat := 4983230072969 + 3 ^ 40 * 1581262 * 2
def baseEnd_1581262 : Nat := 811947446689897538852915

theorem tailTrace_1581262 : CollatzResearch.WordTrace tailWord_1581262 prefixEnd_1581262 811947446689897538852915 := by
  unfold tailWord_1581262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209170399670663361786255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38448908798243537929526693 7209170399670663361786255)
  ·
    refine ⟨10813755599505995042679383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209170399670663361786255 10813755599505995042679383)
    ·
      refine ⟨16220633399258992564019075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10813755599505995042679383 16220633399258992564019075)
      ·
        refine ⟨24330950098888488846028613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220633399258992564019075 24330950098888488846028613)
        ·
          refine ⟨4562053143541591658630365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24330950098888488846028613 4562053143541591658630365)
          ·
            refine ⟨1710769928828096871986387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4562053143541591658630365 1710769928828096871986387)
            ·
              refine ⟨2566154893242145307979581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710769928828096871986387 2566154893242145307979581)
              ·
                refine ⟨962308084965804490492343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2566154893242145307979581 962308084965804490492343)
                ·
                  refine ⟨1443462127448706735738515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962308084965804490492343 1443462127448706735738515)
                  ·
                    refine ⟨2165193191173060103607773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443462127448706735738515 2165193191173060103607773)
                    ·
                      refine ⟨811947446689897538852915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165193191173060103607773 811947446689897538852915)
                      ·
                        rfl

theorem cell23_1581262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_1581262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581262 prefixEnd_1581262 := by exact prefixLift 1581262
  have htrace : WordTrace (prefixWord ++ tailWord_1581262) baseStart_1581262 baseEnd_1581262 := by
    simpa [prefixWord, tailWord_1581262, baseEnd_1581262] using wordTrace_append hprefix tailTrace_1581262
  have hstable : (prefixWord ++ tailWord_1581262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581262).length < 2 ^ (prefixWord ++ tailWord_1581262).sum := by decide
  have hdescent : baseEnd_1581262 < baseStart_1581262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581285 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1581285 : Nat := 118140960795 + 1581285 * 2 ^ 59
def prefixEnd_1581285 : Nat := 4983230072969 + 3 ^ 40 * 1581285 * 2
def baseEnd_1581285 : Nat := 811959256744950948865309

theorem tailTrace_1581285 : CollatzResearch.WordTrace tailWord_1581285 prefixEnd_1581285 811959256744950948865309 := by
  unfold tailWord_1581285
  simp only [CollatzResearch.WordTrace]
  refine ⟨57674202076281981822377309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38449468050854654548251539 57674202076281981822377309)
  ·
    refine ⟨21627825778605743183391491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57674202076281981822377309 21627825778605743183391491)
    ·
      refine ⟨32441738667908614775087237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21627825778605743183391491 32441738667908614775087237)
      ·
        refine ⟨6082826000232865270328857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32441738667908614775087237 6082826000232865270328857)
        ·
          refine ⟨4562119500174648952746643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6082826000232865270328857 4562119500174648952746643)
          ·
            refine ⟨6843179250261973429119965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562119500174648952746643 6843179250261973429119965)
            ·
              refine ⟨2566192218848240035919987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6843179250261973429119965 2566192218848240035919987)
              ·
                refine ⟨3849288328272360053879981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566192218848240035919987 3849288328272360053879981)
                ·
                  refine ⟨1443483123102135020204993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3849288328272360053879981 1443483123102135020204993)
                  ·
                    refine ⟨1082612342326601265153745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1443483123102135020204993 1082612342326601265153745)
                    ·
                      refine ⟨811959256744950948865309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082612342326601265153745 811959256744950948865309)
                      ·
                        rfl

theorem cell23_1581285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1581285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581285 prefixEnd_1581285 := by exact prefixLift 1581285
  have htrace : WordTrace (prefixWord ++ tailWord_1581285) baseStart_1581285 baseEnd_1581285 := by
    simpa [prefixWord, tailWord_1581285, baseEnd_1581285] using wordTrace_append hprefix tailTrace_1581285
  have hstable : (prefixWord ++ tailWord_1581285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581285).length < 2 ^ (prefixWord ++ tailWord_1581285).sum := by decide
  have hdescent : baseEnd_1581285 < baseStart_1581285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581294 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1581294 : Nat := 118140960795 + 1581294 * 2 ^ 59
def prefixEnd_1581294 : Nat := 4983230072969 + 3 ^ 40 * 1581294 * 2
def baseEnd_1581294 : Nat := 811963878070841413652767

theorem tailTrace_1581294 : CollatzResearch.WordTrace tailWord_1581294 prefixEnd_1581294 811963878070841413652767 := by
  unfold tailWord_1581294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209316291656172044931867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38449686888832917572969957 7209316291656172044931867)
  ·
    refine ⟨10813974437484258067397801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209316291656172044931867 10813974437484258067397801)
    ·
      refine ⟨8110480828113193550548351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10813974437484258067397801 8110480828113193550548351)
      ·
        refine ⟨12165721242169790325822527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8110480828113193550548351 12165721242169790325822527)
        ·
          refine ⟨18248581863254685488733791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165721242169790325822527 18248581863254685488733791)
          ·
            refine ⟨27372872794882028233100687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18248581863254685488733791 27372872794882028233100687)
            ·
              refine ⟨41059309192323042349651031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27372872794882028233100687 41059309192323042349651031)
              ·
                refine ⟨61588963788484563524476547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41059309192323042349651031 61588963788484563524476547)
                ·
                  refine ⟨92383445682726845286714821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61588963788484563524476547 92383445682726845286714821)
                  ·
                    refine ⟨17321896065511283491259029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92383445682726845286714821 17321896065511283491259029)
                    ·
                      refine ⟨811963878070841413652767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17321896065511283491259029 811963878070841413652767)
                      ·
                        rfl

theorem cell23_1581294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1581294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581294 prefixEnd_1581294 := by exact prefixLift 1581294
  have htrace : WordTrace (prefixWord ++ tailWord_1581294) baseStart_1581294 baseEnd_1581294 := by
    simpa [prefixWord, tailWord_1581294, baseEnd_1581294] using wordTrace_append hprefix tailTrace_1581294
  have hstable : (prefixWord ++ tailWord_1581294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581294).length < 2 ^ (prefixWord ++ tailWord_1581294).sum := by decide
  have hdescent : baseEnd_1581294 < baseStart_1581294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581295 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 2, 4]
def baseStart_1581295 : Nat := 118140960795 + 1581295 * 2 ^ 59
def prefixEnd_1581295 : Nat := 4983230072969 + 3 ^ 40 * 1581295 * 2
def baseEnd_1581295 : Nat := 270654797183831969913421

theorem tailTrace_1581295 : CollatzResearch.WordTrace tailWord_1581295 prefixEnd_1581295 270654797183831969913421 := by
  unfold tailWord_1581295
  simp only [CollatzResearch.WordTrace]
  refine ⟨57674566806245753530241339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38449711204163835686827559 57674566806245753530241339)
  ·
    refine ⟨86511850209368630295362009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57674566806245753530241339 86511850209368630295362009)
    ·
      refine ⟨64883887657026472721521507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86511850209368630295362009 64883887657026472721521507)
      ·
        refine ⟨97325831485539709082282261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64883887657026472721521507 97325831485539709082282261)
        ·
          refine ⟨4562148350884673863231981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97325831485539709082282261 4562148350884673863231981)
          ·
            refine ⟨1710805631581752698711993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4562148350884673863231981 1710805631581752698711993)
            ·
              refine ⟨1283104223686314524033995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710805631581752698711993 1283104223686314524033995)
              ·
                refine ⟨1924656335529471786050993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283104223686314524033995 1924656335529471786050993)
                ·
                  refine ⟨1443492251647103839538245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924656335529471786050993 1443492251647103839538245)
                  ·
                    refine ⟨270654797183831969913421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443492251647103839538245 270654797183831969913421)
                    ·
                      rfl

theorem cell23_1581295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_1581295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581295 prefixEnd_1581295 := by exact prefixLift 1581295
  have htrace : WordTrace (prefixWord ++ tailWord_1581295) baseStart_1581295 baseEnd_1581295 := by
    simpa [prefixWord, tailWord_1581295, baseEnd_1581295] using wordTrace_append hprefix tailTrace_1581295
  have hstable : (prefixWord ++ tailWord_1581295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581295).length < 2 ^ (prefixWord ++ tailWord_1581295).sum := by decide
  have hdescent : baseEnd_1581295 < baseStart_1581295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581335 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1581335 : Nat := 118140960795 + 1581335 * 2 ^ 59
def prefixEnd_1581335 : Nat := 4983230072969 + 3 ^ 40 * 1581335 * 2
def baseEnd_1581335 : Nat := 811984930777675753240079

theorem tailTrace_1581335 : CollatzResearch.WordTrace tailWord_1581335 prefixEnd_1581335 811984930777675753240079 := by
  unfold tailWord_1581335
  simp only [CollatzResearch.WordTrace]
  refine ⟨57676025726100840361697459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38450683817400560241131639 57676025726100840361697459)
  ·
    refine ⟨86514038589151260542546189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57676025726100840361697459 86514038589151260542546189)
    ·
      refine ⟨32442764470931722703454821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86514038589151260542546189 32442764470931722703454821)
      ·
        refine ⟨6083018338299698006897779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32442764470931722703454821 6083018338299698006897779)
        ·
          refine ⟨9124527507449547010346669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083018338299698006897779 9124527507449547010346669)
          ·
            refine ⟨3421697815293580128880001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9124527507449547010346669 3421697815293580128880001)
            ·
              refine ⟨2566273361470185096660001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421697815293580128880001 2566273361470185096660001)
              ·
                refine ⟨1924705021102638822495001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566273361470185096660001 1924705021102638822495001)
                ·
                  refine ⟨1443528765826979116871251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924705021102638822495001 1443528765826979116871251)
                  ·
                    refine ⟨2165293148740468675306877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443528765826979116871251 2165293148740468675306877)
                    ·
                      refine ⟨811984930777675753240079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165293148740468675306877 811984930777675753240079)
                      ·
                        rfl

theorem cell23_1581335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1581335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581335 prefixEnd_1581335 := by exact prefixLift 1581335
  have htrace : WordTrace (prefixWord ++ tailWord_1581335) baseStart_1581335 baseEnd_1581335 := by
    simpa [prefixWord, tailWord_1581335, baseEnd_1581335] using wordTrace_append hprefix tailTrace_1581335
  have hstable : (prefixWord ++ tailWord_1581335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581335).length < 2 ^ (prefixWord ++ tailWord_1581335).sum := by decide
  have hdescent : baseEnd_1581335 < baseStart_1581335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581392 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2]
def baseStart_1581392 : Nat := 118140960795 + 1581392 * 2 ^ 59
def prefixEnd_1581392 : Nat := 4983230072969 + 3 ^ 40 * 1581392 * 2
def baseEnd_1581392 : Nat := 812014199174982030227317

theorem tailTrace_1581392 : CollatzResearch.WordTrace tailWord_1581392 prefixEnd_1581392 812014199174982030227317 := by
  unfold tailWord_1581392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28839052343447169548261215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38452069791262892731014953 28839052343447169548261215)
  ·
    refine ⟨43258578515170754322391823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28839052343447169548261215 43258578515170754322391823)
    ·
      refine ⟨64887867772756131483587735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43258578515170754322391823 64887867772756131483587735)
      ·
        refine ⟨97331801659134197225381603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64887867772756131483587735 97331801659134197225381603)
        ·
          refine ⟨145997702488701295838072405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97331801659134197225381603 145997702488701295838072405)
          ·
            refine ⟨1710910576039468310602411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 145997702488701295838072405 1710910576039468310602411)
            ·
              refine ⟨2566365864059202465903617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710910576039468310602411 2566365864059202465903617)
              ·
                refine ⟨1924774398044401849427713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566365864059202465903617 1924774398044401849427713)
                ·
                  refine ⟨1443580798533301387070785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924774398044401849427713 1443580798533301387070785)
                  ·
                    refine ⟨1082685598899976040303089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1443580798533301387070785 1082685598899976040303089)
                    ·
                      refine ⟨812014199174982030227317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082685598899976040303089 812014199174982030227317)
                      ·
                        rfl

theorem cell23_1581392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2].length) (baseStart_1581392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581392 prefixEnd_1581392 := by exact prefixLift 1581392
  have htrace : WordTrace (prefixWord ++ tailWord_1581392) baseStart_1581392 baseEnd_1581392 := by
    simpa [prefixWord, tailWord_1581392, baseEnd_1581392] using wordTrace_append hprefix tailTrace_1581392
  have hstable : (prefixWord ++ tailWord_1581392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581392).length < 2 ^ (prefixWord ++ tailWord_1581392).sum := by decide
  have hdescent : baseEnd_1581392 < baseStart_1581392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581448 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1581448 : Nat := 118140960795 + 1581448 * 2 ^ 59
def prefixEnd_1581448 : Nat := 4983230072969 + 3 ^ 40 * 1581448 * 2
def baseEnd_1581448 : Nat := 812042954091633811127059

theorem tailTrace_1581448 : CollatzResearch.WordTrace tailWord_1581448 prefixEnd_1581448 812042954091633811127059 := by
  unfold tailWord_1581448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28840073587345730330280499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38453431449794307107040665 28840073587345730330280499)
  ·
    refine ⟨43260110381018595495420749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28840073587345730330280499 43260110381018595495420749)
    ·
      refine ⟨16222541392881973310782781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43260110381018595495420749 16222541392881973310782781)
      ·
        refine ⟨6083453022330739991543543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16222541392881973310782781 6083453022330739991543543)
        ·
          refine ⟨9125179533496109987315315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083453022330739991543543 9125179533496109987315315)
          ·
            refine ⟨13687769300244164980972973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125179533496109987315315 13687769300244164980972973)
            ·
              refine ⟨5132913487591561867864865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13687769300244164980972973 5132913487591561867864865)
              ·
                refine ⟨3849685115693671400898649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132913487591561867864865 3849685115693671400898649)
                ·
                  refine ⟨2887263836770253550673987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849685115693671400898649 2887263836770253550673987)
                  ·
                    refine ⟨4330895755155380326010981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2887263836770253550673987 4330895755155380326010981)
                    ·
                      refine ⟨812042954091633811127059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4330895755155380326010981 812042954091633811127059)
                      ·
                        rfl

theorem cell23_1581448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1581448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581448 prefixEnd_1581448 := by exact prefixLift 1581448
  have htrace : WordTrace (prefixWord ++ tailWord_1581448) baseStart_1581448 baseEnd_1581448 := by
    simpa [prefixWord, tailWord_1581448, baseEnd_1581448] using wordTrace_append hprefix tailTrace_1581448
  have hstable : (prefixWord ++ tailWord_1581448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581448).length < 2 ^ (prefixWord ++ tailWord_1581448).sum := by decide
  have hdescent : baseEnd_1581448 < baseStart_1581448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581481 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_1581481 : Nat := 118140960795 + 1581481 * 2 ^ 59
def prefixEnd_1581481 : Nat := 4983230072969 + 3 ^ 40 * 1581481 * 2
def baseEnd_1581481 : Nat := 812059898953232182014407

theorem tailTrace_1581481 : CollatzResearch.WordTrace tailWord_1581481 prefixEnd_1581481 812059898953232182014407 := by
  unfold tailWord_1581481
  simp only [CollatzResearch.WordTrace]
  refine ⟨57681350783571907296512297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38454233855714604864341531 57681350783571907296512297)
  ·
    refine ⟨43261013087678930472384223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57681350783571907296512297 43261013087678930472384223)
    ·
      refine ⟨64891519631518395708576335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43261013087678930472384223 64891519631518395708576335)
      ·
        refine ⟨97337279447277593562864503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64891519631518395708576335 97337279447277593562864503)
        ·
          refine ⟨146005919170916390344296755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97337279447277593562864503 146005919170916390344296755)
          ·
            refine ⟨219008878756374585516445133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146005919170916390344296755 219008878756374585516445133)
            ·
              refine ⟨82128329533640469568666925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219008878756374585516445133 82128329533640469568666925)
              ·
                refine ⟨30798123575115176088250097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82128329533640469568666925 30798123575115176088250097)
                ·
                  refine ⟨23098592681336382066187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30798123575115176088250097 23098592681336382066187573)
                  ·
                    refine ⟨2165493063875285818705085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23098592681336382066187573 2165493063875285818705085)
                    ·
                      refine ⟨812059898953232182014407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165493063875285818705085 812059898953232182014407)
                      ·
                        rfl

theorem cell23_1581481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_1581481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581481 prefixEnd_1581481 := by exact prefixLift 1581481
  have htrace : WordTrace (prefixWord ++ tailWord_1581481) baseStart_1581481 baseEnd_1581481 := by
    simpa [prefixWord, tailWord_1581481, baseEnd_1581481] using wordTrace_append hprefix tailTrace_1581481
  have hstable : (prefixWord ++ tailWord_1581481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581481).length < 2 ^ (prefixWord ++ tailWord_1581481).sum := by decide
  have hdescent : baseEnd_1581481 < baseStart_1581481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581548 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_1581548 : Nat := 118140960795 + 1581548 * 2 ^ 59
def prefixEnd_1581548 : Nat := 4983230072969 + 3 ^ 40 * 1581548 * 2
def baseEnd_1581548 : Nat := 270698100719027806625533

theorem tailTrace_1581548 : CollatzResearch.WordTrace tailWord_1581548 prefixEnd_1581548 270698100719027806625533 := by
  unfold tailWord_1581548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841897237164588869600649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38455862982886118492800865 28841897237164588869600649)
  ·
    refine ⟨21631422927873441652200487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28841897237164588869600649 21631422927873441652200487)
    ·
      refine ⟨32447134391810162478300731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21631422927873441652200487 32447134391810162478300731)
      ·
        refine ⟨48670701587715243717451097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32447134391810162478300731 48670701587715243717451097)
        ·
          refine ⟨36503026190786432788088323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48670701587715243717451097 36503026190786432788088323)
          ·
            refine ⟨54754539286179649182132485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36503026190786432788088323 54754539286179649182132485)
            ·
              refine ⟨10266476116158684221649841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54754539286179649182132485 10266476116158684221649841)
              ·
                refine ⟨7699857087119013166237381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10266476116158684221649841 7699857087119013166237381)
                ·
                  refine ⟨1443723203834814968669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7699857087119013166237381 1443723203834814968669509)
                  ·
                    refine ⟨270698100719027806625533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443723203834814968669509 270698100719027806625533)
                    ·
                      rfl

theorem cell23_1581548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_1581548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581548 prefixEnd_1581548 := by exact prefixLift 1581548
  have htrace : WordTrace (prefixWord ++ tailWord_1581548) baseStart_1581548 baseEnd_1581548 := by
    simpa [prefixWord, tailWord_1581548, baseEnd_1581548] using wordTrace_append hprefix tailTrace_1581548
  have hstable : (prefixWord ++ tailWord_1581548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581548).length < 2 ^ (prefixWord ++ tailWord_1581548).sum := by decide
  have hdescent : baseEnd_1581548 < baseStart_1581548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581549 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1581549 : Nat := 118140960795 + 1581549 * 2 ^ 59
def prefixEnd_1581549 : Nat := 4983230072969 + 3 ^ 40 * 1581549 * 2
def baseEnd_1581549 : Nat := 812094815637737915964095

theorem tailTrace_1581549 : CollatzResearch.WordTrace tailWord_1581549 prefixEnd_1581549 812094815637737915964095 := by
  unfold tailWord_1581549
  simp only [CollatzResearch.WordTrace]
  refine ⟨57683830947325554909987701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38455887298217036606658467 57683830947325554909987701)
  ·
    refine ⟨5407859151311770772811347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57683830947325554909987701 5407859151311770772811347)
    ·
      refine ⟨8111788726967656159217021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407859151311770772811347 8111788726967656159217021)
      ·
        refine ⟨3041920772612871059706383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8111788726967656159217021 3041920772612871059706383)
        ·
          refine ⟨4562881158919306589559575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041920772612871059706383 4562881158919306589559575)
          ·
            refine ⟨6844321738378959884339363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562881158919306589559575 6844321738378959884339363)
            ·
              refine ⟨10266482607568439826509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844321738378959884339363 10266482607568439826509045)
              ·
                refine ⟨962482744459541233735223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10266482607568439826509045 962482744459541233735223)
                ·
                  refine ⟨1443724116689311850602835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962482744459541233735223 1443724116689311850602835)
                  ·
                    refine ⟨2165586175033967775904253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443724116689311850602835 2165586175033967775904253)
                    ·
                      refine ⟨812094815637737915964095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165586175033967775904253 812094815637737915964095)
                      ·
                        rfl

theorem cell23_1581549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1581549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581549 prefixEnd_1581549 := by exact prefixLift 1581549
  have htrace : WordTrace (prefixWord ++ tailWord_1581549) baseStart_1581549 baseEnd_1581549 := by
    simpa [prefixWord, tailWord_1581549, baseEnd_1581549] using wordTrace_append hprefix tailTrace_1581549
  have hstable : (prefixWord ++ tailWord_1581549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581549).length < 2 ^ (prefixWord ++ tailWord_1581549).sum := by decide
  have hdescent : baseEnd_1581549 < baseStart_1581549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581551 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1581551 : Nat := 118140960795 + 1581551 * 2 ^ 59
def prefixEnd_1581551 : Nat := 4983230072969 + 3 ^ 40 * 1581551 * 2
def baseEnd_1581551 : Nat := 812095842599046908139085

theorem tailTrace_1581551 : CollatzResearch.WordTrace tailWord_1581551 prefixEnd_1581551 812095842599046908139085 := by
  unfold tailWord_1581551
  simp only [CollatzResearch.WordTrace]
  refine ⟨57683903893318309251560507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38455935928878872834373671 57683903893318309251560507)
  ·
    refine ⟨86525855839977463877340761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57683903893318309251560507 86525855839977463877340761)
    ·
      refine ⟨64894391879983097908005571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86525855839977463877340761 64894391879983097908005571)
      ·
        refine ⟨97341587819974646862008357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64894391879983097908005571 97341587819974646862008357)
        ·
          refine ⟨18251547716245246286626567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97341587819974646862008357 18251547716245246286626567)
          ·
            refine ⟨27377321574367869429939851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18251547716245246286626567 27377321574367869429939851)
            ·
              refine ⟨41065982361551804144909777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27377321574367869429939851 41065982361551804144909777)
              ·
                refine ⟨30799486771163853108682333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41065982361551804144909777 30799486771163853108682333)
                ·
                  refine ⟨11549807539186444915755875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30799486771163853108682333 11549807539186444915755875)
                  ·
                    refine ⟨17324711308779667373633813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11549807539186444915755875 17324711308779667373633813)
                    ·
                      refine ⟨812095842599046908139085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17324711308779667373633813 812095842599046908139085)
                      ·
                        rfl

theorem cell23_1581551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1581551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581551 prefixEnd_1581551 := by exact prefixLift 1581551
  have htrace : WordTrace (prefixWord ++ tailWord_1581551) baseStart_1581551 baseEnd_1581551 := by
    simpa [prefixWord, tailWord_1581551, baseEnd_1581551] using wordTrace_append hprefix tailTrace_1581551
  have hstable : (prefixWord ++ tailWord_1581551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581551).length < 2 ^ (prefixWord ++ tailWord_1581551).sum := by decide
  have hdescent : baseEnd_1581551 < baseStart_1581551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581555 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 5, 2, 2]
def baseStart_1581555 : Nat := 118140960795 + 1581555 * 2 ^ 59
def prefixEnd_1581555 : Nat := 4983230072969 + 3 ^ 40 * 1581555 * 2
def baseEnd_1581555 : Nat := 812097896521664892489067

theorem tailTrace_1581555 : CollatzResearch.WordTrace tailWord_1581555 prefixEnd_1581555 812097896521664892489067 := by
  unfold tailWord_1581555
  simp only [CollatzResearch.WordTrace]
  refine ⟨57684049785303817934706119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456033190202545289804079 57684049785303817934706119)
  ·
    refine ⟨86526074677955726902059179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57684049785303817934706119 86526074677955726902059179)
    ·
      refine ⟨129789112016933590353088769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86526074677955726902059179 129789112016933590353088769)
      ·
        refine ⟨97341834012700192764816577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129789112016933590353088769 97341834012700192764816577)
        ·
          refine ⟨73006375509525144573612433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97341834012700192764816577 73006375509525144573612433)
          ·
            refine ⟨54754781632143858430209325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73006375509525144573612433 54754781632143858430209325)
            ·
              refine ⟨20533043112053946911328497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54754781632143858430209325 20533043112053946911328497)
              ·
                refine ⟨15399782334040460183496373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20533043112053946911328497 15399782334040460183496373)
                ·
                  refine ⟨1443729593816293142202785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15399782334040460183496373 1443729593816293142202785)
                  ·
                    refine ⟨1082797195362219856652089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1443729593816293142202785 1082797195362219856652089)
                    ·
                      refine ⟨812097896521664892489067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082797195362219856652089 812097896521664892489067)
                      ·
                        rfl

theorem cell23_1581555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 2, 2].length) (baseStart_1581555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581555 prefixEnd_1581555 := by exact prefixLift 1581555
  have htrace : WordTrace (prefixWord ++ tailWord_1581555) baseStart_1581555 baseEnd_1581555 := by
    simpa [prefixWord, tailWord_1581555, baseEnd_1581555] using wordTrace_append hprefix tailTrace_1581555
  have hstable : (prefixWord ++ tailWord_1581555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581555).length < 2 ^ (prefixWord ++ tailWord_1581555).sum := by decide
  have hdescent : baseEnd_1581555 < baseStart_1581555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581575 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1581575 : Nat := 118140960795 + 1581575 * 2 ^ 59
def prefixEnd_1581575 : Nat := 4983230072969 + 3 ^ 40 * 1581575 * 2
def baseEnd_1581575 : Nat := 812108166134754814238975

theorem tailTrace_1581575 : CollatzResearch.WordTrace tailWord_1581575 prefixEnd_1581575 812108166134754814238975 := by
  unfold tailWord_1581575
  simp only [CollatzResearch.WordTrace]
  refine ⟨57684779245231361350434179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456519496820907566956119 57684779245231361350434179)
  ·
    refine ⟨86527168867847042025651269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57684779245231361350434179 86527168867847042025651269)
    ·
      refine ⟨16223844162721320379809613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86527168867847042025651269 16223844162721320379809613)
      ·
        refine ⟨6083941561020495142428605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16223844162721320379809613 6083941561020495142428605)
        ·
          refine ⟨2281478085382685678410727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6083941561020495142428605 2281478085382685678410727)
          ·
            refine ⟨3422217128074028517616091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281478085382685678410727 3422217128074028517616091)
            ·
              refine ⟨5133325692111042776424137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422217128074028517616091 5133325692111042776424137)
              ·
                refine ⟨3849994269083282082318103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133325692111042776424137 3849994269083282082318103)
                ·
                  refine ⟨5774991403624923123477155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849994269083282082318103 5774991403624923123477155)
                  ·
                    refine ⟨8662487105437384685215733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5774991403624923123477155 8662487105437384685215733)
                    ·
                      refine ⟨812108166134754814238975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8662487105437384685215733 812108166134754814238975)
                      ·
                        rfl

theorem cell23_1581575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1581575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581575 prefixEnd_1581575 := by exact prefixLift 1581575
  have htrace : WordTrace (prefixWord ++ tailWord_1581575) baseStart_1581575 baseEnd_1581575 := by
    simpa [prefixWord, tailWord_1581575, baseEnd_1581575] using wordTrace_append hprefix tailTrace_1581575
  have hstable : (prefixWord ++ tailWord_1581575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581575).length < 2 ^ (prefixWord ++ tailWord_1581575).sum := by decide
  have hdescent : baseEnd_1581575 < baseStart_1581575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581592 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1581592 : Nat := 118140960795 + 1581592 * 2 ^ 59
def prefixEnd_1581592 : Nat := 4983230072969 + 3 ^ 40 * 1581592 * 2
def baseEnd_1581592 : Nat := 812116895305881247726397

theorem tailTrace_1581592 : CollatzResearch.WordTrace tailWord_1581592 prefixEnd_1581592 812116895305881247726397 := by
  unfold tailWord_1581592
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842699643084886626901515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38456932857446515502535353 28842699643084886626901515)
  ·
    refine ⟨43264049464627329940352273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28842699643084886626901515 43264049464627329940352273)
    ·
      refine ⟨32448037098470497455264205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43264049464627329940352273 32448037098470497455264205)
      ·
        refine ⟨12168013911926436545724077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32448037098470497455264205 12168013911926436545724077)
        ·
          refine ⟨4563005216972413704646529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12168013911926436545724077 4563005216972413704646529)
          ·
            refine ⟨3422253912729310278484897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563005216972413704646529 3422253912729310278484897)
            ·
              refine ⟨2566690434546982708863673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422253912729310278484897 2566690434546982708863673)
              ·
                refine ⟨1925017825910237031647755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566690434546982708863673 1925017825910237031647755)
                ·
                  refine ⟨2887526738865355547471633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925017825910237031647755 2887526738865355547471633)
                  ·
                    refine ⟨2165645054149016660603725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2887526738865355547471633 2165645054149016660603725)
                    ·
                      refine ⟨812116895305881247726397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165645054149016660603725 812116895305881247726397)
                      ·
                        rfl

theorem cell23_1581592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1581592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581592 prefixEnd_1581592 := by exact prefixLift 1581592
  have htrace : WordTrace (prefixWord ++ tailWord_1581592) baseStart_1581592 baseEnd_1581592 := by
    simpa [prefixWord, tailWord_1581592, baseEnd_1581592] using wordTrace_append hprefix tailTrace_1581592
  have hstable : (prefixWord ++ tailWord_1581592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581592).length < 2 ^ (prefixWord ++ tailWord_1581592).sum := by decide
  have hdescent : baseEnd_1581592 < baseStart_1581592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581605 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_1581605 : Nat := 118140960795 + 1581605 * 2 ^ 59
def prefixEnd_1581605 : Nat := 4983230072969 + 3 ^ 40 * 1581605 * 2
def baseEnd_1581605 : Nat := 812123570554389696863837

theorem tailTrace_1581605 : CollatzResearch.WordTrace tailWord_1581605 prefixEnd_1581605 812123570554389696863837 := by
  unfold tailWord_1581605
  simp only [CollatzResearch.WordTrace]
  refine ⟨57685873435122676474026269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38457248956748450982684179 57685873435122676474026269)
  ·
    refine ⟨21632202538171003677759851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57685873435122676474026269 21632202538171003677759851)
    ·
      refine ⟨32448303807256505516639777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21632202538171003677759851 32448303807256505516639777)
      ·
        refine ⟨24336227855442379137479833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32448303807256505516639777 24336227855442379137479833)
        ·
          refine ⟨18252170891581784353109875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24336227855442379137479833 18252170891581784353109875)
          ·
            refine ⟨27378256337372676529664813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18252170891581784353109875 27378256337372676529664813)
            ·
              refine ⟨10266846126514753698624305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27378256337372676529664813 10266846126514753698624305)
              ·
                refine ⟨7700134594886065273968229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10266846126514753698624305 7700134594886065273968229)
                ·
                  refine ⟨1443775236541137238869043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7700134594886065273968229 1443775236541137238869043)
                  ·
                    refine ⟨2165662854811705858303565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443775236541137238869043 2165662854811705858303565)
                    ·
                      refine ⟨812123570554389696863837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165662854811705858303565 812123570554389696863837)
                      ·
                        rfl

theorem cell23_1581605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_1581605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581605 prefixEnd_1581605 := by exact prefixLift 1581605
  have htrace : WordTrace (prefixWord ++ tailWord_1581605) baseStart_1581605 baseEnd_1581605 := by
    simpa [prefixWord, tailWord_1581605, baseEnd_1581605] using wordTrace_append hprefix tailTrace_1581605
  have hstable : (prefixWord ++ tailWord_1581605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581605).length < 2 ^ (prefixWord ++ tailWord_1581605).sum := by decide
  have hdescent : baseEnd_1581605 < baseStart_1581605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581611 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_1581611 : Nat := 118140960795 + 1581611 * 2 ^ 59
def prefixEnd_1581611 : Nat := 4983230072969 + 3 ^ 40 * 1581611 * 2
def baseEnd_1581611 : Nat := 812126651438316673388809

theorem tailTrace_1581611 : CollatzResearch.WordTrace tailWord_1581611 prefixEnd_1581611 812126651438316673388809 := by
  unfold tailWord_1581611
  simp only [CollatzResearch.WordTrace]
  refine ⟨57686092273100939498744687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38457394848733959665829791 57686092273100939498744687)
  ·
    refine ⟨86529138409651409248117031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57686092273100939498744687 86529138409651409248117031)
    ·
      refine ⟨129793707614477113872175547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86529138409651409248117031 129793707614477113872175547)
      ·
        refine ⟨194690561421715670808263321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129793707614477113872175547 194690561421715670808263321)
        ·
          refine ⟨146017921066286753106197491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194690561421715670808263321 146017921066286753106197491)
          ·
            refine ⟨219026881599430129659296237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146017921066286753106197491 219026881599430129659296237)
            ·
              refine ⟨82135080599786298622236089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219026881599430129659296237 82135080599786298622236089)
              ·
                refine ⟨61601310449839723966677067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82135080599786298622236089 61601310449839723966677067)
                ·
                  refine ⟨92401965674759585950015601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61601310449839723966677067 92401965674759585950015601)
                  ·
                    refine ⟨69301474256069689462511701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92401965674759585950015601 69301474256069689462511701)
                    ·
                      refine ⟨812126651438316673388809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69301474256069689462511701 812126651438316673388809)
                      ·
                        rfl

theorem cell23_1581611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_1581611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581611 prefixEnd_1581611 := by exact prefixLift 1581611
  have htrace : WordTrace (prefixWord ++ tailWord_1581611) baseStart_1581611 baseEnd_1581611 := by
    simpa [prefixWord, tailWord_1581611, baseEnd_1581611] using wordTrace_append hprefix tailTrace_1581611
  have hstable : (prefixWord ++ tailWord_1581611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581611).length < 2 ^ (prefixWord ++ tailWord_1581611).sum := by decide
  have hdescent : baseEnd_1581611 < baseStart_1581611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581639 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_1581639 : Nat := 118140960795 + 1581639 * 2 ^ 59
def prefixEnd_1581639 : Nat := 4983230072969 + 3 ^ 40 * 1581639 * 2
def baseEnd_1581639 : Nat := 812141028896642563838681

theorem tailTrace_1581639 : CollatzResearch.WordTrace tailWord_1581639 prefixEnd_1581639 812141028896642563838681 := by
  unfold tailWord_1581639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57687113516999500280763971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38458075677999666853842647 57687113516999500280763971)
  ·
    refine ⟨86530670275499250421145957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57687113516999500280763971 86530670275499250421145957)
    ·
      refine ⟨16224500676656109453964867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86530670275499250421145957 16224500676656109453964867)
      ·
        refine ⟨24336751014984164180947301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16224500676656109453964867 24336751014984164180947301)
        ·
          refine ⟨4563140815309530783927619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24336751014984164180947301 4563140815309530783927619)
          ·
            refine ⟨6844711222964296175891429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563140815309530783927619 6844711222964296175891429)
            ·
              refine ⟨1283383354305805532979643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6844711222964296175891429 1283383354305805532979643)
              ·
                refine ⟨1925075031458708299469465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283383354305805532979643 1925075031458708299469465)
                ·
                  refine ⟨1443806273594031224602099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925075031458708299469465 1443806273594031224602099)
                  ·
                    refine ⟨2165709410391046836903149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443806273594031224602099 2165709410391046836903149)
                    ·
                      refine ⟨812141028896642563838681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165709410391046836903149 812141028896642563838681)
                      ·
                        rfl

theorem cell23_1581639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_1581639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581639 prefixEnd_1581639 := by exact prefixLift 1581639
  have htrace : WordTrace (prefixWord ++ tailWord_1581639) baseStart_1581639 baseEnd_1581639 := by
    simpa [prefixWord, tailWord_1581639, baseEnd_1581639] using wordTrace_append hprefix tailTrace_1581639
  have hstable : (prefixWord ++ tailWord_1581639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581639).length < 2 ^ (prefixWord ++ tailWord_1581639).sum := by decide
  have hdescent : baseEnd_1581639 < baseStart_1581639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581648 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_1581648 : Nat := 118140960795 + 1581648 * 2 ^ 59
def prefixEnd_1581648 : Nat := 4983230072969 + 3 ^ 40 * 1581648 * 2
def baseEnd_1581648 : Nat := 812145650222533028626139

theorem tailTrace_1581648 : CollatzResearch.WordTrace tailWord_1581648 prefixEnd_1581648 812145650222533028626139 := by
  unfold tailWord_1581648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843720886983447408920799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38458294515977929878561065 28843720886983447408920799)
  ·
    refine ⟨43265581330475171113381199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843720886983447408920799 43265581330475171113381199)
    ·
      refine ⟨64898371995712756670071799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43265581330475171113381199 64898371995712756670071799)
      ·
        refine ⟨97347557993569135005107699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64898371995712756670071799 97347557993569135005107699)
        ·
          refine ⟨146021336990353702507661549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97347557993569135005107699 146021336990353702507661549)
          ·
            refine ⟨54758001371382638440373081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146021336990353702507661549 54758001371382638440373081)
            ·
              refine ⟨41068501028536978830279811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54758001371382638440373081 41068501028536978830279811)
              ·
                refine ⟨61602751542805468245419717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41068501028536978830279811 61602751542805468245419717)
                ·
                  refine ⟨11550515914276025296016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61602751542805468245419717 11550515914276025296016197)
                  ·
                    refine ⟨2165721733926754743003037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11550515914276025296016197 2165721733926754743003037)
                    ·
                      refine ⟨812145650222533028626139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165721733926754743003037 812145650222533028626139)
                      ·
                        rfl

theorem cell23_1581648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_1581648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581648 prefixEnd_1581648 := by exact prefixLift 1581648
  have htrace : WordTrace (prefixWord ++ tailWord_1581648) baseStart_1581648 baseEnd_1581648 := by
    simpa [prefixWord, tailWord_1581648, baseEnd_1581648] using wordTrace_append hprefix tailTrace_1581648
  have hstable : (prefixWord ++ tailWord_1581648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581648).length < 2 ^ (prefixWord ++ tailWord_1581648).sum := by decide
  have hdescent : baseEnd_1581648 < baseStart_1581648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581649 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_1581649 : Nat := 118140960795 + 1581649 * 2 ^ 59
def prefixEnd_1581649 : Nat := 4983230072969 + 3 ^ 40 * 1581649 * 2
def baseEnd_1581649 : Nat := 812146163703187524713635

theorem tailTrace_1581649 : CollatzResearch.WordTrace tailWord_1581649 prefixEnd_1581649 812146163703187524713635 := by
  unfold tailWord_1581649
  simp only [CollatzResearch.WordTrace]
  refine ⟨57687478246963271988628001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38458318831308847992418667 57687478246963271988628001)
  ·
    refine ⟨43265608685222453991471001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57687478246963271988628001 43265608685222453991471001)
    ·
      refine ⟨32449206513916840493603251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43265608685222453991471001 32449206513916840493603251)
      ·
        refine ⟨48673809770875260740404877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32449206513916840493603251 48673809770875260740404877)
        ·
          refine ⟨18252678664078222777651829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48673809770875260740404877 18252678664078222777651829)
          ·
            refine ⟨1711188624757333385404859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18252678664078222777651829 1711188624757333385404859)
            ·
              refine ⟨2566782937136000078107289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711188624757333385404859 2566782937136000078107289)
              ·
                refine ⟨1925087202852000058580467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566782937136000078107289 1925087202852000058580467)
                ·
                  refine ⟨2887630804278000087870701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925087202852000058580467 2887630804278000087870701)
                  ·
                    refine ⟨1082861551604250032951513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2887630804278000087870701 1082861551604250032951513)
                    ·
                      refine ⟨812146163703187524713635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082861551604250032951513 812146163703187524713635)
                      ·
                        rfl

theorem cell23_1581649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_1581649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581649 prefixEnd_1581649 := by exact prefixLift 1581649
  have htrace : WordTrace (prefixWord ++ tailWord_1581649) baseStart_1581649 baseEnd_1581649 := by
    simpa [prefixWord, tailWord_1581649, baseEnd_1581649] using wordTrace_append hprefix tailTrace_1581649
  have hstable : (prefixWord ++ tailWord_1581649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581649).length < 2 ^ (prefixWord ++ tailWord_1581649).sum := by decide
  have hdescent : baseEnd_1581649 < baseStart_1581649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581658 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1581658 : Nat := 118140960795 + 1581658 * 2 ^ 59
def prefixEnd_1581658 : Nat := 4983230072969 + 3 ^ 40 * 1581658 * 2
def baseEnd_1581658 : Nat := 812150785029077989501093

theorem tailTrace_1581658 : CollatzResearch.WordTrace tailWord_1581658 prefixEnd_1581658 812150785029077989501093 := by
  unfold tailWord_1581658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421951625982666631426407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38458537669287111017137085 14421951625982666631426407)
  ·
    refine ⟨21632927438973999947139611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14421951625982666631426407 21632927438973999947139611)
    ·
      refine ⟨32449391158460999920709417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21632927438973999947139611 32449391158460999920709417)
      ·
        refine ⟨24337043368845749940532063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32449391158460999920709417 24337043368845749940532063)
        ·
          refine ⟨36505565053268624910798095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24337043368845749940532063 36505565053268624910798095)
          ·
            refine ⟨54758347579902937366197143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36505565053268624910798095 54758347579902937366197143)
            ·
              refine ⟨82137521369854406049295715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54758347579902937366197143 82137521369854406049295715)
              ·
                refine ⟨123206282054781609073943573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82137521369854406049295715 123206282054781609073943573)
                ·
                  refine ⟨5775294471317887925341105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123206282054781609073943573 5775294471317887925341105)
                  ·
                    refine ⟨4331470853488415944005829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775294471317887925341105 4331470853488415944005829)
                    ·
                      refine ⟨812150785029077989501093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4331470853488415944005829 812150785029077989501093)
                      ·
                        rfl

theorem cell23_1581658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1581658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581658 prefixEnd_1581658 := by exact prefixLift 1581658
  have htrace : WordTrace (prefixWord ++ tailWord_1581658) baseStart_1581658 baseEnd_1581658 := by
    simpa [prefixWord, tailWord_1581658, baseEnd_1581658] using wordTrace_append hprefix tailTrace_1581658
  have hstable : (prefixWord ++ tailWord_1581658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581658).length < 2 ^ (prefixWord ++ tailWord_1581658).sum := by decide
  have hdescent : baseEnd_1581658 < baseStart_1581658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581705 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 5, 2]
def baseStart_1581705 : Nat := 118140960795 + 1581705 * 2 ^ 59
def prefixEnd_1581705 : Nat := 4983230072969 + 3 ^ 40 * 1581705 * 2
def baseEnd_1581705 : Nat := 812174918619839305613377

theorem tailTrace_1581705 : CollatzResearch.WordTrace tailWord_1581705 prefixEnd_1581705 812174918619839305613377 := by
  unfold tailWord_1581705
  simp only [CollatzResearch.WordTrace]
  refine ⟨57689520734760393552666569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38459680489840262368444379 57689520734760393552666569)
  ·
    refine ⟨43267140551070295164499927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57689520734760393552666569 43267140551070295164499927)
    ·
      refine ⟨64900710826605442746749891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43267140551070295164499927 64900710826605442746749891)
      ·
        refine ⟨97351066239908164120124837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64900710826605442746749891 97351066239908164120124837)
        ·
          refine ⟨18253324919982780772523407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97351066239908164120124837 18253324919982780772523407)
          ·
            refine ⟨27379987379974171158785111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18253324919982780772523407 27379987379974171158785111)
            ·
              refine ⟨41069981069961256738177667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27379987379974171158785111 41069981069961256738177667)
              ·
                refine ⟨61604971604941885107266501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41069981069961256738177667 61604971604941885107266501)
                ·
                  refine ⟨11550932175926603457612469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61604971604941885107266501 11550932175926603457612469)
                  ·
                    refine ⟨1082899891493119074151169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11550932175926603457612469 1082899891493119074151169)
                    ·
                      refine ⟨812174918619839305613377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1082899891493119074151169 812174918619839305613377)
                      ·
                        rfl

theorem cell23_1581705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 5, 2].length) (baseStart_1581705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581705 prefixEnd_1581705 := by exact prefixLift 1581705
  have htrace : WordTrace (prefixWord ++ tailWord_1581705) baseStart_1581705 baseEnd_1581705 := by
    simpa [prefixWord, tailWord_1581705, baseEnd_1581705] using wordTrace_append hprefix tailTrace_1581705
  have hstable : (prefixWord ++ tailWord_1581705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581705).length < 2 ^ (prefixWord ++ tailWord_1581705).sum := by decide
  have hdescent : baseEnd_1581705 < baseStart_1581705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581708 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1581708 : Nat := 118140960795 + 1581708 * 2 ^ 59
def prefixEnd_1581708 : Nat := 4983230072969 + 3 ^ 40 * 1581708 * 2
def baseEnd_1581708 : Nat := 812176459061802793875863

theorem tailTrace_1581708 : CollatzResearch.WordTrace tailWord_1581708 prefixEnd_1581708 812176459061802793875863 := by
  unfold tailWord_1581708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844815076874762532512889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38459753435833016710017185 28844815076874762532512889)
  ·
    refine ⟨21633611307656071899384667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28844815076874762532512889 21633611307656071899384667)
    ·
      refine ⟨32450416961484107849077001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21633611307656071899384667 32450416961484107849077001)
      ·
        refine ⟨24337812721113080886807751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32450416961484107849077001 24337812721113080886807751)
        ·
          refine ⟨36506719081669621330211627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24337812721113080886807751 36506719081669621330211627)
          ·
            refine ⟨54760078622504431995317441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36506719081669621330211627 54760078622504431995317441)
            ·
              refine ⟨41070058966878323996488081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54760078622504431995317441 41070058966878323996488081)
              ·
                refine ⟨30802544225158742997366061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41070058966878323996488081 30802544225158742997366061)
                ·
                  refine ⟨11550954084434528624012273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30802544225158742997366061 11550954084434528624012273)
                  ·
                    refine ⟨8663215563325896468009205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11550954084434528624012273 8663215563325896468009205)
                    ·
                      refine ⟨812176459061802793875863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8663215563325896468009205 812176459061802793875863)
                      ·
                        rfl

theorem cell23_1581708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1581708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581708 prefixEnd_1581708 := by exact prefixLift 1581708
  have htrace : WordTrace (prefixWord ++ tailWord_1581708) baseStart_1581708 baseEnd_1581708 := by
    simpa [prefixWord, tailWord_1581708, baseEnd_1581708] using wordTrace_append hprefix tailTrace_1581708
  have hstable : (prefixWord ++ tailWord_1581708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581708).length < 2 ^ (prefixWord ++ tailWord_1581708).sum := by decide
  have hdescent : baseEnd_1581708 < baseStart_1581708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581772 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1581772 : Nat := 118140960795 + 1581772 * 2 ^ 59
def prefixEnd_1581772 : Nat := 4983230072969 + 3 ^ 40 * 1581772 * 2
def baseEnd_1581772 : Nat := 812209321823690543475569

theorem tailTrace_1581772 : CollatzResearch.WordTrace tailWord_1581772 prefixEnd_1581772 812209321823690543475569 := by
  unfold tailWord_1581772
  simp only [CollatzResearch.WordTrace]
  refine ⟨28845982212758831997677785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38461309617011775996903713 28845982212758831997677785)
  ·
    refine ⟨21634486659569123998258339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28845982212758831997677785 21634486659569123998258339)
    ·
      refine ⟨32451729989353685997387509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21634486659569123998258339 32451729989353685997387509)
      ·
        refine ⟨3042349686501908062255079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32451729989353685997387509 3042349686501908062255079)
        ·
          refine ⟨4563524529752862093382619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042349686501908062255079 4563524529752862093382619)
          ·
            refine ⟨6845286794629293140073929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563524529752862093382619 6845286794629293140073929)
            ·
              refine ⟨5133965095971969855055447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845286794629293140073929 5133965095971969855055447)
              ·
                refine ⟨7700947643957954782583171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133965095971969855055447 7700947643957954782583171)
                ·
                  refine ⟨11551421465936932173874757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700947643957954782583171 11551421465936932173874757)
                  ·
                    refine ⟨2165891524863174782601517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11551421465936932173874757 2165891524863174782601517)
                    ·
                      refine ⟨812209321823690543475569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2165891524863174782601517 812209321823690543475569)
                      ·
                        rfl

theorem cell23_1581772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1581772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581772 prefixEnd_1581772 := by exact prefixLift 1581772
  have htrace : WordTrace (prefixWord ++ tailWord_1581772) baseStart_1581772 baseEnd_1581772 := by
    simpa [prefixWord, tailWord_1581772, baseEnd_1581772] using wordTrace_append hprefix tailTrace_1581772
  have hstable : (prefixWord ++ tailWord_1581772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581772).length < 2 ^ (prefixWord ++ tailWord_1581772).sum := by decide
  have hdescent : baseEnd_1581772 < baseStart_1581772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581796 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1581796 : Nat := 118140960795 + 1581796 * 2 ^ 59
def prefixEnd_1581796 : Nat := 4983230072969 + 3 ^ 40 * 1581796 * 2
def baseEnd_1581796 : Nat := 270740548453132816525153

theorem tailTrace_1581796 : CollatzResearch.WordTrace tailWord_1581796 prefixEnd_1581796 270740548453132816525153 := by
  unfold tailWord_1581796
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846419888715358047114621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38461893184953810729486161 28846419888715358047114621)
  ·
    refine ⟨10817407458268259267667983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28846419888715358047114621 10817407458268259267667983)
    ·
      refine ⟨16226111187402388901501975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817407458268259267667983 16226111187402388901501975)
      ·
        refine ⟨24339166781103583352252963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226111187402388901501975 24339166781103583352252963)
        ·
          refine ⟨36508750171655375028379445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24339166781103583352252963 36508750171655375028379445)
          ·
            refine ⟨3422695328592691408910573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36508750171655375028379445 3422695328592691408910573)
            ·
              refine ⟨1283510748222259278341465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3422695328592691408910573 1283510748222259278341465)
              ·
                refine ⟨962633061166694458756099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283510748222259278341465 962633061166694458756099)
                ·
                  refine ⟨1443949591750041688134149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962633061166694458756099 1443949591750041688134149)
                  ·
                    refine ⟨270740548453132816525153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443949591750041688134149 270740548453132816525153)
                    ·
                      rfl

theorem cell23_1581796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1581796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581796 prefixEnd_1581796 := by exact prefixLift 1581796
  have htrace : WordTrace (prefixWord ++ tailWord_1581796) baseStart_1581796 baseEnd_1581796 := by
    simpa [prefixWord, tailWord_1581796, baseEnd_1581796] using wordTrace_append hprefix tailTrace_1581796
  have hstable : (prefixWord ++ tailWord_1581796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581796).length < 2 ^ (prefixWord ++ tailWord_1581796).sum := by decide
  have hdescent : baseEnd_1581796 < baseStart_1581796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581859 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 3, 2, 2]
def baseStart_1581859 : Nat := 118140960795 + 1581859 * 2 ^ 59
def prefixEnd_1581859 : Nat := 4983230072969 + 3 ^ 40 * 1581859 * 2
def baseEnd_1581859 : Nat := 812253994640631703087669

theorem tailTrace_1581859 : CollatzResearch.WordTrace tailWord_1581859 prefixEnd_1581859 812253994640631703087669 := by
  unfold tailWord_1581859
  simp only [CollatzResearch.WordTrace]
  refine ⟨57695137576202477853772631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38463425050801651902515087 57695137576202477853772631)
  ·
    refine ⟨86542706364303716780658947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57695137576202477853772631 86542706364303716780658947)
    ·
      refine ⟨129814059546455575170988421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86542706364303716780658947 129814059546455575170988421)
      ·
        refine ⟨24340136164960420344560329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129814059546455575170988421 24340136164960420344560329)
        ·
          refine ⟨18255102123720315258420247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24340136164960420344560329 18255102123720315258420247)
          ·
            refine ⟨27382653185580472887630371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18255102123720315258420247 27382653185580472887630371)
            ·
              refine ⟨41073979778370709331445557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27382653185580472887630371 41073979778370709331445557)
              ·
                refine ⟨3850685604222253999823021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41073979778370709331445557 3850685604222253999823021)
                ·
                  refine ⟨1444007101583345249933633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3850685604222253999823021 1444007101583345249933633)
                  ·
                    refine ⟨1083005326187508937450225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444007101583345249933633 1083005326187508937450225)
                    ·
                      refine ⟨812253994640631703087669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083005326187508937450225 812253994640631703087669)
                      ·
                        rfl

theorem cell23_1581859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_1581859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581859 prefixEnd_1581859 := by exact prefixLift 1581859
  have htrace : WordTrace (prefixWord ++ tailWord_1581859) baseStart_1581859 baseEnd_1581859 := by
    simpa [prefixWord, tailWord_1581859, baseEnd_1581859] using wordTrace_append hprefix tailTrace_1581859
  have hstable : (prefixWord ++ tailWord_1581859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581859).length < 2 ^ (prefixWord ++ tailWord_1581859).sum := by decide
  have hdescent : baseEnd_1581859 < baseStart_1581859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581909 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1581909 : Nat := 118140960795 + 1581909 * 2 ^ 59
def prefixEnd_1581909 : Nat := 4983230072969 + 3 ^ 40 * 1581909 * 2
def baseEnd_1581909 : Nat := 812279668673356507462439

theorem tailTrace_1581909 : CollatzResearch.WordTrace tailWord_1581909 prefixEnd_1581909 812279668673356507462439 := by
  unfold tailWord_1581909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57696961226021336393092781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38464640817347557595395187 57696961226021336393092781)
  ·
    refine ⟨21636360459758001147409793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57696961226021336393092781 21636360459758001147409793)
    ·
      refine ⟨16227270344818500860557345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21636360459758001147409793 16227270344818500860557345)
      ·
        refine ⟨12170452758613875645418009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16227270344818500860557345 12170452758613875645418009)
        ·
          refine ⟨9127839568960406734063507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12170452758613875645418009 9127839568960406734063507)
          ·
            refine ⟨13691759353440610101095261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9127839568960406734063507 13691759353440610101095261)
            ·
              refine ⟨5134409757540228787910723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13691759353440610101095261 5134409757540228787910723)
              ·
                refine ⟨7701614636310343181866085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134409757540228787910723 7701614636310343181866085)
                ·
                  refine ⟨1444052744308189346599891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7701614636310343181866085 1444052744308189346599891)
                  ·
                    refine ⟨2166079116462284019899837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444052744308189346599891 2166079116462284019899837)
                    ·
                      refine ⟨812279668673356507462439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2166079116462284019899837 812279668673356507462439)
                      ·
                        rfl

theorem cell23_1581909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1581909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581909 prefixEnd_1581909 := by exact prefixLift 1581909
  have htrace : WordTrace (prefixWord ++ tailWord_1581909) baseStart_1581909 baseEnd_1581909 := by
    simpa [prefixWord, tailWord_1581909, baseEnd_1581909] using wordTrace_append hprefix tailTrace_1581909
  have hstable : (prefixWord ++ tailWord_1581909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581909).length < 2 ^ (prefixWord ++ tailWord_1581909).sum := by decide
  have hdescent : baseEnd_1581909 < baseStart_1581909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581915 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_1581915 : Nat := 118140960795 + 1581915 * 2 ^ 59
def prefixEnd_1581915 : Nat := 4983230072969 + 3 ^ 40 * 1581915 * 2
def baseEnd_1581915 : Nat := 812282749557283483987411

theorem tailTrace_1581915 : CollatzResearch.WordTrace tailWord_1581915 prefixEnd_1581915 812282749557283483987411 := by
  unfold tailWord_1581915
  simp only [CollatzResearch.WordTrace]
  refine ⟨57697180063999599417811199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38464786709333066278540799 57697180063999599417811199)
  ·
    refine ⟨86545770095999399126716799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57697180063999599417811199 86545770095999399126716799)
    ·
      refine ⟨129818655143999098690075199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86545770095999399126716799 129818655143999098690075199)
      ·
        refine ⟨194727982715998648035112799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129818655143999098690075199 194727982715998648035112799)
        ·
          refine ⟨292091974073997972052669199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194727982715998648035112799 292091974073997972052669199)
          ·
            refine ⟨438137961110996958079003799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292091974073997972052669199 438137961110996958079003799)
            ·
              refine ⟨657206941666495437118505699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438137961110996958079003799 657206941666495437118505699)
              ·
                refine ⟨985810412499743155677758549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657206941666495437118505699 985810412499743155677758549)
                ·
                  refine ⟨11552465771481365105598733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 985810412499743155677758549 11552465771481365105598733)
                  ·
                    refine ⟨4332174664305511914599525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11552465771481365105598733 4332174664305511914599525)
                    ·
                      refine ⟨812282749557283483987411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4332174664305511914599525 812282749557283483987411)
                      ·
                        rfl

theorem cell23_1581915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_1581915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581915 prefixEnd_1581915 := by exact prefixLift 1581915
  have htrace : WordTrace (prefixWord ++ tailWord_1581915) baseStart_1581915 baseEnd_1581915 := by
    simpa [prefixWord, tailWord_1581915, baseEnd_1581915] using wordTrace_append hprefix tailTrace_1581915
  have hstable : (prefixWord ++ tailWord_1581915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581915).length < 2 ^ (prefixWord ++ tailWord_1581915).sum := by decide
  have hdescent : baseEnd_1581915 < baseStart_1581915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581935 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1581935 : Nat := 118140960795 + 1581935 * 2 ^ 59
def prefixEnd_1581935 : Nat := 4983230072969 + 3 ^ 40 * 1581935 * 2
def baseEnd_1581935 : Nat := 812293019170373405737319

theorem tailTrace_1581935 : CollatzResearch.WordTrace tailWord_1581935 prefixEnd_1581935 812293019170373405737319 := by
  unfold tailWord_1581935
  simp only [CollatzResearch.WordTrace]
  refine ⟨57697909523927142833539259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38465273015951428555692839 57697909523927142833539259)
  ·
    refine ⟨86546864285890714250308889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57697909523927142833539259 86546864285890714250308889)
    ·
      refine ⟨64910148214418035687731667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86546864285890714250308889 64910148214418035687731667)
      ·
        refine ⟨97365222321627053531597501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64910148214418035687731667 97365222321627053531597501)
        ·
          refine ⟨36511958370610145074349063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97365222321627053531597501 36511958370610145074349063)
          ·
            refine ⟨54767937555915217611523595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36511958370610145074349063 54767937555915217611523595)
            ·
              refine ⟨82151906333872826417285393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54767937555915217611523595 82151906333872826417285393)
              ·
                refine ⟨61613929750404619812964045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82151906333872826417285393 61613929750404619812964045)
                ·
                  refine ⟨23105223656401732429861517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61613929750404619812964045 23105223656401732429861517)
                  ·
                    refine ⟨8664458871150649661198069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23105223656401732429861517 8664458871150649661198069)
                    ·
                      refine ⟨812293019170373405737319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8664458871150649661198069 812293019170373405737319)
                      ·
                        rfl

theorem cell23_1581935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1581935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581935 prefixEnd_1581935 := by exact prefixLift 1581935
  have htrace : WordTrace (prefixWord ++ tailWord_1581935) baseStart_1581935 baseEnd_1581935 := by
    simpa [prefixWord, tailWord_1581935, baseEnd_1581935] using wordTrace_append hprefix tailTrace_1581935
  have hstable : (prefixWord ++ tailWord_1581935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581935).length < 2 ^ (prefixWord ++ tailWord_1581935).sum := by decide
  have hdescent : baseEnd_1581935 < baseStart_1581935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581949 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_1581949 : Nat := 118140960795 + 1581949 * 2 ^ 59
def prefixEnd_1581949 : Nat := 4983230072969 + 3 ^ 40 * 1581949 * 2
def baseEnd_1581949 : Nat := 812300207899536350962255

theorem tailTrace_1581949 : CollatzResearch.WordTrace tailWord_1581949 prefixEnd_1581949 812300207899536350962255 := by
  unfold tailWord_1581949
  simp only [CollatzResearch.WordTrace]
  refine ⟨57698420145876423224548901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38465613430584282149699267 57698420145876423224548901)
  ·
    refine ⟨10818453777351829354602919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57698420145876423224548901 10818453777351829354602919)
    ·
      refine ⟨16227680666027744031904379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818453777351829354602919 16227680666027744031904379)
      ·
        refine ⟨24341520999041616047856569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16227680666027744031904379 24341520999041616047856569)
        ·
          refine ⟨18256140749281212035892427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24341520999041616047856569 18256140749281212035892427)
          ·
            refine ⟨27384211123921818053838641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18256140749281212035892427 27384211123921818053838641)
            ·
              refine ⟨20538158342941363540378981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27384211123921818053838641 20538158342941363540378981)
              ·
                refine ⟨3850904689301505663821059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20538158342941363540378981 3850904689301505663821059)
                ·
                  refine ⟨5776357033952258495731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850904689301505663821059 5776357033952258495731589)
                  ·
                    refine ⟨1083066943866048467949673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776357033952258495731589 1083066943866048467949673)
                    ·
                      refine ⟨812300207899536350962255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083066943866048467949673 812300207899536350962255)
                      ·
                        rfl

theorem cell23_1581949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_1581949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581949 prefixEnd_1581949 := by exact prefixLift 1581949
  have htrace : WordTrace (prefixWord ++ tailWord_1581949) baseStart_1581949 baseEnd_1581949 := by
    simpa [prefixWord, tailWord_1581949, baseEnd_1581949] using wordTrace_append hprefix tailTrace_1581949
  have hstable : (prefixWord ++ tailWord_1581949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581949).length < 2 ^ (prefixWord ++ tailWord_1581949).sum := by decide
  have hdescent : baseEnd_1581949 < baseStart_1581949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581983 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1581983 : Nat := 118140960795 + 1581983 * 2 ^ 59
def prefixEnd_1581983 : Nat := 4983230072969 + 3 ^ 40 * 1581983 * 2
def baseEnd_1581983 : Nat := 812317666241789217937099

theorem tailTrace_1581983 : CollatzResearch.WordTrace tailWord_1581983 prefixEnd_1581983 812317666241789217937099 := by
  unfold tailWord_1581983
  simp only [CollatzResearch.WordTrace]
  refine ⟨57699660227753247031286603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38466440151835498020857735 57699660227753247031286603)
  ·
    refine ⟨86549490341629870546929905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57699660227753247031286603 86549490341629870546929905)
    ·
      refine ⟨64912117756222402910197429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86549490341629870546929905 64912117756222402910197429)
      ·
        refine ⟨6085511039645850272831009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64912117756222402910197429 6085511039645850272831009)
        ·
          refine ⟨4564133279734387704623257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6085511039645850272831009 4564133279734387704623257)
          ·
            refine ⟨3423099959800790778467443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4564133279734387704623257 3423099959800790778467443)
            ·
              refine ⟨5134649939701186167701165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423099959800790778467443 5134649939701186167701165)
              ·
                refine ⟨1925493727387944812887937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5134649939701186167701165 1925493727387944812887937)
                ·
                  refine ⟨1444120295540958609665953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925493727387944812887937 1444120295540958609665953)
                  ·
                    refine ⟨1083090221655718957249465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444120295540958609665953 1083090221655718957249465)
                    ·
                      refine ⟨812317666241789217937099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083090221655718957249465 812317666241789217937099)
                      ·
                        rfl

theorem cell23_1581983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1581983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1581983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1581983 prefixEnd_1581983 := by exact prefixLift 1581983
  have htrace : WordTrace (prefixWord ++ tailWord_1581983) baseStart_1581983 baseEnd_1581983 := by
    simpa [prefixWord, tailWord_1581983, baseEnd_1581983] using wordTrace_append hprefix tailTrace_1581983
  have hstable : (prefixWord ++ tailWord_1581983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581983).length < 2 ^ (prefixWord ++ tailWord_1581983).sum := by decide
  have hdescent : baseEnd_1581983 < baseStart_1581983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582052 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_1582052 : Nat := 118140960795 + 1582052 * 2 ^ 59
def prefixEnd_1582052 : Nat := 4983230072969 + 3 ^ 40 * 1582052 * 2
def baseEnd_1582052 : Nat := 812353096406949447974281

theorem tailTrace_1582052 : CollatzResearch.WordTrace tailWord_1582052 prefixEnd_1582052 812353096406949447974281 := by
  unfold tailWord_1582052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28851088432251635907774205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38468117909668847877032273 28851088432251635907774205)
  ·
    refine ⟨10819158162094363465415327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28851088432251635907774205 10819158162094363465415327)
    ·
      refine ⟨16228737243141545198122991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10819158162094363465415327 16228737243141545198122991)
      ·
        refine ⟨24343105864712317797184487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16228737243141545198122991 24343105864712317797184487)
        ·
          refine ⟨36514658797068476695776731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24343105864712317797184487 36514658797068476695776731)
          ·
            refine ⟨54771988195602715043665097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36514658797068476695776731 54771988195602715043665097)
            ·
              refine ⟨41078991146702036282748823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54771988195602715043665097 41078991146702036282748823)
              ·
                refine ⟨61618486720053054424123235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41078991146702036282748823 61618486720053054424123235)
                ·
                  refine ⟨92427730080079581636184853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61618486720053054424123235 92427730080079581636184853)
                  ·
                    refine ⟨4332549847503730389196165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92427730080079581636184853 4332549847503730389196165)
                    ·
                      refine ⟨812353096406949447974281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4332549847503730389196165 812353096406949447974281)
                      ·
                        rfl

theorem cell23_1582052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_1582052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582052 prefixEnd_1582052 := by exact prefixLift 1582052
  have htrace : WordTrace (prefixWord ++ tailWord_1582052) baseStart_1582052 baseEnd_1582052 := by
    simpa [prefixWord, tailWord_1582052, baseEnd_1582052] using wordTrace_append hprefix tailTrace_1582052
  have hstable : (prefixWord ++ tailWord_1582052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582052).length < 2 ^ (prefixWord ++ tailWord_1582052).sum := by decide
  have hdescent : baseEnd_1582052 < baseStart_1582052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582053 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_1582053 : Nat := 118140960795 + 1582053 * 2 ^ 59
def prefixEnd_1582053 : Nat := 4983230072969 + 3 ^ 40 * 1582053 * 2
def baseEnd_1582053 : Nat := 270784536629201314687259

theorem tailTrace_1582053 : CollatzResearch.WordTrace tailWord_1582053 prefixEnd_1582053 270784536629201314687259 := by
  unfold tailWord_1582053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57702213337499648986334813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38468142224999765990889875 57702213337499648986334813)
  ·
    refine ⟨21638330001562368369875555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57702213337499648986334813 21638330001562368369875555)
    ·
      refine ⟨32457495002343552554813333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21638330001562368369875555 32457495002343552554813333)
      ·
        refine ⟨1521445078234854026006875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32457495002343552554813333 1521445078234854026006875)
        ·
          refine ⟨2282167617352281039010313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521445078234854026006875 2282167617352281039010313)
          ·
            refine ⟨1711625713014210779257735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282167617352281039010313 1711625713014210779257735)
            ·
              refine ⟨2567438569521316168886603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711625713014210779257735 2567438569521316168886603)
              ·
                refine ⟨3851157854281974253329905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567438569521316168886603 3851157854281974253329905)
                ·
                  refine ⟨2888368390711480689997429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3851157854281974253329905 2888368390711480689997429)
                  ·
                    refine ⟨270784536629201314687259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2888368390711480689997429 270784536629201314687259)
                    ·
                      rfl

theorem cell23_1582053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_1582053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582053 prefixEnd_1582053 := by exact prefixLift 1582053
  have htrace : WordTrace (prefixWord ++ tailWord_1582053) baseStart_1582053 baseEnd_1582053 := by
    simpa [prefixWord, tailWord_1582053, baseEnd_1582053] using wordTrace_append hprefix tailTrace_1582053
  have hstable : (prefixWord ++ tailWord_1582053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582053).length < 2 ^ (prefixWord ++ tailWord_1582053).sum := by decide
  have hdescent : baseEnd_1582053 < baseStart_1582053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582068 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1582068 : Nat := 118140960795 + 1582068 * 2 ^ 59
def prefixEnd_1582068 : Nat := 4983230072969 + 3 ^ 40 * 1582068 * 2
def baseEnd_1582068 : Nat := 812361312097421385374209

theorem tailTrace_1582068 : CollatzResearch.WordTrace tailWord_1582068 prefixEnd_1582068 812361312097421385374209 := by
  unfold tailWord_1582068
  simp only [CollatzResearch.WordTrace]
  refine ⟨28851380216222653274065429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38468506954963537698753905 28851380216222653274065429)
  ·
    refine ⟨1352408447635436872221817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28851380216222653274065429 1352408447635436872221817)
    ·
      refine ⟨1014306335726577654166363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352408447635436872221817 1014306335726577654166363)
      ·
        refine ⟨1521459503589866481249545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014306335726577654166363 1521459503589866481249545)
        ·
          refine ⟨1141094627692399860937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521459503589866481249545 1141094627692399860937159)
          ·
            refine ⟨1711641941538599791405739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141094627692399860937159 1711641941538599791405739)
            ·
              refine ⟨2567462912307899687108609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711641941538599791405739 2567462912307899687108609)
              ·
                refine ⟨1925597184230924765331457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567462912307899687108609 1925597184230924765331457)
                ·
                  refine ⟨1444197888173193573998593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925597184230924765331457 1444197888173193573998593)
                  ·
                    refine ⟨1083148416129895180498945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444197888173193573998593 1083148416129895180498945)
                    ·
                      refine ⟨812361312097421385374209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083148416129895180498945 812361312097421385374209)
                      ·
                        rfl

theorem cell23_1582068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1582068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582068 prefixEnd_1582068 := by exact prefixLift 1582068
  have htrace : WordTrace (prefixWord ++ tailWord_1582068) baseStart_1582068 baseEnd_1582068 := by
    simpa [prefixWord, tailWord_1582068, baseEnd_1582068] using wordTrace_append hprefix tailTrace_1582068
  have hstable : (prefixWord ++ tailWord_1582068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582068).length < 2 ^ (prefixWord ++ tailWord_1582068).sum := by decide
  have hdescent : baseEnd_1582068 < baseStart_1582068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582106 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1582106 : Nat := 118140960795 + 1582106 * 2 ^ 59
def prefixEnd_1582106 : Nat := 4983230072969 + 3 ^ 40 * 1582106 * 2
def baseEnd_1582106 : Nat := 812380824362292236699033

theorem tailTrace_1582106 : CollatzResearch.WordTrace tailWord_1582106 prefixEnd_1582106 812380824362292236699033 := by
  unfold tailWord_1582106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426036601576909759503543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38469430937538426025342781 14426036601576909759503543)
  ·
    refine ⟨21639054902365364639255315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426036601576909759503543 21639054902365364639255315)
    ·
      refine ⟨32458582353548046958882973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21639054902365364639255315 32458582353548046958882973)
      ·
        refine ⟨12171968382580517609581115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32458582353548046958882973 12171968382580517609581115)
        ·
          refine ⟨18257952573870776414371673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171968382580517609581115 18257952573870776414371673)
          ·
            refine ⟨13693464430403082310778755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18257952573870776414371673 13693464430403082310778755)
            ·
              refine ⟨20540196645604623466168133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13693464430403082310778755 20540196645604623466168133)
              ·
                refine ⟨3851286871050866899906525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20540196645604623466168133 3851286871050866899906525)
                ·
                  refine ⟨1444232576644075087464947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3851286871050866899906525 1444232576644075087464947)
                  ·
                    refine ⟨2166348864966112631197421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444232576644075087464947 2166348864966112631197421)
                    ·
                      refine ⟨812380824362292236699033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2166348864966112631197421 812380824362292236699033)
                      ·
                        rfl

theorem cell23_1582106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1582106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582106 prefixEnd_1582106 := by exact prefixLift 1582106
  have htrace : WordTrace (prefixWord ++ tailWord_1582106) baseStart_1582106 baseEnd_1582106 := by
    simpa [prefixWord, tailWord_1582106, baseEnd_1582106] using wordTrace_append hprefix tailTrace_1582106
  have hstable : (prefixWord ++ tailWord_1582106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582106).length < 2 ^ (prefixWord ++ tailWord_1582106).sum := by decide
  have hdescent : baseEnd_1582106 < baseStart_1582106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582126 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1582126 : Nat := 118140960795 + 1582126 * 2 ^ 59
def prefixEnd_1582126 : Nat := 4983230072969 + 3 ^ 40 * 1582126 * 2
def baseEnd_1582126 : Nat := 270797031325127386149647

theorem tailTrace_1582126 : CollatzResearch.WordTrace tailWord_1582126 prefixEnd_1582126 270797031325127386149647 := by
  unfold tailWord_1582126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213109483279397806717779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38469917244156788302494821 7213109483279397806717779)
  ·
    refine ⟨10819664224919096710076669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7213109483279397806717779 10819664224919096710076669)
    ·
      refine ⟨4057374084344661266278751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10819664224919096710076669 4057374084344661266278751)
      ·
        refine ⟨6086061126516991899418127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057374084344661266278751 6086061126516991899418127)
        ·
          refine ⟨9129091689775487849127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086061126516991899418127 9129091689775487849127191)
          ·
            refine ⟨13693637534663231773690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9129091689775487849127191 13693637534663231773690787)
            ·
              refine ⟨20540456301994847660536181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13693637534663231773690787 20540456301994847660536181)
              ·
                refine ⟨1925667778312016968175267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20540456301994847660536181 1925667778312016968175267)
                ·
                  refine ⟨2888501667468025452262901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925667778312016968175267 2888501667468025452262901)
                  ·
                    refine ⟨270797031325127386149647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2888501667468025452262901 270797031325127386149647)
                    ·
                      rfl

theorem cell23_1582126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1582126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582126 prefixEnd_1582126 := by exact prefixLift 1582126
  have htrace : WordTrace (prefixWord ++ tailWord_1582126) baseStart_1582126 baseEnd_1582126 := by
    simpa [prefixWord, tailWord_1582126, baseEnd_1582126] using wordTrace_append hprefix tailTrace_1582126
  have hstable : (prefixWord ++ tailWord_1582126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582126).length < 2 ^ (prefixWord ++ tailWord_1582126).sum := by decide
  have hdescent : baseEnd_1582126 < baseStart_1582126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582149 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_1582149 : Nat := 118140960795 + 1582149 * 2 ^ 59
def prefixEnd_1582149 : Nat := 4983230072969 + 3 ^ 40 * 1582149 * 2
def baseEnd_1582149 : Nat := 812402904030435568461335

theorem tailTrace_1582149 : CollatzResearch.WordTrace tailWord_1582149 prefixEnd_1582149 812402904030435568461335 := by
  unfold tailWord_1582149
  simp only [CollatzResearch.WordTrace]
  refine ⟨57705714745151857381829501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38470476496767904921219667 57705714745151857381829501)
  ·
    refine ⟨21639643029431946518186063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57705714745151857381829501 21639643029431946518186063)
    ·
      refine ⟨32459464544147919777279095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21639643029431946518186063 32459464544147919777279095)
      ·
        refine ⟨48689196816221879665918643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32459464544147919777279095 48689196816221879665918643)
        ·
          refine ⟨73033795224332819498877965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48689196816221879665918643 73033795224332819498877965)
          ·
            refine ⟨27387673209124807312079237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73033795224332819498877965 27387673209124807312079237)
            ·
              refine ⟨5135188726710901371014857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27387673209124807312079237 5135188726710901371014857)
              ·
                refine ⟨3851391545033176028261143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135188726710901371014857 3851391545033176028261143)
                ·
                  refine ⟨5777087317549764042391715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851391545033176028261143 5777087317549764042391715)
                  ·
                    refine ⟨8665630976324646063587573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5777087317549764042391715 8665630976324646063587573)
                    ·
                      refine ⟨812402904030435568461335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8665630976324646063587573 812402904030435568461335)
                      ·
                        rfl

theorem cell23_1582149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_1582149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582149 prefixEnd_1582149 := by exact prefixLift 1582149
  have htrace : WordTrace (prefixWord ++ tailWord_1582149) baseStart_1582149 baseEnd_1582149 := by
    simpa [prefixWord, tailWord_1582149, baseEnd_1582149] using wordTrace_append hprefix tailTrace_1582149
  have hstable : (prefixWord ++ tailWord_1582149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582149).length < 2 ^ (prefixWord ++ tailWord_1582149).sum := by decide
  have hdescent : baseEnd_1582149 < baseStart_1582149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582173 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1582173 : Nat := 118140960795 + 1582173 * 2 ^ 59
def prefixEnd_1582173 : Nat := 4983230072969 + 3 ^ 40 * 1582173 * 2
def baseEnd_1582173 : Nat := 270805075855381158187075

theorem tailTrace_1582173 : CollatzResearch.WordTrace tailWord_1582173 prefixEnd_1582173 270805075855381158187075 := by
  unfold tailWord_1582173
  simp only [CollatzResearch.WordTrace]
  refine ⟨57706590097064909480703173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38471060064709939653802115 57706590097064909480703173)
  ·
    refine ⟨10819985643199670527631845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57706590097064909480703173 10819985643199670527631845)
    ·
      refine ⟨2028747308099938223930971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10819985643199670527631845 2028747308099938223930971)
      ·
        refine ⟨3043120962149907335896457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028747308099938223930971 3043120962149907335896457)
        ·
          refine ⟨2282340721612430501922343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043120962149907335896457 2282340721612430501922343)
          ·
            refine ⟨3423511082418645752883515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282340721612430501922343 3423511082418645752883515)
            ·
              refine ⟨5135266623627968629325273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423511082418645752883515 5135266623627968629325273)
              ·
                refine ⟨3851449967720976471993955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135266623627968629325273 3851449967720976471993955)
                ·
                  refine ⟨5777174951581464707990933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851449967720976471993955 5777174951581464707990933)
                  ·
                    refine ⟨270805075855381158187075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5777174951581464707990933 270805075855381158187075)
                    ·
                      rfl

theorem cell23_1582173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1582173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582173 prefixEnd_1582173 := by exact prefixLift 1582173
  have htrace : WordTrace (prefixWord ++ tailWord_1582173) baseStart_1582173 baseEnd_1582173 := by
    simpa [prefixWord, tailWord_1582173, baseEnd_1582173] using wordTrace_append hprefix tailTrace_1582173
  have hstable : (prefixWord ++ tailWord_1582173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582173).length < 2 ^ (prefixWord ++ tailWord_1582173).sum := by decide
  have hdescent : baseEnd_1582173 < baseStart_1582173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582180 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_1582180 : Nat := 118140960795 + 1582180 * 2 ^ 59
def prefixEnd_1582180 : Nat := 4983230072969 + 3 ^ 40 * 1582180 * 2
def baseEnd_1582180 : Nat := 812418821930724947173693

theorem tailTrace_1582180 : CollatzResearch.WordTrace tailWord_1582180 prefixEnd_1582180 812418821930724947173693 := by
  unfold tailWord_1582180
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853422704019774838103997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38471230272026366450805329 28853422704019774838103997)
  ·
    refine ⟨10820033514007415564288999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28853422704019774838103997 10820033514007415564288999)
    ·
      refine ⟨16230050271011123346433499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820033514007415564288999 16230050271011123346433499)
      ·
        refine ⟨24345075406516685019650249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16230050271011123346433499 24345075406516685019650249)
        ·
          refine ⟨18258806554887513764737687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24345075406516685019650249 18258806554887513764737687)
          ·
            refine ⟨27388209832331270647106531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18258806554887513764737687 27388209832331270647106531)
            ·
              refine ⟨41082314748496905970659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27388209832331270647106531 41082314748496905970659797)
              ·
                refine ⟨962866751917896233687339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41082314748496905970659797 962866751917896233687339)
                ·
                  refine ⟨1444300127876844350531009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962866751917896233687339 1444300127876844350531009)
                  ·
                    refine ⟨1083225095907633262898257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444300127876844350531009 1083225095907633262898257)
                    ·
                      refine ⟨812418821930724947173693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083225095907633262898257 812418821930724947173693)
                      ·
                        rfl

theorem cell23_1582180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_1582180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582180 prefixEnd_1582180 := by exact prefixLift 1582180
  have htrace : WordTrace (prefixWord ++ tailWord_1582180) baseStart_1582180 baseEnd_1582180 := by
    simpa [prefixWord, tailWord_1582180, baseEnd_1582180] using wordTrace_append hprefix tailTrace_1582180
  have hstable : (prefixWord ++ tailWord_1582180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582180).length < 2 ^ (prefixWord ++ tailWord_1582180).sum := by decide
  have hdescent : baseEnd_1582180 < baseStart_1582180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582213 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_1582213 : Nat := 118140960795 + 1582213 * 2 ^ 59
def prefixEnd_1582213 : Nat := 4983230072969 + 3 ^ 40 * 1582213 * 2
def baseEnd_1582213 : Nat := 812435766792323318061041

theorem tailTrace_1582213 : CollatzResearch.WordTrace tailWord_1582213 prefixEnd_1582213 812435766792323318061041 := by
  unfold tailWord_1582213
  simp only [CollatzResearch.WordTrace]
  refine ⟨57708049016919996312159293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38472032677946664208106195 57708049016919996312159293)
  ·
    refine ⟨21640518381344998617059735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57708049016919996312159293 21640518381344998617059735)
    ·
      refine ⟨32460777572017497925589603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640518381344998617059735 32460777572017497925589603)
      ·
        refine ⟨48691166358026246888384405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32460777572017497925589603 48691166358026246888384405)
        ·
          refine ⟨2282398423032480322893019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48691166358026246888384405 2282398423032480322893019)
          ·
            refine ⟨3423597634548720484339529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282398423032480322893019 3423597634548720484339529)
            ·
              refine ⟨2567698225911540363254647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423597634548720484339529 2567698225911540363254647)
              ·
                refine ⟨3851547338867310544881971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567698225911540363254647 3851547338867310544881971)
                ·
                  refine ⟨5777321008300965817322957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851547338867310544881971 5777321008300965817322957)
                  ·
                    refine ⟨2166495378112862181496109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5777321008300965817322957 2166495378112862181496109)
                    ·
                      refine ⟨812435766792323318061041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2166495378112862181496109 812435766792323318061041)
                      ·
                        rfl

theorem cell23_1582213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_1582213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582213 prefixEnd_1582213 := by exact prefixLift 1582213
  have htrace : WordTrace (prefixWord ++ tailWord_1582213) baseStart_1582213 baseEnd_1582213 := by
    simpa [prefixWord, tailWord_1582213, baseEnd_1582213] using wordTrace_append hprefix tailTrace_1582213
  have hstable : (prefixWord ++ tailWord_1582213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582213).length < 2 ^ (prefixWord ++ tailWord_1582213).sum := by decide
  have hdescent : baseEnd_1582213 < baseStart_1582213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582247 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1582247 : Nat := 118140960795 + 1582247 * 2 ^ 59
def prefixEnd_1582247 : Nat := 4983230072969 + 3 ^ 40 * 1582247 * 2
def baseEnd_1582247 : Nat := 812453225134576185035885

theorem tailTrace_1582247 : CollatzResearch.WordTrace tailWord_1582247 prefixEnd_1582247 812453225134576185035885 := by
  unfold tailWord_1582247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57709289098796820118896995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38472859399197880079264663 57709289098796820118896995)
  ·
    refine ⟨86563933648195230178345493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57709289098796820118896995 86563933648195230178345493)
    ·
      refine ⟨4057684389759151414609945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86563933648195230178345493 4057684389759151414609945)
      ·
        refine ⟨3043263292319363560957459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057684389759151414609945 3043263292319363560957459)
        ·
          refine ⟨4564894938479045341436189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043263292319363560957459 4564894938479045341436189)
          ·
            refine ⟨1711835601929642003038571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4564894938479045341436189 1711835601929642003038571)
            ·
              refine ⟨2567753402894463004557857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711835601929642003038571 2567753402894463004557857)
              ·
                refine ⟨1925815052170847253418393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567753402894463004557857 1925815052170847253418393)
                ·
                  refine ⟨1444361289128135440063795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925815052170847253418393 1444361289128135440063795)
                  ·
                    refine ⟨2166541933692203160095693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444361289128135440063795 2166541933692203160095693)
                    ·
                      refine ⟨812453225134576185035885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2166541933692203160095693 812453225134576185035885)
                      ·
                        rfl

theorem cell23_1582247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1582247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582247 prefixEnd_1582247 := by exact prefixLift 1582247
  have htrace : WordTrace (prefixWord ++ tailWord_1582247) baseStart_1582247 baseEnd_1582247 := by
    simpa [prefixWord, tailWord_1582247, baseEnd_1582247] using wordTrace_append hprefix tailTrace_1582247
  have hstable : (prefixWord ++ tailWord_1582247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582247).length < 2 ^ (prefixWord ++ tailWord_1582247).sum := by decide
  have hdescent : baseEnd_1582247 < baseStart_1582247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582259 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 7]
def baseStart_1582259 : Nat := 118140960795 + 1582259 * 2 ^ 59
def prefixEnd_1582259 : Nat := 4983230072969 + 3 ^ 40 * 1582259 * 2
def baseEnd_1582259 : Nat := 90273265211381126453981

theorem tailTrace_1582259 : CollatzResearch.WordTrace tailWord_1582259 prefixEnd_1582259 90273265211381126453981 := by
  unfold tailWord_1582259
  simp only [CollatzResearch.WordTrace]
  refine ⟨57709726774753346168333831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38473151183168897445555887 57709726774753346168333831)
  ·
    refine ⟨86564590162130019252500747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57709726774753346168333831 86564590162130019252500747)
    ·
      refine ⟨129846885243195028878751121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86564590162130019252500747 129846885243195028878751121)
      ·
        refine ⟨97385163932396271659063341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129846885243195028878751121 97385163932396271659063341)
        ·
          refine ⟨36519436474648601872148753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97385163932396271659063341 36519436474648601872148753)
          ·
            refine ⟨27389577355986451404111565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36519436474648601872148753 27389577355986451404111565)
            ·
              refine ⟨10271091508494919276541837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27389577355986451404111565 10271091508494919276541837)
              ·
                refine ⟨3851659315685594728703189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10271091508494919276541837 3851659315685594728703189)
                ·
                  refine ⟨90273265211381126453981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3851659315685594728703189 90273265211381126453981)
                  ·
                    rfl

theorem cell23_1582259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 7].length) (baseStart_1582259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582259 prefixEnd_1582259 := by exact prefixLift 1582259
  have htrace : WordTrace (prefixWord ++ tailWord_1582259) baseStart_1582259 baseEnd_1582259 := by
    simpa [prefixWord, tailWord_1582259, baseEnd_1582259] using wordTrace_append hprefix tailTrace_1582259
  have hstable : (prefixWord ++ tailWord_1582259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582259).length < 2 ^ (prefixWord ++ tailWord_1582259).sum := by decide
  have hdescent : baseEnd_1582259 < baseStart_1582259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582270 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_1582270 : Nat := 118140960795 + 1582270 * 2 ^ 59
def prefixEnd_1582270 : Nat := 4983230072969 + 3 ^ 40 * 1582270 * 2
def baseEnd_1582270 : Nat := 812465035189629595048279

theorem tailTrace_1582270 : CollatzResearch.WordTrace tailWord_1582270 prefixEnd_1582270 812465035189629595048279 := by
  unfold tailWord_1582270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213765997214186880873033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38473418651808996697989509 7213765997214186880873033)
  ·
    refine ⟨5410324497910640160654775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7213765997214186880873033 5410324497910640160654775)
    ·
      refine ⟨8115486746865960240982163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410324497910640160654775 8115486746865960240982163)
      ·
        refine ⟨12173230120298940361473245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115486746865960240982163 12173230120298940361473245)
        ·
          refine ⟨4564961295112102635552467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12173230120298940361473245 4564961295112102635552467)
          ·
            refine ⟨6847441942668153953328701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564961295112102635552467 6847441942668153953328701)
            ·
              refine ⟨2567790728500557732498263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847441942668153953328701 2567790728500557732498263)
              ·
                refine ⟨3851686092750836598747395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567790728500557732498263 3851686092750836598747395)
                ·
                  refine ⟨5777529139126254898121093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851686092750836598747395 5777529139126254898121093)
                  ·
                    refine ⟨1083286713586172793397705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5777529139126254898121093 1083286713586172793397705)
                    ·
                      refine ⟨812465035189629595048279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083286713586172793397705 812465035189629595048279)
                      ·
                        rfl

theorem cell23_1582270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_1582270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582270 prefixEnd_1582270 := by exact prefixLift 1582270
  have htrace : WordTrace (prefixWord ++ tailWord_1582270) baseStart_1582270 baseEnd_1582270 := by
    simpa [prefixWord, tailWord_1582270, baseEnd_1582270] using wordTrace_append hprefix tailTrace_1582270
  have hstable : (prefixWord ++ tailWord_1582270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582270).length < 2 ^ (prefixWord ++ tailWord_1582270).sum := by decide
  have hdescent : baseEnd_1582270 < baseStart_1582270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582316 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1582316 : Nat := 118140960795 + 1582316 * 2 ^ 59
def prefixEnd_1582316 : Nat := 4983230072969 + 3 ^ 40 * 1582316 * 2
def baseEnd_1582316 : Nat := 812488655299736415073067

theorem tailTrace_1582316 : CollatzResearch.WordTrace tailWord_1582316 prefixEnd_1582316 812488655299736415073067 := by
  unfold tailWord_1582316
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855902867773422451579401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38474537157031229935439201 28855902867773422451579401)
  ·
    refine ⟨21641927150830066838684551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28855902867773422451579401 21641927150830066838684551)
    ·
      refine ⟨32462890726245100258026827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641927150830066838684551 32462890726245100258026827)
      ·
        refine ⟨48694336089367650387040241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32462890726245100258026827 48694336089367650387040241)
        ·
          refine ⟨36520752067025737790280181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48694336089367650387040241 36520752067025737790280181)
          ·
            refine ⟨3423820506283662917838767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36520752067025737790280181 3423820506283662917838767)
            ·
              refine ⟨5135730759425494376758151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423820506283662917838767 5135730759425494376758151)
              ·
                refine ⟨7703596139138241565137227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135730759425494376758151 7703596139138241565137227)
                ·
                  refine ⟨11555394208707362347705841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7703596139138241565137227 11555394208707362347705841)
                  ·
                    refine ⟨8666545656530521760779381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11555394208707362347705841 8666545656530521760779381)
                    ·
                      refine ⟨812488655299736415073067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8666545656530521760779381 812488655299736415073067)
                      ·
                        rfl

theorem cell23_1582316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1582316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582316 prefixEnd_1582316 := by exact prefixLift 1582316
  have htrace : WordTrace (prefixWord ++ tailWord_1582316) baseStart_1582316 baseEnd_1582316 := by
    simpa [prefixWord, tailWord_1582316, baseEnd_1582316] using wordTrace_append hprefix tailTrace_1582316
  have hstable : (prefixWord ++ tailWord_1582316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582316).length < 2 ^ (prefixWord ++ tailWord_1582316).sum := by decide
  have hdescent : baseEnd_1582316 < baseStart_1582316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582336 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_1582336 : Nat := 118140960795 + 1582336 * 2 ^ 59
def prefixEnd_1582336 : Nat := 4983230072969 + 3 ^ 40 * 1582336 * 2
def baseEnd_1582336 : Nat := 270832974970942112274325

theorem tailTrace_1582336 : CollatzResearch.WordTrace tailWord_1582336 prefixEnd_1582336 270832974970942112274325 := by
  unfold tailWord_1582336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28856267597737194159443431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38475023463649592212591241 28856267597737194159443431)
  ·
    refine ⟨43284401396605791239165147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28856267597737194159443431 43284401396605791239165147)
    ·
      refine ⟨64926602094908686858747721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43284401396605791239165147 64926602094908686858747721)
      ·
        refine ⟨48694951571181515144060791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64926602094908686858747721 48694951571181515144060791)
        ·
          refine ⟨73042427356772272716091187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48694951571181515144060791 73042427356772272716091187)
          ·
            refine ⟨109563641035158409074136781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73042427356772272716091187 109563641035158409074136781)
            ·
              refine ⟨41086365388184403402801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109563641035158409074136781 41086365388184403402801293)
              ·
                refine ⟨15407387020569151276050485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41086365388184403402801293 15407387020569151276050485)
                ·
                  refine ⟨1444442533178357932129733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15407387020569151276050485 1444442533178357932129733)
                  ·
                    refine ⟨270832974970942112274325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444442533178357932129733 270832974970942112274325)
                    ·
                      rfl

theorem cell23_1582336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_1582336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582336 prefixEnd_1582336 := by exact prefixLift 1582336
  have htrace : WordTrace (prefixWord ++ tailWord_1582336) baseStart_1582336 baseEnd_1582336 := by
    simpa [prefixWord, tailWord_1582336, baseEnd_1582336] using wordTrace_append hprefix tailTrace_1582336
  have hstable : (prefixWord ++ tailWord_1582336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582336).length < 2 ^ (prefixWord ++ tailWord_1582336).sum := by decide
  have hdescent : baseEnd_1582336 < baseStart_1582336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582404 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1582404 : Nat := 118140960795 + 1582404 * 2 ^ 59
def prefixEnd_1582404 : Nat := 4983230072969 + 3 ^ 40 * 1582404 * 2
def baseEnd_1582404 : Nat := 270844613865777356924221

theorem tailTrace_1582404 : CollatzResearch.WordTrace tailWord_1582404 prefixEnd_1582404 270844613865777356924221 := by
  unfold tailWord_1582404
  simp only [CollatzResearch.WordTrace]
  refine ⟨28857507679614017966181133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38476676906152023954908177 28857507679614017966181133)
  ·
    refine ⟨10821565379855256737317925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28857507679614017966181133 10821565379855256737317925)
    ·
      refine ⟨2029043508722860638247111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10821565379855256737317925 2029043508722860638247111)
      ·
        refine ⟨3043565263084290957370667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029043508722860638247111 3043565263084290957370667)
        ·
          refine ⟨4565347894626436436056001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043565263084290957370667 4565347894626436436056001)
          ·
            refine ⟨3424010920969827327042001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4565347894626436436056001 3424010920969827327042001)
            ·
              refine ⟨2568008190727370495281501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424010920969827327042001 2568008190727370495281501)
              ·
                refine ⟨963003071522763935730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568008190727370495281501 963003071522763935730563)
                ·
                  refine ⟨1444504607284145903595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963003071522763935730563 1444504607284145903595845)
                  ·
                    refine ⟨270844613865777356924221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444504607284145903595845 270844613865777356924221)
                    ·
                      rfl

theorem cell23_1582404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1582404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582404 prefixEnd_1582404 := by exact prefixLift 1582404
  have htrace : WordTrace (prefixWord ++ tailWord_1582404) baseStart_1582404 baseEnd_1582404 := by
    simpa [prefixWord, tailWord_1582404, baseEnd_1582404] using wordTrace_append hprefix tailTrace_1582404
  have hstable : (prefixWord ++ tailWord_1582404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582404).length < 2 ^ (prefixWord ++ tailWord_1582404).sum := by decide
  have hdescent : baseEnd_1582404 < baseStart_1582404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582420 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_1582420 : Nat := 118140960795 + 1582420 * 2 ^ 59
def prefixEnd_1582420 : Nat := 4983230072969 + 3 ^ 40 * 1582420 * 2
def baseEnd_1582420 : Nat := 812542057287804008172589

theorem tailTrace_1582420 : CollatzResearch.WordTrace tailWord_1582420 prefixEnd_1582420 812542057287804008172589 := by
  unfold tailWord_1582420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28857799463585035332472357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38477065951446713776629809 28857799463585035332472357)
  ·
    refine ⟨5410837399422194124838567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28857799463585035332472357 5410837399422194124838567)
    ·
      refine ⟨8116256099133291187257851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410837399422194124838567 8116256099133291187257851)
      ·
        refine ⟨12174384148699936780886777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8116256099133291187257851 12174384148699936780886777)
        ·
          refine ⟨9130788111524952585665083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12174384148699936780886777 9130788111524952585665083)
          ·
            refine ⟨13696182167287428878497625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130788111524952585665083 13696182167287428878497625)
            ·
              refine ⟨10272136625465571658873219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13696182167287428878497625 10272136625465571658873219)
              ·
                refine ⟨15408204938198357488309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272136625465571658873219 15408204938198357488309829)
                ·
                  refine ⟨2889038425912192029058093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15408204938198357488309829 2889038425912192029058093)
                  ·
                    refine ⟨1083389409717072010896785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2889038425912192029058093 1083389409717072010896785)
                    ·
                      refine ⟨812542057287804008172589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083389409717072010896785 812542057287804008172589)
                      ·
                        rfl

theorem cell23_1582420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_1582420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582420 prefixEnd_1582420 := by exact prefixLift 1582420
  have htrace : WordTrace (prefixWord ++ tailWord_1582420) baseStart_1582420 baseEnd_1582420 := by
    simpa [prefixWord, tailWord_1582420, baseEnd_1582420] using wordTrace_append hprefix tailTrace_1582420
  have hstable : (prefixWord ++ tailWord_1582420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582420).length < 2 ^ (prefixWord ++ tailWord_1582420).sum := by decide
  have hdescent : baseEnd_1582420 < baseStart_1582420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582426 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_1582426 : Nat := 118140960795 + 1582426 * 2 ^ 59
def prefixEnd_1582426 : Nat := 4983230072969 + 3 ^ 40 * 1582426 * 2
def baseEnd_1582426 : Nat := 270848379390576994899187

theorem tailTrace_1582426 : CollatzResearch.WordTrace tailWord_1582426 prefixEnd_1582426 270848379390576994899187 := by
  unfold tailWord_1582426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428954441287083422415783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38477211843432222459775421 14428954441287083422415783)
  ·
    refine ⟨21643431661930625133623675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14428954441287083422415783 21643431661930625133623675)
    ·
      refine ⟨32465147492895937700435513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21643431661930625133623675 32465147492895937700435513)
      ·
        refine ⟨24348860619671953275326635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465147492895937700435513 24348860619671953275326635)
        ·
          refine ⟨36523290929507929912989953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24348860619671953275326635 36523290929507929912989953)
          ·
            refine ⟨27392468197130947434742465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36523290929507929912989953 27392468197130947434742465)
            ·
              refine ⟨20544351147848210576056849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27392468197130947434742465 20544351147848210576056849)
              ·
                refine ⟨15408263360886157932042637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20544351147848210576056849 15408263360886157932042637)
                ·
                  refine ⟨5778098760332309224515989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15408263360886157932042637 5778098760332309224515989)
                  ·
                    refine ⟨270848379390576994899187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5778098760332309224515989 270848379390576994899187)
                    ·
                      rfl

theorem cell23_1582426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_1582426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582426 prefixEnd_1582426 := by exact prefixLift 1582426
  have htrace : WordTrace (prefixWord ++ tailWord_1582426) baseStart_1582426 baseEnd_1582426 := by
    simpa [prefixWord, tailWord_1582426, baseEnd_1582426] using wordTrace_append hprefix tailTrace_1582426
  have hstable : (prefixWord ++ tailWord_1582426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582426).length < 2 ^ (prefixWord ++ tailWord_1582426).sum := by decide
  have hdescent : baseEnd_1582426 < baseStart_1582426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582450 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1582450 : Nat := 118140960795 + 1582450 * 2 ^ 59
def prefixEnd_1582450 : Nat := 4983230072969 + 3 ^ 40 * 1582450 * 2
def baseEnd_1582450 : Nat := 812557461707438890797451

theorem tailTrace_1582450 : CollatzResearch.WordTrace tailWord_1582450 prefixEnd_1582450 812557461707438890797451 := by
  unfold tailWord_1582450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429173279265346447134201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38477795411374257192357869 14429173279265346447134201)
  ·
    refine ⟨10821879959449009835350651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14429173279265346447134201 10821879959449009835350651)
    ·
      refine ⟨16232819939173514753025977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10821879959449009835350651 16232819939173514753025977)
      ·
        refine ⟨12174614954380136064769483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16232819939173514753025977 12174614954380136064769483)
        ·
          refine ⟨18261922431570204097154225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12174614954380136064769483 18261922431570204097154225)
          ·
            refine ⟨13696441823677653072865669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18261922431570204097154225 13696441823677653072865669)
            ·
              refine ⟨2568082841939559951162313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13696441823677653072865669 2568082841939559951162313)
              ·
                refine ⟨1926062131454669963371735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568082841939559951162313 1926062131454669963371735)
                ·
                  refine ⟨2889093197182004945057603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926062131454669963371735 2889093197182004945057603)
                  ·
                    refine ⟨4333639795773007417586405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889093197182004945057603 4333639795773007417586405)
                    ·
                      refine ⟨812557461707438890797451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4333639795773007417586405 812557461707438890797451)
                      ·
                        rfl

theorem cell23_1582450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1582450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582450 prefixEnd_1582450 := by exact prefixLift 1582450
  have htrace : WordTrace (prefixWord ++ tailWord_1582450) baseStart_1582450 baseEnd_1582450 := by
    simpa [prefixWord, tailWord_1582450, baseEnd_1582450] using wordTrace_append hprefix tailTrace_1582450
  have hstable : (prefixWord ++ tailWord_1582450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582450).length < 2 ^ (prefixWord ++ tailWord_1582450).sum := by decide
  have hdescent : baseEnd_1582450 < baseStart_1582450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582473 : List Nat := [1, 2, 1, 1, 7, 2, 9]
def baseStart_1582473 : Nat := 118140960795 + 1582473 * 2 ^ 59
def prefixEnd_1582473 : Nat := 4983230072969 + 3 ^ 40 * 1582473 * 2
def baseEnd_1582473 : Nat := 10031719404475213590245

theorem tailTrace_1582473 : CollatzResearch.WordTrace tailWord_1582473 prefixEnd_1582473 10031719404475213590245 := by
  unfold tailWord_1582473
  simp only [CollatzResearch.WordTrace]
  refine ⟨57717531995978060716624073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38478354663985373811082715 57717531995978060716624073)
  ·
    refine ⟨43288148996983545537468055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57717531995978060716624073 43288148996983545537468055)
    ·
      refine ⟨64932223495475318306202083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43288148996983545537468055 64932223495475318306202083)
      ·
        refine ⟨97398335243212977459303125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64932223495475318306202083 97398335243212977459303125)
        ·
          refine ⟨2282773482262804159202417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97398335243212977459303125 2282773482262804159202417)
          ·
            refine ⟨1712080111697103119401813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282773482262804159202417 1712080111697103119401813)
            ·
              refine ⟨10031719404475213590245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1712080111697103119401813 10031719404475213590245)
              ·
                rfl

theorem cell23_1582473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 9].length) (baseStart_1582473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582473 prefixEnd_1582473 := by exact prefixLift 1582473
  have htrace : WordTrace (prefixWord ++ tailWord_1582473) baseStart_1582473 baseEnd_1582473 := by
    simpa [prefixWord, tailWord_1582473, baseEnd_1582473] using wordTrace_append hprefix tailTrace_1582473
  have hstable : (prefixWord ++ tailWord_1582473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582473).length < 2 ^ (prefixWord ++ tailWord_1582473).sum := by decide
  have hdescent : baseEnd_1582473 < baseStart_1582473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582484 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1582484 : Nat := 118140960795 + 1582484 * 2 ^ 59
def prefixEnd_1582484 : Nat := 4983230072969 + 3 ^ 40 * 1582484 * 2
def baseEnd_1582484 : Nat := 812574920049691757772295

theorem tailTrace_1582484 : CollatzResearch.WordTrace tailWord_1582484 prefixEnd_1582484 812574920049691757772295 := by
  unfold tailWord_1582484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858966599469104797637253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38478622132625473063516337 28858966599469104797637253)
  ·
    refine ⟨5411056237400457149556985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28858966599469104797637253 5411056237400457149556985)
    ·
      refine ⟨4058292178050342862167739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5411056237400457149556985 4058292178050342862167739)
      ·
        refine ⟨6087438267075514293251609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058292178050342862167739 6087438267075514293251609)
        ·
          refine ⟨4565578700306635719938707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087438267075514293251609 4565578700306635719938707)
          ·
            refine ⟨6848368050459953579908061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565578700306635719938707 6848368050459953579908061)
            ·
              refine ⟨2568138018922482592465523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6848368050459953579908061 2568138018922482592465523)
              ·
                refine ⟨3852207028383723888698285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568138018922482592465523 3852207028383723888698285)
                ·
                  refine ⟨1444577635643896458261857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3852207028383723888698285 1444577635643896458261857)
                  ·
                    refine ⟨1083433226732922343696393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444577635643896458261857 1083433226732922343696393)
                    ·
                      refine ⟨812574920049691757772295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083433226732922343696393 812574920049691757772295)
                      ·
                        rfl

theorem cell23_1582484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1582484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582484 prefixEnd_1582484 := by exact prefixLift 1582484
  have htrace : WordTrace (prefixWord ++ tailWord_1582484) baseStart_1582484 baseEnd_1582484 := by
    simpa [prefixWord, tailWord_1582484, baseEnd_1582484] using wordTrace_append hprefix tailTrace_1582484
  have hstable : (prefixWord ++ tailWord_1582484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582484).length < 2 ^ (prefixWord ++ tailWord_1582484).sum := by decide
  have hdescent : baseEnd_1582484 < baseStart_1582484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582494 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1582494 : Nat := 118140960795 + 1582494 * 2 ^ 59
def prefixEnd_1582494 : Nat := 4983230072969 + 3 ^ 40 * 1582494 * 2
def baseEnd_1582494 : Nat := 270860018285412239549083

theorem tailTrace_1582494 : CollatzResearch.WordTrace tailWord_1582494 prefixEnd_1582494 270860018285412239549083 := by
  unfold tailWord_1582494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214787241112747662892317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38478865285934654202092357 7214787241112747662892317)
  ·
    refine ⟨2705545215417280373584619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7214787241112747662892317 2705545215417280373584619)
    ·
      refine ⟨4058317823125920560376929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705545215417280373584619 4058317823125920560376929)
      ·
        refine ⟨3043738367344440420282697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058317823125920560376929 3043738367344440420282697)
        ·
          refine ⟨2282803775508330315212023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043738367344440420282697 2282803775508330315212023)
          ·
            refine ⟨3424205663262495472818035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282803775508330315212023 3424205663262495472818035)
            ·
              refine ⟨5136308494893743209227053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424205663262495472818035 5136308494893743209227053)
              ·
                refine ⟨1926115685585153703460145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5136308494893743209227053 1926115685585153703460145)
                ·
                  refine ⟨1444586764188865277595109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926115685585153703460145 1444586764188865277595109)
                  ·
                    refine ⟨270860018285412239549083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444586764188865277595109 270860018285412239549083)
                    ·
                      rfl

theorem cell23_1582494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1582494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582494 prefixEnd_1582494 := by exact prefixLift 1582494
  have htrace : WordTrace (prefixWord ++ tailWord_1582494) baseStart_1582494 baseEnd_1582494 := by
    simpa [prefixWord, tailWord_1582494, baseEnd_1582494] using wordTrace_append hprefix tailTrace_1582494
  have hstable : (prefixWord ++ tailWord_1582494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582494).length < 2 ^ (prefixWord ++ tailWord_1582494).sum := by decide
  have hdescent : baseEnd_1582494 < baseStart_1582494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582543 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_1582543 : Nat := 118140960795 + 1582543 * 2 ^ 59
def prefixEnd_1582543 : Nat := 4983230072969 + 3 ^ 40 * 1582543 * 2
def baseEnd_1582543 : Nat := 812605215408307026934523

theorem tailTrace_1582543 : CollatzResearch.WordTrace tailWord_1582543 prefixEnd_1582543 812605215408307026934523 := by
  unfold tailWord_1582543
  simp only [CollatzResearch.WordTrace]
  refine ⟨57720085105724462671672283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38480056737149641781114855 57720085105724462671672283)
  ·
    refine ⟨86580127658586694007508425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57720085105724462671672283 86580127658586694007508425)
    ·
      refine ⟨64935095743940020505631319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86580127658586694007508425 64935095743940020505631319)
      ·
        refine ⟨97402643615910030758446979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64935095743940020505631319 97402643615910030758446979)
        ·
          refine ⟨146103965423865046137670469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97402643615910030758446979 146103965423865046137670469)
          ·
            refine ⟨27394493516974696150813213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146103965423865046137670469 27394493516974696150813213)
            ·
              refine ⟨10272935068865511056554955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27394493516974696150813213 10272935068865511056554955)
              ·
                refine ⟨15409402603298266584832433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272935068865511056554955 15409402603298266584832433)
                ·
                  refine ⟨11557051952473699938624325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15409402603298266584832433 11557051952473699938624325)
                  ·
                    refine ⟨2166947241088818738492061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11557051952473699938624325 2166947241088818738492061)
                    ·
                      refine ⟨812605215408307026934523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2166947241088818738492061 812605215408307026934523)
                      ·
                        rfl

theorem cell23_1582543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_1582543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582543 prefixEnd_1582543 := by exact prefixLift 1582543
  have htrace : WordTrace (prefixWord ++ tailWord_1582543) baseStart_1582543 baseEnd_1582543 := by
    simpa [prefixWord, tailWord_1582543, baseEnd_1582543] using wordTrace_append hprefix tailTrace_1582543
  have hstable : (prefixWord ++ tailWord_1582543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582543).length < 2 ^ (prefixWord ++ tailWord_1582543).sum := by decide
  have hdescent : baseEnd_1582543 < baseStart_1582543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582550 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1582550 : Nat := 118140960795 + 1582550 * 2 ^ 59
def prefixEnd_1582550 : Nat := 4983230072969 + 3 ^ 40 * 1582550 * 2
def baseEnd_1582550 : Nat := 270869603257629499848997

theorem tailTrace_1582550 : CollatzResearch.WordTrace tailWord_1582550 prefixEnd_1582550 270869603257629499848997 := by
  unfold tailWord_1582550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607521276043693929198569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38480226944466068578118069 3607521276043693929198569)
  ·
    refine ⟨2705640957032770446898927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3607521276043693929198569 2705640957032770446898927)
    ·
      refine ⟨4058461435549155670348391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705640957032770446898927 4058461435549155670348391)
      ·
        refine ⟨6087692153323733505522587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058461435549155670348391 6087692153323733505522587)
        ·
          refine ⟨9131538229985600258283881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087692153323733505522587 9131538229985600258283881)
          ·
            refine ⟨6848653672489200193712911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131538229985600258283881 6848653672489200193712911)
            ·
              refine ⟨10272980508733800290569367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848653672489200193712911 10272980508733800290569367)
              ·
                refine ⟨15409470763100700435854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272980508733800290569367 15409470763100700435854051)
                ·
                  refine ⟨23114206144651050653781077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15409470763100700435854051 23114206144651050653781077)
                  ·
                    refine ⟨270869603257629499848997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23114206144651050653781077 270869603257629499848997)
                    ·
                      rfl

theorem cell23_1582550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1582550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582550 prefixEnd_1582550 := by exact prefixLift 1582550
  have htrace : WordTrace (prefixWord ++ tailWord_1582550) baseStart_1582550 baseEnd_1582550 := by
    simpa [prefixWord, tailWord_1582550, baseEnd_1582550] using wordTrace_append hprefix tailTrace_1582550
  have hstable : (prefixWord ++ tailWord_1582550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582550).length < 2 ^ (prefixWord ++ tailWord_1582550).sum := by decide
  have hdescent : baseEnd_1582550 < baseStart_1582550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582553 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1582553 : Nat := 118140960795 + 1582553 * 2 ^ 59
def prefixEnd_1582553 : Nat := 4983230072969 + 3 ^ 40 * 1582553 * 2
def baseEnd_1582553 : Nat := 812610350214851987809477

theorem tailTrace_1582553 : CollatzResearch.WordTrace tailWord_1582553 prefixEnd_1582553 812610350214851987809477 := by
  unfold tailWord_1582553
  simp only [CollatzResearch.WordTrace]
  refine ⟨57720449835688234379536313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38480299890458822919690875 57720449835688234379536313)
  ·
    refine ⟨43290337376766175784652235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57720449835688234379536313 43290337376766175784652235)
    ·
      refine ⟨64935506065149263676978353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43290337376766175784652235 64935506065149263676978353)
      ·
        refine ⟨48701629548861947757733765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64935506065149263676978353 48701629548861947757733765)
        ·
          refine ⟨9131555540411615204575081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48701629548861947757733765 9131555540411615204575081)
          ·
            refine ⟨6848666655308711403431311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131555540411615204575081 6848666655308711403431311)
            ·
              refine ⟨10272999982963067105146967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848666655308711403431311 10272999982963067105146967)
              ·
                refine ⟨15409499974444600657720451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10272999982963067105146967 15409499974444600657720451)
                ·
                  refine ⟨23114249961666900986580677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15409499974444600657720451 23114249961666900986580677)
                  ·
                    refine ⟨4333921867812543934983877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23114249961666900986580677 4333921867812543934983877)
                    ·
                      refine ⟨812610350214851987809477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4333921867812543934983877 812610350214851987809477)
                      ·
                        rfl

theorem cell23_1582553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1582553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582553 prefixEnd_1582553 := by exact prefixLift 1582553
  have htrace : WordTrace (prefixWord ++ tailWord_1582553) baseStart_1582553 baseEnd_1582553 := by
    simpa [prefixWord, tailWord_1582553, baseEnd_1582553] using wordTrace_append hprefix tailTrace_1582553
  have hstable : (prefixWord ++ tailWord_1582553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582553).length < 2 ^ (prefixWord ++ tailWord_1582553).sum := by decide
  have hdescent : baseEnd_1582553 < baseStart_1582553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582557 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1582557 : Nat := 118140960795 + 1582557 * 2 ^ 59
def prefixEnd_1582557 : Nat := 4983230072969 + 3 ^ 40 * 1582557 * 2
def baseEnd_1582557 : Nat := 812612404137469972159459

theorem tailTrace_1582557 : CollatzResearch.WordTrace tailWord_1582557 prefixEnd_1582557 812612404137469972159459 := by
  unfold tailWord_1582557
  simp only [CollatzResearch.WordTrace]
  refine ⟨57720595727673743062681925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38480397151782495375121283 57720595727673743062681925)
  ·
    refine ⟨10822611698938826824252861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57720595727673743062681925 10822611698938826824252861)
    ·
      refine ⟨4058479387102060059094823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10822611698938826824252861 4058479387102060059094823)
      ·
        refine ⟨6087719080653090088642235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058479387102060059094823 6087719080653090088642235)
        ·
          refine ⟨9131578620979635132963353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087719080653090088642235 9131578620979635132963353)
          ·
            refine ⟨6848683965734726349722515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131578620979635132963353 6848683965734726349722515)
            ·
              refine ⟨10273025948602089524583773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848683965734726349722515 10273025948602089524583773)
              ·
                refine ⟨3852384730725783571718915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10273025948602089524583773 3852384730725783571718915)
                ·
                  refine ⟨5778577096088675357578373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3852384730725783571718915 5778577096088675357578373)
                  ·
                    refine ⟨1083483205516626629545945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5778577096088675357578373 1083483205516626629545945)
                    ·
                      refine ⟨812612404137469972159459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083483205516626629545945 812612404137469972159459)
                      ·
                        rfl

theorem cell23_1582557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1582557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582557 prefixEnd_1582557 := by exact prefixLift 1582557
  have htrace : WordTrace (prefixWord ++ tailWord_1582557) baseStart_1582557 baseEnd_1582557 := by
    simpa [prefixWord, tailWord_1582557, baseEnd_1582557] using wordTrace_append hprefix tailTrace_1582557
  have hstable : (prefixWord ++ tailWord_1582557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582557).length < 2 ^ (prefixWord ++ tailWord_1582557).sum := by decide
  have hdescent : baseEnd_1582557 < baseStart_1582557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582563 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 9]
def baseStart_1582563 : Nat := 118140960795 + 1582563 * 2 ^ 59
def prefixEnd_1582563 : Nat := 4983230072969 + 3 ^ 40 * 1582563 * 2
def baseEnd_1582563 : Nat := 90290609446821883187159

theorem tailTrace_1582563 : CollatzResearch.WordTrace tailWord_1582563 prefixEnd_1582563 90290609446821883187159 := by
  unfold tailWord_1582563
  simp only [CollatzResearch.WordTrace]
  refine ⟨57720814565652006087400343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38480543043768004058266895 57720814565652006087400343)
  ·
    refine ⟨86581221848478009131100515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57720814565652006087400343 86581221848478009131100515)
    ·
      refine ⟨129871832772717013696650773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86581221848478009131100515 129871832772717013696650773)
      ·
        refine ⟨6087742161221110017030505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129871832772717013696650773 6087742161221110017030505)
        ·
          refine ⟨4565806620915832512772879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087742161221110017030505 4565806620915832512772879)
          ·
            refine ⟨6848709931373748769159319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565806620915832512772879 6848709931373748769159319)
            ·
              refine ⟨10273064897060623153738979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848709931373748769159319 10273064897060623153738979)
              ·
                refine ⟨15409597345590934730608469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10273064897060623153738979 15409597345590934730608469)
                ·
                  refine ⟨90290609446821883187159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15409597345590934730608469 90290609446821883187159)
                  ·
                    rfl

theorem cell23_1582563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 9].length) (baseStart_1582563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582563 prefixEnd_1582563 := by exact prefixLift 1582563
  have htrace : WordTrace (prefixWord ++ tailWord_1582563) baseStart_1582563 baseEnd_1582563 := by
    simpa [prefixWord, tailWord_1582563, baseEnd_1582563] using wordTrace_append hprefix tailTrace_1582563
  have hstable : (prefixWord ++ tailWord_1582563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582563).length < 2 ^ (prefixWord ++ tailWord_1582563).sum := by decide
  have hdescent : baseEnd_1582563 < baseStart_1582563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582600 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_1582600 : Nat := 118140960795 + 1582600 * 2 ^ 59
def prefixEnd_1582600 : Nat := 4983230072969 + 3 ^ 40 * 1582600 * 2
def baseEnd_1582600 : Nat := 812634483805613303921761

theorem tailTrace_1582600 : CollatzResearch.WordTrace tailWord_1582600 prefixEnd_1582600 812634483805613303921761 := by
  unfold tailWord_1582600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861082033258980703248627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38481442711011974270998169 28861082033258980703248627)
  ·
    refine ⟨43291623049888471054872941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28861082033258980703248627 43291623049888471054872941)
    ·
      refine ⟨16234358643708176645577353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43291623049888471054872941 16234358643708176645577353)
      ·
        refine ⟨12175768982781132484183015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16234358643708176645577353 12175768982781132484183015)
        ·
          refine ⟨18263653474171698726274523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12175768982781132484183015 18263653474171698726274523)
          ·
            refine ⟨27395480211257548089411785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18263653474171698726274523 27395480211257548089411785)
            ·
              refine ⟨20546610158443161067058839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27395480211257548089411785 20546610158443161067058839)
              ·
                refine ⟨30819915237664741600588259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20546610158443161067058839 30819915237664741600588259)
                ·
                  refine ⟨46229872856497112400882389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30819915237664741600588259 46229872856497112400882389)
                  ·
                    refine ⟨1083512645074151071895681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46229872856497112400882389 1083512645074151071895681)
                    ·
                      refine ⟨812634483805613303921761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083512645074151071895681 812634483805613303921761)
                      ·
                        rfl

theorem cell23_1582600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_1582600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582600 prefixEnd_1582600 := by exact prefixLift 1582600
  have htrace : WordTrace (prefixWord ++ tailWord_1582600) baseStart_1582600 baseEnd_1582600 := by
    simpa [prefixWord, tailWord_1582600, baseEnd_1582600] using wordTrace_append hprefix tailTrace_1582600
  have hstable : (prefixWord ++ tailWord_1582600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582600).length < 2 ^ (prefixWord ++ tailWord_1582600).sum := by decide
  have hdescent : baseEnd_1582600 < baseStart_1582600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582684 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1582684 : Nat := 118140960795 + 1582684 * 2 ^ 59
def prefixEnd_1582684 : Nat := 4983230072969 + 3 ^ 40 * 1582684 * 2
def baseEnd_1582684 : Nat := 812677616180590975271375

theorem tailTrace_1582684 : CollatzResearch.WordTrace tailWord_1582684 prefixEnd_1582684 812677616180590975271375 := by
  unfold tailWord_1582684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862613899106821876277553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38483485198809095835036737 28862613899106821876277553)
  ·
    refine ⟨21646960424330116407208165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28862613899106821876277553 21646960424330116407208165)
    ·
      refine ⟨4058805079561896826351531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21646960424330116407208165 4058805079561896826351531)
      ·
        refine ⟨6088207619342845239527297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058805079561896826351531 6088207619342845239527297)
        ·
          refine ⟨4566155714507133929645473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088207619342845239527297 4566155714507133929645473)
          ·
            refine ⟨3424616785880350447234105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566155714507133929645473 3424616785880350447234105)
            ·
              refine ⟨2568462589410262835425579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424616785880350447234105 2568462589410262835425579)
              ·
                refine ⟨3852693884115394253138369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568462589410262835425579 3852693884115394253138369)
                ·
                  refine ⟨2889520413086545689853777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852693884115394253138369 2889520413086545689853777)
                  ·
                    refine ⟨2167140309814909267390333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2889520413086545689853777 2167140309814909267390333)
                    ·
                      refine ⟨812677616180590975271375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167140309814909267390333 812677616180590975271375)
                      ·
                        rfl

theorem cell23_1582684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1582684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582684 prefixEnd_1582684 := by exact prefixLift 1582684
  have htrace : WordTrace (prefixWord ++ tailWord_1582684) baseStart_1582684 baseEnd_1582684 := by
    simpa [prefixWord, tailWord_1582684, baseEnd_1582684] using wordTrace_append hprefix tailTrace_1582684
  have hstable : (prefixWord ++ tailWord_1582684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582684).length < 2 ^ (prefixWord ++ tailWord_1582684).sum := by decide
  have hdescent : baseEnd_1582684 < baseStart_1582684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582720 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_1582720 : Nat := 118140960795 + 1582720 * 2 ^ 59
def prefixEnd_1582720 : Nat := 4983230072969 + 3 ^ 40 * 1582720 * 2
def baseEnd_1582720 : Nat := 812696101484152834421209

theorem tailTrace_1582720 : CollatzResearch.WordTrace tailWord_1582720 prefixEnd_1582720 812696101484152834421209 := by
  unfold tailWord_1582720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863270413041610950432807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38484360550722147933910409 28863270413041610950432807)
  ·
    refine ⟨43294905619562416425649211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28863270413041610950432807 43294905619562416425649211)
    ·
      refine ⟨64942358429343624638473817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43294905619562416425649211 64942358429343624638473817)
      ·
        refine ⟨48706768822007718478855363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64942358429343624638473817 48706768822007718478855363)
        ·
          refine ⟨73060153233011577718283045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48706768822007718478855363 73060153233011577718283045)
          ·
            refine ⟨13698778731189670822178071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73060153233011577718283045 13698778731189670822178071)
            ·
              refine ⟨20548168096784506233267107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13698778731189670822178071 20548168096784506233267107)
              ·
                refine ⟨30822252145176759349900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20548168096784506233267107 30822252145176759349900661)
                ·
                  refine ⟨2889586138610321189053187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30822252145176759349900661 2889586138610321189053187)
                  ·
                    refine ⟨4334379207915481783579781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2889586138610321189053187 4334379207915481783579781)
                    ·
                      refine ⟨812696101484152834421209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4334379207915481783579781 812696101484152834421209)
                      ·
                        rfl

theorem cell23_1582720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_1582720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582720 prefixEnd_1582720 := by exact prefixLift 1582720
  have htrace : WordTrace (prefixWord ++ tailWord_1582720) baseStart_1582720 baseEnd_1582720 := by
    simpa [prefixWord, tailWord_1582720, baseEnd_1582720] using wordTrace_append hprefix tailTrace_1582720
  have hstable : (prefixWord ++ tailWord_1582720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582720).length < 2 ^ (prefixWord ++ tailWord_1582720).sum := by decide
  have hdescent : baseEnd_1582720 < baseStart_1582720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582748 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_1582748 : Nat := 118140960795 + 1582748 * 2 ^ 59
def prefixEnd_1582748 : Nat := 4983230072969 + 3 ^ 40 * 1582748 * 2
def baseEnd_1582748 : Nat := 812710478942478724871081

theorem tailTrace_1582748 : CollatzResearch.WordTrace tailWord_1582748 prefixEnd_1582748 812710478942478724871081 := by
  unfold tailWord_1582748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863781034990891341442449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38485041379987855121923265 28863781034990891341442449)
  ·
    refine ⟨21647835776243168506081837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28863781034990891341442449 21647835776243168506081837)
    ·
      refine ⟨8117938416091188189780689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21647835776243168506081837 8117938416091188189780689)
      ·
        refine ⟨6088453812068391142335517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117938416091188189780689 6088453812068391142335517)
        ·
          refine ⟨2283170179525646678375819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6088453812068391142335517 2283170179525646678375819)
          ·
            refine ⟨3424755269288470017563729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283170179525646678375819 3424755269288470017563729)
            ·
              refine ⟨2568566451966352513172797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424755269288470017563729 2568566451966352513172797)
              ·
                refine ⟨963212419487382192439799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568566451966352513172797 963212419487382192439799)
                ·
                  refine ⟨1444818629231073288659699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963212419487382192439799 1444818629231073288659699)
                  ·
                    refine ⟨2167227943846609932989549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444818629231073288659699 2167227943846609932989549)
                    ·
                      refine ⟨812710478942478724871081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167227943846609932989549 812710478942478724871081)
                      ·
                        rfl

theorem cell23_1582748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_1582748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582748 prefixEnd_1582748 := by exact prefixLift 1582748
  have htrace : WordTrace (prefixWord ++ tailWord_1582748) baseStart_1582748 baseEnd_1582748 := by
    simpa [prefixWord, tailWord_1582748, baseEnd_1582748] using wordTrace_append hprefix tailTrace_1582748
  have hstable : (prefixWord ++ tailWord_1582748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582748).length < 2 ^ (prefixWord ++ tailWord_1582748).sum := by decide
  have hdescent : baseEnd_1582748 < baseStart_1582748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582771 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 1, 2, 2]
def baseStart_1582771 : Nat := 118140960795 + 1582771 * 2 ^ 59
def prefixEnd_1582771 : Nat := 4983230072969 + 3 ^ 40 * 1582771 * 2
def baseEnd_1582771 : Nat := 812722288997532134883475

theorem tailTrace_1582771 : CollatzResearch.WordTrace tailWord_1582771 prefixEnd_1582771 812722288997532134883475 := by
  unfold tailWord_1582771
  simp only [CollatzResearch.WordTrace]
  refine ⟨57728400948898457610972167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38485600632598971740648111 57728400948898457610972167)
  ·
    refine ⟨86592601423347686416458251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57728400948898457610972167 86592601423347686416458251)
    ·
      refine ⟨129888902135021529624687377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86592601423347686416458251 129888902135021529624687377)
      ·
        refine ⟨97416676601266147218515533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129888902135021529624687377 97416676601266147218515533)
        ·
          refine ⟨36531253725474805206943325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97416676601266147218515533 36531253725474805206943325)
          ·
            refine ⟨13699220147053051952603747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36531253725474805206943325 13699220147053051952603747)
            ·
              refine ⟨20548830220579577928905621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13699220147053051952603747 20548830220579577928905621)
              ·
                refine ⟨963226416589667715417451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20548830220579577928905621 963226416589667715417451)
                ·
                  refine ⟨1444839624884501573126177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963226416589667715417451 1444839624884501573126177)
                  ·
                    refine ⟨1083629718663376179844633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444839624884501573126177 1083629718663376179844633)
                    ·
                      refine ⟨812722288997532134883475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083629718663376179844633 812722288997532134883475)
                      ·
                        rfl

theorem cell23_1582771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 2, 2].length) (baseStart_1582771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582771 prefixEnd_1582771 := by exact prefixLift 1582771
  have htrace : WordTrace (prefixWord ++ tailWord_1582771) baseStart_1582771 baseEnd_1582771 := by
    simpa [prefixWord, tailWord_1582771, baseEnd_1582771] using wordTrace_append hprefix tailTrace_1582771
  have hstable : (prefixWord ++ tailWord_1582771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582771).length < 2 ^ (prefixWord ++ tailWord_1582771).sum := by decide
  have hdescent : baseEnd_1582771 < baseStart_1582771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582774 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1582774 : Nat := 118140960795 + 1582774 * 2 ^ 59
def prefixEnd_1582774 : Nat := 4983230072969 + 3 ^ 40 * 1582774 * 2
def baseEnd_1582774 : Nat := 812723829439495623145961

theorem tailTrace_1582774 : CollatzResearch.WordTrace tailWord_1582774 prefixEnd_1582774 812723829439495623145961 := by
  unfold tailWord_1582774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608031897992974320208211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38485673578591726082220917 3608031897992974320208211)
  ·
    refine ⟨5412047846989461480312317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608031897992974320208211 5412047846989461480312317)
    ·
      refine ⟨2029517942621048055117119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5412047846989461480312317 2029517942621048055117119)
      ·
        refine ⟨3044276913931572082675679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029517942621048055117119 3044276913931572082675679)
        ·
          refine ⟨4566415370897358124013519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044276913931572082675679 4566415370897358124013519)
          ·
            refine ⟨6849623056346037186020279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566415370897358124013519 6849623056346037186020279)
            ·
              refine ⟨10274434584519055779030419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6849623056346037186020279 10274434584519055779030419)
              ·
                refine ⟨15411651876778583668545629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10274434584519055779030419 15411651876778583668545629)
                ·
                  refine ⟨5779369453791968875704611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15411651876778583668545629 5779369453791968875704611)
                  ·
                    refine ⟨8669054180687953313556917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5779369453791968875704611 8669054180687953313556917)
                    ·
                      refine ⟨812723829439495623145961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8669054180687953313556917 812723829439495623145961)
                      ·
                        rfl

theorem cell23_1582774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1582774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582774 prefixEnd_1582774 := by exact prefixLift 1582774
  have htrace : WordTrace (prefixWord ++ tailWord_1582774) baseStart_1582774 baseEnd_1582774 := by
    simpa [prefixWord, tailWord_1582774, baseEnd_1582774] using wordTrace_append hprefix tailTrace_1582774
  have hstable : (prefixWord ++ tailWord_1582774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582774).length < 2 ^ (prefixWord ++ tailWord_1582774).sum := by decide
  have hdescent : baseEnd_1582774 < baseStart_1582774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582794 : List Nat := [3, 1, 2, 1, 5, 2, 2, 7]
def baseStart_1582794 : Nat := 118140960795 + 1582794 * 2 ^ 59
def prefixEnd_1582794 : Nat := 4983230072969 + 3 ^ 40 * 1582794 * 2
def baseEnd_1582794 : Nat := 30101262927873538699847

theorem tailTrace_1582794 : CollatzResearch.WordTrace tailWord_1582794 prefixEnd_1582794 30101262927873538699847 := by
  unfold tailWord_1582794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432309956953783134764859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38486159885210088359372957 14432309956953783134764859)
  ·
    refine ⟨21648464935430674702147289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14432309956953783134764859 21648464935430674702147289)
    ·
      refine ⟨16236348701573006026610467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21648464935430674702147289 16236348701573006026610467)
      ·
        refine ⟨24354523052359509039915701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236348701573006026610467 24354523052359509039915701)
        ·
          refine ⟨2283236536158703972492097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24354523052359509039915701 2283236536158703972492097)
          ·
            refine ⟨1712427402119027979369073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283236536158703972492097 1712427402119027979369073)
            ·
              refine ⟨1284320551589270984526805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712427402119027979369073 1284320551589270984526805)
              ·
                refine ⟨30101262927873538699847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1284320551589270984526805 30101262927873538699847)
                ·
                  rfl

theorem cell23_1582794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_1582794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582794 prefixEnd_1582794 := by exact prefixLift 1582794
  have htrace : WordTrace (prefixWord ++ tailWord_1582794) baseStart_1582794 baseEnd_1582794 := by
    simpa [prefixWord, tailWord_1582794, baseEnd_1582794] using wordTrace_append hprefix tailTrace_1582794
  have hstable : (prefixWord ++ tailWord_1582794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582794).length < 2 ^ (prefixWord ++ tailWord_1582794).sum := by decide
  have hdescent : baseEnd_1582794 < baseStart_1582794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582838 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1582838 : Nat := 118140960795 + 1582838 * 2 ^ 59
def prefixEnd_1582838 : Nat := 4983230072969 + 3 ^ 40 * 1582838 * 2
def baseEnd_1582838 : Nat := 812756692201383372745667

theorem tailTrace_1582838 : CollatzResearch.WordTrace tailWord_1582838 prefixEnd_1582838 812756692201383372745667 := by
  unfold tailWord_1582838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608177789978483003353823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38487229759770485369107445 3608177789978483003353823)
  ·
    refine ⟨5412266684967724505030735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608177789978483003353823 5412266684967724505030735)
    ·
      refine ⟨8118400027451586757546103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412266684967724505030735 8118400027451586757546103)
      ·
        refine ⟨12177600041177380136319155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118400027451586757546103 12177600041177380136319155)
        ·
          refine ⟨18266400061766070204478733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12177600041177380136319155 18266400061766070204478733)
          ·
            refine ⟨6849900023162276326679525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18266400061766070204478733 6849900023162276326679525)
            ·
              refine ⟨1284356254342926811252411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6849900023162276326679525 1284356254342926811252411)
              ·
                refine ⟨1926534381514390216878617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284356254342926811252411 1926534381514390216878617)
                ·
                  refine ⟨1444900786135792662658963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926534381514390216878617 1444900786135792662658963)
                  ·
                    refine ⟨2167351179203688993988445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444900786135792662658963 2167351179203688993988445)
                    ·
                      refine ⟨812756692201383372745667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167351179203688993988445 812756692201383372745667)
                      ·
                        rfl

theorem cell23_1582838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1582838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582838 prefixEnd_1582838 := by exact prefixLift 1582838
  have htrace : WordTrace (prefixWord ++ tailWord_1582838) baseStart_1582838 baseEnd_1582838 := by
    simpa [prefixWord, tailWord_1582838, baseEnd_1582838] using wordTrace_append hprefix tailTrace_1582838
  have hstable : (prefixWord ++ tailWord_1582838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582838).length < 2 ^ (prefixWord ++ tailWord_1582838).sum := by decide
  have hdescent : baseEnd_1582838 < baseStart_1582838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582844 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_1582844 : Nat := 118140960795 + 1582844 * 2 ^ 59
def prefixEnd_1582844 : Nat := 4983230072969 + 3 ^ 40 * 1582844 * 2
def baseEnd_1582844 : Nat := 812759773085310349270639

theorem tailTrace_1582844 : CollatzResearch.WordTrace tailWord_1582844 prefixEnd_1582844 812759773085310349270639 := by
  unfold tailWord_1582844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28865531738816995539189793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38487375651755994052253057 28865531738816995539189793)
  ·
    refine ⟨21649148804112746654392345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28865531738816995539189793 21649148804112746654392345)
    ·
      refine ⟨16236861603084559990794259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21649148804112746654392345 16236861603084559990794259)
      ·
        refine ⟨24355292404626839986191389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16236861603084559990794259 24355292404626839986191389)
        ·
          refine ⟨9133234651735064994821771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24355292404626839986191389 9133234651735064994821771)
          ·
            refine ⟨13699851977602597492232657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133234651735064994821771 13699851977602597492232657)
            ·
              refine ⟨10274888983201948119174493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13699851977602597492232657 10274888983201948119174493)
              ·
                refine ⟨3853083368700730544690435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10274888983201948119174493 3853083368700730544690435)
                ·
                  refine ⟨5779625053051095817035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853083368700730544690435 5779625053051095817035653)
                  ·
                    refine ⟨1083679697447080465694185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5779625053051095817035653 1083679697447080465694185)
                    ·
                      refine ⟨812759773085310349270639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083679697447080465694185 812759773085310349270639)
                      ·
                        rfl

theorem cell23_1582844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_1582844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582844 prefixEnd_1582844 := by exact prefixLift 1582844
  have htrace : WordTrace (prefixWord ++ tailWord_1582844) baseStart_1582844 baseEnd_1582844 := by
    simpa [prefixWord, tailWord_1582844, baseEnd_1582844] using wordTrace_append hprefix tailTrace_1582844
  have hstable : (prefixWord ++ tailWord_1582844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582844).length < 2 ^ (prefixWord ++ tailWord_1582844).sum := by decide
  have hdescent : baseEnd_1582844 < baseStart_1582844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582917 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1582917 : Nat := 118140960795 + 1582917 * 2 ^ 59
def prefixEnd_1582917 : Nat := 4983230072969 + 3 ^ 40 * 1582917 * 2
def baseEnd_1582917 : Nat := 812797257173088563657803

theorem tailTrace_1582917 : CollatzResearch.WordTrace tailWord_1582917 prefixEnd_1582917 812797257173088563657803 := by
  unfold tailWord_1582917
  simp only [CollatzResearch.WordTrace]
  refine ⟨57733726006369524545787005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38489150670913016363858003 57733726006369524545787005)
  ·
    refine ⟨21650147252388571704670127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57733726006369524545787005 21650147252388571704670127)
    ·
      refine ⟨32475220878582857557005191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21650147252388571704670127 32475220878582857557005191)
      ·
        refine ⟨48712831317874286335507787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32475220878582857557005191 48712831317874286335507787)
        ·
          refine ⟨73069246976811429503261681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48712831317874286335507787 73069246976811429503261681)
          ·
            refine ⟨54801935232608572127446261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73069246976811429503261681 54801935232608572127446261)
            ·
              refine ⟨5137681428057053636948087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54801935232608572127446261 5137681428057053636948087)
              ·
                refine ⟨7706522142085580455422131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137681428057053636948087 7706522142085580455422131)
                ·
                  refine ⟨11559783213128370683133197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7706522142085580455422131 11559783213128370683133197)
                  ·
                    refine ⟨4334918704923139006174949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11559783213128370683133197 4334918704923139006174949)
                    ·
                      refine ⟨812797257173088563657803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4334918704923139006174949 812797257173088563657803)
                      ·
                        rfl

theorem cell23_1582917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1582917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582917 prefixEnd_1582917 := by exact prefixLift 1582917
  have htrace : WordTrace (prefixWord ++ tailWord_1582917) baseStart_1582917 baseEnd_1582917 := by
    simpa [prefixWord, tailWord_1582917, baseEnd_1582917] using wordTrace_append hprefix tailTrace_1582917
  have hstable : (prefixWord ++ tailWord_1582917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582917).length < 2 ^ (prefixWord ++ tailWord_1582917).sum := by decide
  have hdescent : baseEnd_1582917 < baseStart_1582917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582918 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1582918 : Nat := 118140960795 + 1582918 * 2 ^ 59
def prefixEnd_1582918 : Nat := 4983230072969 + 3 ^ 40 * 1582918 * 2
def baseEnd_1582918 : Nat := 90310863405971451082811

theorem tailTrace_1582918 : CollatzResearch.WordTrace tailWord_1582918 prefixEnd_1582918 90310863405971451082811 := by
  unfold tailWord_1582918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804180077480184428642919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38489174986243934477715605 1804180077480184428642919)
  ·
    refine ⟨2706270116220276642964379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1804180077480184428642919 2706270116220276642964379)
    ·
      refine ⟨4059405174330414964446569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706270116220276642964379 4059405174330414964446569)
      ·
        refine ⟨3044553880747811223334927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059405174330414964446569 3044553880747811223334927)
        ·
          refine ⟨4566830821121716835002391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044553880747811223334927 4566830821121716835002391)
          ·
            refine ⟨6850246231682575252503587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566830821121716835002391 6850246231682575252503587)
            ·
              refine ⟨10275369347523862878755381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850246231682575252503587 10275369347523862878755381)
              ·
                refine ⟨963315876330362144883317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10275369347523862878755381 963315876330362144883317)
                ·
                  refine ⟨90310863405971451082811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 963315876330362144883317 90310863405971451082811)
                  ·
                    rfl

theorem cell23_1582918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1582918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582918 prefixEnd_1582918 := by exact prefixLift 1582918
  have htrace : WordTrace (prefixWord ++ tailWord_1582918) baseStart_1582918 baseEnd_1582918 := by
    simpa [prefixWord, tailWord_1582918, baseEnd_1582918] using wordTrace_append hprefix tailTrace_1582918
  have hstable : (prefixWord ++ tailWord_1582918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582918).length < 2 ^ (prefixWord ++ tailWord_1582918).sum := by decide
  have hdescent : baseEnd_1582918 < baseStart_1582918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582944 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_1582944 : Nat := 118140960795 + 1582944 * 2 ^ 59
def prefixEnd_1582944 : Nat := 4983230072969 + 3 ^ 40 * 1582944 * 2
def baseEnd_1582944 : Nat := 270937040383586652673393

theorem tailTrace_1582944 : CollatzResearch.WordTrace tailWord_1582944 prefixEnd_1582944 270937040383586652673393 := by
  unfold tailWord_1582944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867355388635854078509943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38489807184847805438013257 28867355388635854078509943)
  ·
    refine ⟨43301033082953781117764915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28867355388635854078509943 43301033082953781117764915)
    ·
      refine ⟨64951549624430671676647373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43301033082953781117764915 64951549624430671676647373)
      ·
        refine ⟨24356831109161501878742765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64951549624430671676647373 24356831109161501878742765)
        ·
          refine ⟨9133811665935563204528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24356831109161501878742765 9133811665935563204528537)
          ·
            refine ⟨6850358749451672403396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9133811665935563204528537 6850358749451672403396403)
            ·
              refine ⟨10275538124177508605094605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850358749451672403396403 10275538124177508605094605)
              ·
                refine ⟨3853326796566565726910477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10275538124177508605094605 3853326796566565726910477)
                ·
                  refine ⟨1444997548712462147591429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3853326796566565726910477 1444997548712462147591429)
                  ·
                    refine ⟨270937040383586652673393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444997548712462147591429 270937040383586652673393)
                    ·
                      rfl

theorem cell23_1582944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_1582944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582944 prefixEnd_1582944 := by exact prefixLift 1582944
  have htrace : WordTrace (prefixWord ++ tailWord_1582944) baseStart_1582944 baseEnd_1582944 := by
    simpa [prefixWord, tailWord_1582944, baseEnd_1582944] using wordTrace_append hprefix tailTrace_1582944
  have hstable : (prefixWord ++ tailWord_1582944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582944).length < 2 ^ (prefixWord ++ tailWord_1582944).sum := by decide
  have hdescent : baseEnd_1582944 < baseStart_1582944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582987 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 5, 5]
def baseStart_1582987 : Nat := 118140960795 + 1582987 * 2 ^ 59
def prefixEnd_1582987 : Nat := 4983230072969 + 3 ^ 40 * 1582987 * 2
def baseEnd_1582987 : Nat := 270944400272967763260827

theorem tailTrace_1582987 : CollatzResearch.WordTrace tailWord_1582987 prefixEnd_1582987 270944400272967763260827 := by
  unfold tailWord_1582987
  simp only [CollatzResearch.WordTrace]
  refine ⟨57736279116115926500835215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38490852744077284333890143 57736279116115926500835215)
  ·
    refine ⟨86604418674173889751252823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57736279116115926500835215 86604418674173889751252823)
    ·
      refine ⟨129906628011260834626879235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86604418674173889751252823 129906628011260834626879235)
      ·
        refine ⟨194859942016891251940318853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129906628011260834626879235 194859942016891251940318853)
        ·
          refine ⟨36536239128167109738809785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194859942016891251940318853 36536239128167109738809785)
          ·
            refine ⟨27402179346125332304107339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36536239128167109738809785 27402179346125332304107339)
            ·
              refine ⟨41103269019187998456161009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27402179346125332304107339 41103269019187998456161009)
              ·
                refine ⟨30827451764390998842120757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41103269019187998456161009 30827451764390998842120757)
                ·
                  refine ⟨2890073602911656141448821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30827451764390998842120757 2890073602911656141448821)
                  ·
                    refine ⟨270944400272967763260827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2890073602911656141448821 270944400272967763260827)
                    ·
                      rfl

theorem cell23_1582987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].length) (baseStart_1582987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1582987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1582987 prefixEnd_1582987 := by exact prefixLift 1582987
  have htrace : WordTrace (prefixWord ++ tailWord_1582987) baseStart_1582987 baseEnd_1582987 := by
    simpa [prefixWord, tailWord_1582987, baseEnd_1582987] using wordTrace_append hprefix tailTrace_1582987
  have hstable : (prefixWord ++ tailWord_1582987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582987).length < 2 ^ (prefixWord ++ tailWord_1582987).sum := by decide
  have hdescent : baseEnd_1582987 < baseStart_1582987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583001 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_1583001 : Nat := 118140960795 + 1583001 * 2 ^ 59
def prefixEnd_1583001 : Nat := 4983230072969 + 3 ^ 40 * 1583001 * 2
def baseEnd_1583001 : Nat := 812840389548066235007417

theorem tailTrace_1583001 : CollatzResearch.WordTrace tailWord_1583001 prefixEnd_1583001 812840389548066235007417 := by
  unfold tailWord_1583001
  simp only [CollatzResearch.WordTrace]
  refine ⟨57736789738065206891844857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38491193158710137927896571 57736789738065206891844857)
  ·
    refine ⟨43302592303548905168883643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57736789738065206891844857 43302592303548905168883643)
    ·
      refine ⟨64953888455323357753325465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43302592303548905168883643 64953888455323357753325465)
      ·
        refine ⟨48715416341492518314994099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64953888455323357753325465 48715416341492518314994099)
        ·
          refine ⟨73073124512238777472491149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48715416341492518314994099 73073124512238777472491149)
          ·
            refine ⟨27402421692089541552184181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73073124512238777472491149 27402421692089541552184181)
            ·
              refine ⟨2568977033633394520517267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27402421692089541552184181 2568977033633394520517267)
              ·
                refine ⟨3853465550450091780775901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568977033633394520517267 3853465550450091780775901)
                ·
                  refine ⟨1445049581418784417790963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3853465550450091780775901 1445049581418784417790963)
                  ·
                    refine ⟨2167574372128176626686445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445049581418784417790963 2167574372128176626686445)
                    ·
                      refine ⟨812840389548066235007417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167574372128176626686445 812840389548066235007417)
                      ·
                        rfl

theorem cell23_1583001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_1583001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583001 prefixEnd_1583001 := by exact prefixLift 1583001
  have htrace : WordTrace (prefixWord ++ tailWord_1583001) baseStart_1583001 baseEnd_1583001 := by
    simpa [prefixWord, tailWord_1583001, baseEnd_1583001] using wordTrace_append hprefix tailTrace_1583001
  have hstable : (prefixWord ++ tailWord_1583001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583001).length < 2 ^ (prefixWord ++ tailWord_1583001).sum := by decide
  have hdescent : baseEnd_1583001 < baseStart_1583001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583022 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1583022 : Nat := 118140960795 + 1583022 * 2 ^ 59
def prefixEnd_1583022 : Nat := 4983230072969 + 3 ^ 40 * 1583022 * 2
def baseEnd_1583022 : Nat := 812851172641810652844821

theorem tailTrace_1583022 : CollatzResearch.WordTrace tailWord_1583022 prefixEnd_1583022 812851172641810652844821 := by
  unfold tailWord_1583022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217194458873640934794915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38491703780659418318906213 7217194458873640934794915)
  ·
    refine ⟨10825791688310461402192373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217194458873640934794915 10825791688310461402192373)
    ·
      refine ⟨1014917970779105756455535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10825791688310461402192373 1014917970779105756455535)
      ·
        refine ⟨1522376956168658634683303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014917970779105756455535 1522376956168658634683303)
        ·
          refine ⟨2283565434252987952024955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522376956168658634683303 2283565434252987952024955)
          ·
            refine ⟨3425348151379481928037433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283565434252987952024955 3425348151379481928037433)
            ·
              refine ⟨2569011113534611446028075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425348151379481928037433 2569011113534611446028075)
              ·
                refine ⟨3853516670301917169042113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569011113534611446028075 3853516670301917169042113)
                ·
                  refine ⟨2890137502726437876781585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853516670301917169042113 2890137502726437876781585)
                  ·
                    refine ⟨2167603127044828407586189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890137502726437876781585 2167603127044828407586189)
                    ·
                      refine ⟨812851172641810652844821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167603127044828407586189 812851172641810652844821)
                      ·
                        rfl

theorem cell23_1583022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1583022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583022 prefixEnd_1583022 := by exact prefixLift 1583022
  have htrace : WordTrace (prefixWord ++ tailWord_1583022) baseStart_1583022 baseEnd_1583022 := by
    simpa [prefixWord, tailWord_1583022, baseEnd_1583022] using wordTrace_append hprefix tailTrace_1583022
  have hstable : (prefixWord ++ tailWord_1583022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583022).length < 2 ^ (prefixWord ++ tailWord_1583022).sum := by decide
  have hdescent : baseEnd_1583022 < baseStart_1583022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583034 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_1583034 : Nat := 118140960795 + 1583034 * 2 ^ 59
def prefixEnd_1583034 : Nat := 4983230072969 + 3 ^ 40 * 1583034 * 2
def baseEnd_1583034 : Nat := 270952444803221535298255

theorem tailTrace_1583034 : CollatzResearch.WordTrace tailWord_1583034 prefixEnd_1583034 270952444803221535298255 := by
  unfold tailWord_1583034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434498336736413381949039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38491995564630435685197437 14434498336736413381949039)
  ·
    refine ⟨21651747505104620072923559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14434498336736413381949039 21651747505104620072923559)
    ·
      refine ⟨32477621257656930109385339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21651747505104620072923559 32477621257656930109385339)
      ·
        refine ⟨48716431886485395164078009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32477621257656930109385339 48716431886485395164078009)
        ·
          refine ⟨36537323914864046373058507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48716431886485395164078009 36537323914864046373058507)
          ·
            refine ⟨54805985872296069559587761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537323914864046373058507 54805985872296069559587761)
            ·
              refine ⟨41104489404222052169690821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54805985872296069559587761 41104489404222052169690821)
              ·
                refine ⟨7707091763291634781817029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41104489404222052169690821 7707091763291634781817029)
                ·
                  refine ⟨1445079705617181521590693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7707091763291634781817029 1445079705617181521590693)
                  ·
                    refine ⟨270952444803221535298255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445079705617181521590693 270952444803221535298255)
                    ·
                      rfl

theorem cell23_1583034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_1583034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583034 prefixEnd_1583034 := by exact prefixLift 1583034
  have htrace : WordTrace (prefixWord ++ tailWord_1583034) baseStart_1583034 baseEnd_1583034 := by
    simpa [prefixWord, tailWord_1583034, baseEnd_1583034] using wordTrace_append hprefix tailTrace_1583034
  have hstable : (prefixWord ++ tailWord_1583034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583034).length < 2 ^ (prefixWord ++ tailWord_1583034).sum := by decide
  have hdescent : baseEnd_1583034 < baseStart_1583034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583038 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1583038 : Nat := 118140960795 + 1583038 * 2 ^ 59
def prefixEnd_1583038 : Nat := 4983230072969 + 3 ^ 40 * 1583038 * 2
def baseEnd_1583038 : Nat := 270953129444094196748249

theorem tailTrace_1583038 : CollatzResearch.WordTrace tailWord_1583038 prefixEnd_1583038 270953129444094196748249 := by
  unfold tailWord_1583038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217267404866395276367721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38492092825954108140627845 7217267404866395276367721)
  ·
    refine ⟨5412950553649796457275791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7217267404866395276367721 5412950553649796457275791)
    ·
      refine ⟨8119425830474694685913687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412950553649796457275791 8119425830474694685913687)
      ·
        refine ⟨12179138745712042028870531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119425830474694685913687 12179138745712042028870531)
        ·
          refine ⟨18268708118568063043305797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12179138745712042028870531 18268708118568063043305797)
          ·
            refine ⟨3425382772231511820619837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18268708118568063043305797 3425382772231511820619837)
            ·
              refine ⟨1284518539586816932732439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3425382772231511820619837 1284518539586816932732439)
              ·
                refine ⟨1926777809380225399098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284518539586816932732439 1926777809380225399098659)
                ·
                  refine ⟨2890166714070338098647989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926777809380225399098659 2890166714070338098647989)
                  ·
                    refine ⟨270953129444094196748249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2890166714070338098647989 270953129444094196748249)
                    ·
                      rfl

theorem cell23_1583038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1583038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583038 prefixEnd_1583038 := by exact prefixLift 1583038
  have htrace : WordTrace (prefixWord ++ tailWord_1583038) baseStart_1583038 baseEnd_1583038 := by
    simpa [prefixWord, tailWord_1583038, baseEnd_1583038] using wordTrace_append hprefix tailTrace_1583038
  have hstable : (prefixWord ++ tailWord_1583038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583038).length < 2 ^ (prefixWord ++ tailWord_1583038).sum := by decide
  have hdescent : baseEnd_1583038 < baseStart_1583038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583051 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 2, 4]
def baseStart_1583051 : Nat := 118140960795 + 1583051 * 2 ^ 59
def prefixEnd_1583051 : Nat := 4983230072969 + 3 ^ 40 * 1583051 * 2
def baseEnd_1583051 : Nat := 270955354526930346460729

theorem tailTrace_1583051 : CollatzResearch.WordTrace tailWord_1583051 prefixEnd_1583051 270955354526930346460729 := by
  unfold tailWord_1583051
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738613387884065431165007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492408925256043620776671 57738613387884065431165007)
  ·
    refine ⟨86607920081826098146747511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57738613387884065431165007 86607920081826098146747511)
    ·
      refine ⟨129911880122739147220121267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86607920081826098146747511 129911880122739147220121267)
      ·
        refine ⟨194867820184108720830181901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129911880122739147220121267 194867820184108720830181901)
        ·
          refine ⟨73075432569040770311318213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194867820184108720830181901 73075432569040770311318213)
          ·
            refine ⟨13701643606695144433372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73075432569040770311318213 13701643606695144433372165)
            ·
              refine ⟨2569058176255339581257281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13701643606695144433372165 2569058176255339581257281)
              ·
                refine ⟨1926793632191504685942961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569058176255339581257281 1926793632191504685942961)
                ·
                  refine ⟨1445095224143628514457221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926793632191504685942961 1445095224143628514457221)
                  ·
                    refine ⟨270955354526930346460729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445095224143628514457221 270955354526930346460729)
                    ·
                      rfl

theorem cell23_1583051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 4].length) (baseStart_1583051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583051 prefixEnd_1583051 := by exact prefixLift 1583051
  have htrace : WordTrace (prefixWord ++ tailWord_1583051) baseStart_1583051 baseEnd_1583051 := by
    simpa [prefixWord, tailWord_1583051, baseEnd_1583051] using wordTrace_append hprefix tailTrace_1583051
  have hstable : (prefixWord ++ tailWord_1583051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583051).length < 2 ^ (prefixWord ++ tailWord_1583051).sum := by decide
  have hdescent : baseEnd_1583051 < baseStart_1583051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583052 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1583052 : Nat := 118140960795 + 1583052 * 2 ^ 59
def prefixEnd_1583052 : Nat := 4983230072969 + 3 ^ 40 * 1583052 * 2
def baseEnd_1583052 : Nat := 812866577061445535469683

theorem tailTrace_1583052 : CollatzResearch.WordTrace tailWord_1583052 prefixEnd_1583052 812866577061445535469683 := by
  unfold tailWord_1583052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28869324930440221300975705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38492433240586961734634273 28869324930440221300975705)
  ·
    refine ⟨21651993697830165975731779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28869324930440221300975705 21651993697830165975731779)
    ·
      refine ⟨32477990546745248963597669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21651993697830165975731779 32477990546745248963597669)
      ·
        refine ⟨6089623227514734180674563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32477990546745248963597669 6089623227514734180674563)
        ·
          refine ⟨9134434841272101271011845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089623227514734180674563 9134434841272101271011845)
          ·
            refine ⟨1712706532738518988314721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9134434841272101271011845 1712706532738518988314721)
            ·
              refine ⟨1284529899553889241236041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712706532738518988314721 1284529899553889241236041)
              ·
                refine ⟨963397424665416930927031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284529899553889241236041 963397424665416930927031)
                ·
                  refine ⟨1445096136998125396390547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963397424665416930927031 1445096136998125396390547)
                  ·
                    refine ⟨2167644205497188094585821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445096136998125396390547 2167644205497188094585821)
                    ·
                      refine ⟨812866577061445535469683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167644205497188094585821 812866577061445535469683)
                      ·
                        rfl

theorem cell23_1583052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1583052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583052 prefixEnd_1583052 := by exact prefixLift 1583052
  have htrace : WordTrace (prefixWord ++ tailWord_1583052) baseStart_1583052 baseEnd_1583052 := by
    simpa [prefixWord, tailWord_1583052, baseEnd_1583052] using wordTrace_append hprefix tailTrace_1583052
  have hstable : (prefixWord ++ tailWord_1583052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583052).length < 2 ^ (prefixWord ++ tailWord_1583052).sum := by decide
  have hdescent : baseEnd_1583052 < baseStart_1583052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583054 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1583054 : Nat := 118140960795 + 1583054 * 2 ^ 59
def prefixEnd_1583054 : Nat := 4983230072969 + 3 ^ 40 * 1583054 * 2
def baseEnd_1583054 : Nat := 812867604022754527644673

theorem tailTrace_1583054 : CollatzResearch.WordTrace tailWord_1583054 prefixEnd_1583054 812867604022754527644673 := by
  unfold tailWord_1583054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217340350859149617940527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38492481871248797962349477 7217340350859149617940527)
  ·
    refine ⟨10826010526288724426910791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217340350859149617940527 10826010526288724426910791)
    ·
      refine ⟨16239015789433086640366187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10826010526288724426910791 16239015789433086640366187)
      ·
        refine ⟨24358523684149629960549281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16239015789433086640366187 24358523684149629960549281)
        ·
          refine ⟨18268892763112222470411961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24358523684149629960549281 18268892763112222470411961)
          ·
            refine ⟨13701669572334166852808971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18268892763112222470411961 13701669572334166852808971)
            ·
              refine ⟨20552504358501250279213457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13701669572334166852808971 20552504358501250279213457)
              ·
                refine ⟨15414378268875937709410093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20552504358501250279213457 15414378268875937709410093)
                ·
                  refine ⟨5780391850828476641028785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15414378268875937709410093 5780391850828476641028785)
                  ·
                    refine ⟨4335293888121357480771589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780391850828476641028785 4335293888121357480771589)
                    ·
                      refine ⟨812867604022754527644673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4335293888121357480771589 812867604022754527644673)
                      ·
                        rfl

theorem cell23_1583054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1583054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583054 prefixEnd_1583054 := by exact prefixLift 1583054
  have htrace : WordTrace (prefixWord ++ tailWord_1583054) baseStart_1583054 baseEnd_1583054 := by
    simpa [prefixWord, tailWord_1583054, baseEnd_1583054] using wordTrace_append hprefix tailTrace_1583054
  have hstable : (prefixWord ++ tailWord_1583054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583054).length < 2 ^ (prefixWord ++ tailWord_1583054).sum := by decide
  have hdescent : baseEnd_1583054 < baseStart_1583054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583057 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1583057 : Nat := 118140960795 + 1583057 * 2 ^ 59
def prefixEnd_1583057 : Nat := 4983230072969 + 3 ^ 40 * 1583057 * 2
def baseEnd_1583057 : Nat := 812869144464718015907159

theorem tailTrace_1583057 : CollatzResearch.WordTrace tailWord_1583057 prefixEnd_1583057 812869144464718015907159 := by
  unfold tailWord_1583057
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738832225862328455883425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492554817241552303922283 57738832225862328455883425)
  ·
    refine ⟨43304124169396746341912569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57738832225862328455883425 43304124169396746341912569)
    ·
      refine ⟨32478093127047559756434427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43304124169396746341912569 32478093127047559756434427)
      ·
        refine ⟨48717139690571339634651641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32478093127047559756434427 48717139690571339634651641)
        ·
          refine ⟨36537854767928504725988731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48717139690571339634651641 36537854767928504725988731)
          ·
            refine ⟨54806782151892757088983097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537854767928504725988731 54806782151892757088983097)
            ·
              refine ⟨41105086613919567816737323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54806782151892757088983097 41105086613919567816737323)
              ·
                refine ⟨61657629920879351725105985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41105086613919567816737323 61657629920879351725105985)
                ·
                  refine ⟨46243222440659513793829489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61657629920879351725105985 46243222440659513793829489)
                  ·
                    refine ⟨34682416830494635345372117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46243222440659513793829489 34682416830494635345372117)
                    ·
                      refine ⟨812869144464718015907159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34682416830494635345372117 812869144464718015907159)
                      ·
                        rfl

theorem cell23_1583057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1583057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583057 prefixEnd_1583057 := by exact prefixLift 1583057
  have htrace : WordTrace (prefixWord ++ tailWord_1583057) baseStart_1583057 baseEnd_1583057 := by
    simpa [prefixWord, tailWord_1583057, baseEnd_1583057] using wordTrace_append hprefix tailTrace_1583057
  have hstable : (prefixWord ++ tailWord_1583057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583057).length < 2 ^ (prefixWord ++ tailWord_1583057).sum := by decide
  have hdescent : baseEnd_1583057 < baseStart_1583057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583061 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1583061 : Nat := 118140960795 + 1583061 * 2 ^ 59
def prefixEnd_1583061 : Nat := 4983230072969 + 3 ^ 40 * 1583061 * 2
def baseEnd_1583061 : Nat := 812871198387336000257141

theorem tailTrace_1583061 : CollatzResearch.WordTrace tailWord_1583061 prefixEnd_1583061 812871198387336000257141 := by
  unfold tailWord_1583061
  simp only [CollatzResearch.WordTrace]
  refine ⟨57738978117847837139029037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492652078565224759352691 57738978117847837139029037)
  ·
    refine ⟨21652116794192938927135889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57738978117847837139029037 21652116794192938927135889)
    ·
      refine ⟨16239087595644704195351917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21652116794192938927135889 16239087595644704195351917)
      ·
        refine ⟨6089657848366764073256969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16239087595644704195351917 6089657848366764073256969)
        ·
          refine ⟨4567243386275073054942727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089657848366764073256969 4567243386275073054942727)
          ·
            refine ⟨6850865079412609582414091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567243386275073054942727 6850865079412609582414091)
            ·
              refine ⟨10276297619118914373621137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850865079412609582414091 10276297619118914373621137)
              ·
                refine ⟨7707223214339185780215853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10276297619118914373621137 7707223214339185780215853)
                ·
                  refine ⟨2890208705377194667580945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7707223214339185780215853 2890208705377194667580945)
                  ·
                    refine ⟨2167656529032896000685709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890208705377194667580945 2167656529032896000685709)
                    ·
                      refine ⟨812871198387336000257141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167656529032896000685709 812871198387336000257141)
                      ·
                        rfl

theorem cell23_1583061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1583061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583061 prefixEnd_1583061 := by exact prefixLift 1583061
  have htrace : WordTrace (prefixWord ++ tailWord_1583061) baseStart_1583061 baseEnd_1583061 := by
    simpa [prefixWord, tailWord_1583061, baseEnd_1583061] using wordTrace_append hprefix tailTrace_1583061
  have hstable : (prefixWord ++ tailWord_1583061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583061).length < 2 ^ (prefixWord ++ tailWord_1583061).sum := by decide
  have hdescent : baseEnd_1583061 < baseStart_1583061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583071 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1583071 : Nat := 118140960795 + 1583071 * 2 ^ 59
def prefixEnd_1583071 : Nat := 4983230072969 + 3 ^ 40 * 1583071 * 2
def baseEnd_1583071 : Nat := 812876333193880961132095

theorem tailTrace_1583071 : CollatzResearch.WordTrace tailWord_1583071 prefixEnd_1583071 812876333193880961132095 := by
  unfold tailWord_1583071
  simp only [CollatzResearch.WordTrace]
  refine ⟨57739342847811608846893067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492895231874405897928711 57739342847811608846893067)
  ·
    refine ⟨86609014271717413270339601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57739342847811608846893067 86609014271717413270339601)
    ·
      refine ⟨64956760703788059952754701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86609014271717413270339601 64956760703788059952754701)
      ·
        refine ⟨24358785263920522482283013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64956760703788059952754701 24358785263920522482283013)
        ·
          refine ⟨4567272236985097965428065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24358785263920522482283013 4567272236985097965428065)
          ·
            refine ⟨3425454177738823474071049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567272236985097965428065 3425454177738823474071049)
            ·
              refine ⟨2569090633304117605553287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425454177738823474071049 2569090633304117605553287)
              ·
                refine ⟨3853635949956176408329931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569090633304117605553287 3853635949956176408329931)
                ·
                  refine ⟨5780453924934264612494897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853635949956176408329931 5780453924934264612494897)
                  ·
                    refine ⟨4335340443700698459371173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5780453924934264612494897 4335340443700698459371173)
                    ·
                      refine ⟨812876333193880961132095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4335340443700698459371173 812876333193880961132095)
                      ·
                        rfl

theorem cell23_1583071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1583071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583071 prefixEnd_1583071 := by exact prefixLift 1583071
  have htrace : WordTrace (prefixWord ++ tailWord_1583071) baseStart_1583071 baseEnd_1583071 := by
    simpa [prefixWord, tailWord_1583071, baseEnd_1583071] using wordTrace_append hprefix tailTrace_1583071
  have hstable : (prefixWord ++ tailWord_1583071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583071).length < 2 ^ (prefixWord ++ tailWord_1583071).sum := by decide
  have hdescent : baseEnd_1583071 < baseStart_1583071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583125 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_1583125 : Nat := 118140960795 + 1583125 * 2 ^ 59
def prefixEnd_1583125 : Nat := 4983230072969 + 3 ^ 40 * 1583125 * 2
def baseEnd_1583125 : Nat := 812904061149223749856847

theorem tailTrace_1583125 : CollatzResearch.WordTrace tailWord_1583125 prefixEnd_1583125 812904061149223749856847 := by
  unfold tailWord_1583125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57741312389615976069358829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38494208259743984046239219 57741312389615976069358829)
  ·
    refine ⟨21652992146105991026009561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57741312389615976069358829 21652992146105991026009561)
    ·
      refine ⟨16239744109579493269507171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21652992146105991026009561 16239744109579493269507171)
      ·
        refine ⟨24359616164369239904260757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16239744109579493269507171 24359616164369239904260757)
        ·
          refine ⟨1141857007704808120512223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24359616164369239904260757 1141857007704808120512223)
          ·
            refine ⟨1712785511557212180768335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141857007704808120512223 1712785511557212180768335)
            ·
              refine ⟨2569178267335818271152503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712785511557212180768335 2569178267335818271152503)
              ·
                refine ⟨3853767401003727406728755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569178267335818271152503 3853767401003727406728755)
                ·
                  refine ⟨5780651101505591110093133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853767401003727406728755 5780651101505591110093133)
                  ·
                    refine ⟨2167744163064596666284925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5780651101505591110093133 2167744163064596666284925)
                    ·
                      refine ⟨812904061149223749856847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167744163064596666284925 812904061149223749856847)
                      ·
                        rfl

theorem cell23_1583125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_1583125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583125 prefixEnd_1583125 := by exact prefixLift 1583125
  have htrace : WordTrace (prefixWord ++ tailWord_1583125) baseStart_1583125 baseEnd_1583125 := by
    simpa [prefixWord, tailWord_1583125, baseEnd_1583125] using wordTrace_append hprefix tailTrace_1583125
  have hstable : (prefixWord ++ tailWord_1583125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583125).length < 2 ^ (prefixWord ++ tailWord_1583125).sum := by decide
  have hdescent : baseEnd_1583125 < baseStart_1583125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583131 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 4, 2]
def baseStart_1583131 : Nat := 118140960795 + 1583131 * 2 ^ 59
def prefixEnd_1583131 : Nat := 4983230072969 + 3 ^ 40 * 1583131 * 2
def baseEnd_1583131 : Nat := 812907142033150726381819

theorem tailTrace_1583131 : CollatzResearch.WordTrace tailWord_1583131 prefixEnd_1583131 812907142033150726381819 := by
  unfold tailWord_1583131
  simp only [CollatzResearch.WordTrace]
  refine ⟨57741531227594239094077247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38494354151729492729384831 57741531227594239094077247)
  ·
    refine ⟨86612296841391358641115871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57741531227594239094077247 86612296841391358641115871)
    ·
      refine ⟨129918445262087037961673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86612296841391358641115871 129918445262087037961673807)
      ·
        refine ⟨194877667893130556942510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129918445262087037961673807 194877667893130556942510711)
        ·
          refine ⟨292316501839695835413766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194877667893130556942510711 292316501839695835413766067)
          ·
            refine ⟨438474752759543753120649101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292316501839695835413766067 438474752759543753120649101)
            ·
              refine ⟨164428032284828907420243413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438474752759543753120649101 164428032284828907420243413)
              ·
                refine ⟨3853782006675677517661955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 164428032284828907420243413 3853782006675677517661955)
                ·
                  refine ⟨5780673010013516276492933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3853782006675677517661955 5780673010013516276492933)
                  ·
                    refine ⟨1083876189377534301842425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780673010013516276492933 1083876189377534301842425)
                    ·
                      refine ⟨812907142033150726381819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083876189377534301842425 812907142033150726381819)
                      ·
                        rfl

theorem cell23_1583131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4, 2].length) (baseStart_1583131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583131 prefixEnd_1583131 := by exact prefixLift 1583131
  have htrace : WordTrace (prefixWord ++ tailWord_1583131) baseStart_1583131 baseEnd_1583131 := by
    simpa [prefixWord, tailWord_1583131, baseEnd_1583131] using wordTrace_append hprefix tailTrace_1583131
  have hstable : (prefixWord ++ tailWord_1583131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583131).length < 2 ^ (prefixWord ++ tailWord_1583131).sum := by decide
  have hdescent : baseEnd_1583131 < baseStart_1583131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583164 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1583164 : Nat := 118140960795 + 1583164 * 2 ^ 59
def prefixEnd_1583164 : Nat := 4983230072969 + 3 ^ 40 * 1583164 * 2
def baseEnd_1583164 : Nat := 812924086894749097269167

theorem tailTrace_1583164 : CollatzResearch.WordTrace tailWord_1583164 prefixEnd_1583164 812924086894749097269167 := by
  unfold tailWord_1583164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28871367418237342865014273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38495156557649790486685697 28871367418237342865014273)
  ·
    refine ⟨21653525563678007148760705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28871367418237342865014273 21653525563678007148760705)
    ·
      refine ⟨16240144172758505361570529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21653525563678007148760705 16240144172758505361570529)
      ·
        refine ⟨12180108129568879021177897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16240144172758505361570529 12180108129568879021177897)
        ·
          refine ⟨9135081097176659265883423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12180108129568879021177897 9135081097176659265883423)
          ·
            refine ⟨13702621645764988898825135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135081097176659265883423 13702621645764988898825135)
            ·
              refine ⟨20553932468647483348237703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13702621645764988898825135 20553932468647483348237703)
              ·
                refine ⟨30830898702971225022356555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20553932468647483348237703 30830898702971225022356555)
                ·
                  refine ⟨46246348054456837533534833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30830898702971225022356555 46246348054456837533534833)
                  ·
                    refine ⟨34684761040842628150151125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46246348054456837533534833 34684761040842628150151125)
                    ·
                      refine ⟨812924086894749097269167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34684761040842628150151125 812924086894749097269167)
                      ·
                        rfl

theorem cell23_1583164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1583164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583164 prefixEnd_1583164 := by exact prefixLift 1583164
  have htrace : WordTrace (prefixWord ++ tailWord_1583164) baseStart_1583164 baseEnd_1583164 := by
    simpa [prefixWord, tailWord_1583164, baseEnd_1583164] using wordTrace_append hprefix tailTrace_1583164
  have hstable : (prefixWord ++ tailWord_1583164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583164).length < 2 ^ (prefixWord ++ tailWord_1583164).sum := by decide
  have hdescent : baseEnd_1583164 < baseStart_1583164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583165 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1583165 : Nat := 118140960795 + 1583165 * 2 ^ 59
def prefixEnd_1583165 : Nat := 4983230072969 + 3 ^ 40 * 1583165 * 2
def baseEnd_1583165 : Nat := 812924600375403593356663

theorem tailTrace_1583165 : CollatzResearch.WordTrace tailWord_1583165 prefixEnd_1583165 812924600375403593356663 := by
  unfold tailWord_1583165
  simp only [CollatzResearch.WordTrace]
  refine ⟨57742771309471062900814949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38495180872980708600543299 57742771309471062900814949)
  ·
    refine ⟨10826769620525824293902803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57742771309471062900814949 10826769620525824293902803)
    ·
      refine ⟨16240154430788736440854205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10826769620525824293902803 16240154430788736440854205)
      ·
        refine ⟨6090057911545776165320327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16240154430788736440854205 6090057911545776165320327)
        ·
          refine ⟨9135086867318664247980491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090057911545776165320327 9135086867318664247980491)
          ·
            refine ⟨13702630300977996371970737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135086867318664247980491 13702630300977996371970737)
            ·
              refine ⟨10276972725733497278978053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13702630300977996371970737 10276972725733497278978053)
              ·
                refine ⟨1926932386075030739808385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10276972725733497278978053 1926932386075030739808385)
                ·
                  refine ⟨1445199289556273054856289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926932386075030739808385 1445199289556273054856289)
                  ·
                    refine ⟨1083899467167204791142217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445199289556273054856289 1083899467167204791142217)
                    ·
                      refine ⟨812924600375403593356663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083899467167204791142217 812924600375403593356663)
                      ·
                        rfl

theorem cell23_1583165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1583165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583165 prefixEnd_1583165 := by exact prefixLift 1583165
  have htrace : WordTrace (prefixWord ++ tailWord_1583165) baseStart_1583165 baseEnd_1583165 := by
    simpa [prefixWord, tailWord_1583165, baseEnd_1583165] using wordTrace_append hprefix tailTrace_1583165
  have hstable : (prefixWord ++ tailWord_1583165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583165).length < 2 ^ (prefixWord ++ tailWord_1583165).sum := by decide
  have hdescent : baseEnd_1583165 < baseStart_1583165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583182 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_1583182 : Nat := 118140960795 + 1583182 * 2 ^ 59
def prefixEnd_1583182 : Nat := 4983230072969 + 3 ^ 40 * 1583182 * 2
def baseEnd_1583182 : Nat := 812933329546530026844085

theorem tailTrace_1583182 : CollatzResearch.WordTrace tailWord_1583182 prefixEnd_1583182 812933329546530026844085 := by
  unfold tailWord_1583182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217923918801184350522975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38495594233606316536122533 7217923918801184350522975)
  ·
    refine ⟨10826885878201776525784463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217923918801184350522975 10826885878201776525784463)
    ·
      refine ⟨16240328817302664788676695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10826885878201776525784463 16240328817302664788676695)
      ·
        refine ⟨24360493225953997183015043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16240328817302664788676695 24360493225953997183015043)
        ·
          refine ⟨36540739838930995774522565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24360493225953997183015043 36540739838930995774522565)
          ·
            refine ⟨6851388719799561707722981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36540739838930995774522565 6851388719799561707722981)
            ·
              refine ⟨1284635384962417820198059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6851388719799561707722981 1284635384962417820198059)
              ·
                refine ⟨1926953077443626730297089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284635384962417820198059 1926953077443626730297089)
                ·
                  refine ⟨1445214808082720047722817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926953077443626730297089 1445214808082720047722817)
                  ·
                    refine ⟨1083911106062040035792113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445214808082720047722817 1083911106062040035792113)
                    ·
                      refine ⟨812933329546530026844085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1083911106062040035792113 812933329546530026844085)
                      ·
                        rfl

theorem cell23_1583182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_1583182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583182 prefixEnd_1583182 := by exact prefixLift 1583182
  have htrace : WordTrace (prefixWord ++ tailWord_1583182) baseStart_1583182 baseEnd_1583182 := by
    simpa [prefixWord, tailWord_1583182, baseEnd_1583182] using wordTrace_append hprefix tailTrace_1583182
  have hstable : (prefixWord ++ tailWord_1583182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583182).length < 2 ^ (prefixWord ++ tailWord_1583182).sum := by decide
  have hdescent : baseEnd_1583182 < baseStart_1583182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583194 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1583194 : Nat := 118140960795 + 1583194 * 2 ^ 59
def prefixEnd_1583194 : Nat := 4983230072969 + 3 ^ 40 * 1583194 * 2
def baseEnd_1583194 : Nat := 812939491314383979894029

theorem tailTrace_1583194 : CollatzResearch.WordTrace tailWord_1583194 prefixEnd_1583194 812939491314383979894029 := by
  unfold tailWord_1583194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435957256591500213405159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38495886017577333902413757 14435957256591500213405159)
  ·
    refine ⟨21653935884887250320107739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14435957256591500213405159 21653935884887250320107739)
    ·
      refine ⟨32480903827330875480161609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21653935884887250320107739 32480903827330875480161609)
      ·
        refine ⟨24360677870498156610121207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32480903827330875480161609 24360677870498156610121207)
        ·
          refine ⟨36541016805747234915181811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24360677870498156610121207 36541016805747234915181811)
          ·
            refine ⟨54811525208620852372772717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36541016805747234915181811 54811525208620852372772717)
            ·
              refine ⟨20554321953232819639789769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54811525208620852372772717 20554321953232819639789769)
              ·
                refine ⟨15415741464924614729842327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20554321953232819639789769 15415741464924614729842327)
                ·
                  refine ⟨23123612197386922094763491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15415741464924614729842327 23123612197386922094763491)
                  ·
                    refine ⟨34685418296080383142145237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23123612197386922094763491 34685418296080383142145237)
                    ·
                      refine ⟨812939491314383979894029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34685418296080383142145237 812939491314383979894029)
                      ·
                        rfl

theorem cell23_1583194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1583194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583194 prefixEnd_1583194 := by exact prefixLift 1583194
  have htrace : WordTrace (prefixWord ++ tailWord_1583194) baseStart_1583194 baseEnd_1583194 := by
    simpa [prefixWord, tailWord_1583194, baseEnd_1583194] using wordTrace_append hprefix tailTrace_1583194
  have hstable : (prefixWord ++ tailWord_1583194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583194).length < 2 ^ (prefixWord ++ tailWord_1583194).sum := by decide
  have hdescent : baseEnd_1583194 < baseStart_1583194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583222 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_1583222 : Nat := 118140960795 + 1583222 * 2 ^ 59
def prefixEnd_1583222 : Nat := 4983230072969 + 3 ^ 40 * 1583222 * 2
def baseEnd_1583222 : Nat := 90328207641412207815989

theorem tailTrace_1583222 : CollatzResearch.WordTrace tailWord_1583222 prefixEnd_1583222 90328207641412207815989 := by
  unfold tailWord_1583222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609053141891535102227495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38496566846843041090426613 3609053141891535102227495)
  ·
    refine ⟨5413579712837302653341243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3609053141891535102227495 5413579712837302653341243)
    ·
      refine ⟨8120369569255953980011865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413579712837302653341243 8120369569255953980011865)
      ·
        refine ⟨6090277176941965485008899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8120369569255953980011865 6090277176941965485008899)
        ·
          refine ⟨9135415765412948227513349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090277176941965485008899 9135415765412948227513349)
          ·
            refine ⟨1712890456014927792658753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9135415765412948227513349 1712890456014927792658753)
            ·
              refine ⟨1284667842011195844494065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712890456014927792658753 1284667842011195844494065)
              ·
                refine ⟨963500881508396883370549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284667842011195844494065 963500881508396883370549)
                ·
                  refine ⟨90328207641412207815989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 963500881508396883370549 90328207641412207815989)
                  ·
                    rfl

theorem cell23_1583222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_1583222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583222 prefixEnd_1583222 := by exact prefixLift 1583222
  have htrace : WordTrace (prefixWord ++ tailWord_1583222) baseStart_1583222 baseEnd_1583222 := by
    simpa [prefixWord, tailWord_1583222, baseEnd_1583222] using wordTrace_append hprefix tailTrace_1583222
  have hstable : (prefixWord ++ tailWord_1583222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583222).length < 2 ^ (prefixWord ++ tailWord_1583222).sum := by decide
  have hdescent : baseEnd_1583222 < baseStart_1583222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583224 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1583224 : Nat := 118140960795 + 1583224 * 2 ^ 59
def prefixEnd_1583224 : Nat := 4983230072969 + 3 ^ 40 * 1583224 * 2
def baseEnd_1583224 : Nat := 812954895734018862518891

theorem tailTrace_1583224 : CollatzResearch.WordTrace tailWord_1583224 prefixEnd_1583224 812954895734018862518891 := by
  unfold tailWord_1583224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872461608128657988606363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38496615477504877318141817 28872461608128657988606363)
  ·
    refine ⟨43308692412192986982909545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28872461608128657988606363 43308692412192986982909545)
    ·
      refine ⟨32481519309144740237182159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43308692412192986982909545 32481519309144740237182159)
      ·
        refine ⟨48722278963717110355773239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32481519309144740237182159 48722278963717110355773239)
        ·
          refine ⟨73083418445575665533659859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48722278963717110355773239 73083418445575665533659859)
          ·
            refine ⟨109625127668363498300489789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73083418445575665533659859 109625127668363498300489789)
            ·
              refine ⟨41109422875636311862683671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109625127668363498300489789 41109422875636311862683671)
              ·
                refine ⟨61664134313454467794025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41109422875636311862683671 61664134313454467794025507)
                ·
                  refine ⟨92496201470181701691038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61664134313454467794025507 92496201470181701691038261)
                  ·
                    refine ⟨8671518887829534533534837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92496201470181701691038261 8671518887829534533534837)
                    ·
                      refine ⟨812954895734018862518891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8671518887829534533534837 812954895734018862518891)
                      ·
                        rfl

theorem cell23_1583224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1583224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583224 prefixEnd_1583224 := by exact prefixLift 1583224
  have htrace : WordTrace (prefixWord ++ tailWord_1583224) baseStart_1583224 baseEnd_1583224 := by
    simpa [prefixWord, tailWord_1583224, baseEnd_1583224] using wordTrace_append hprefix tailTrace_1583224
  have hstable : (prefixWord ++ tailWord_1583224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583224).length < 2 ^ (prefixWord ++ tailWord_1583224).sum := by decide
  have hdescent : baseEnd_1583224 < baseStart_1583224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583241 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_1583241 : Nat := 118140960795 + 1583241 * 2 ^ 59
def prefixEnd_1583241 : Nat := 4983230072969 + 3 ^ 40 * 1583241 * 2
def baseEnd_1583241 : Nat := 812963624905145296006313

theorem tailTrace_1583241 : CollatzResearch.WordTrace tailWord_1583241 prefixEnd_1583241 812963624905145296006313 := by
  unfold tailWord_1583241
  simp only [CollatzResearch.WordTrace]
  refine ⟨57745543257195727880581577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38497028838130485253721051 57745543257195727880581577)
  ·
    refine ⟨43309157442896795910436183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57745543257195727880581577 43309157442896795910436183)
    ·
      refine ⟨64963736164345193865654275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43309157442896795910436183 64963736164345193865654275)
      ·
        refine ⟨97445604246517790798481413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64963736164345193865654275 97445604246517790798481413)
        ·
          refine ⟨18271050796222085774715265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97445604246517790798481413 18271050796222085774715265)
          ·
            refine ⟨13703288097166564331036449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18271050796222085774715265 13703288097166564331036449)
            ·
              refine ⟨10277466072874923248277337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13703288097166564331036449 10277466072874923248277337)
              ·
                refine ⟨7708099554656192436208003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10277466072874923248277337 7708099554656192436208003)
                ·
                  refine ⟨11562149331984288654312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708099554656192436208003 11562149331984288654312005)
                  ·
                    refine ⟨2167902999747054122683501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11562149331984288654312005 2167902999747054122683501)
                    ·
                      refine ⟨812963624905145296006313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2167902999747054122683501 812963624905145296006313)
                      ·
                        rfl

theorem cell23_1583241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_1583241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583241 prefixEnd_1583241 := by exact prefixLift 1583241
  have htrace : WordTrace (prefixWord ++ tailWord_1583241) baseStart_1583241 baseEnd_1583241 := by
    simpa [prefixWord, tailWord_1583241, baseEnd_1583241] using wordTrace_append hprefix tailTrace_1583241
  have hstable : (prefixWord ++ tailWord_1583241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583241).length < 2 ^ (prefixWord ++ tailWord_1583241).sum := by decide
  have hdescent : baseEnd_1583241 < baseStart_1583241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583244 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 12]
def baseStart_1583244 : Nat := 118140960795 + 1583244 * 2 ^ 59
def prefixEnd_1583244 : Nat := 4983230072969 + 3 ^ 40 * 1583244 * 2
def baseEnd_1583244 : Nat := 90329462816345420474311

theorem tailTrace_1583244 : CollatzResearch.WordTrace tailWord_1583244 prefixEnd_1583244 90329462816345420474311 := by
  unfold tailWord_1583244
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872826338092429696470393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38497101784123239595293857 28872826338092429696470393)
  ·
    refine ⟨21654619753569322272352795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28872826338092429696470393 21654619753569322272352795)
    ·
      refine ⟨32481929630353983408529193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21654619753569322272352795 32481929630353983408529193)
      ·
        refine ⟨24361447222765487556396895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32481929630353983408529193 24361447222765487556396895)
        ·
          refine ⟨36542170834148231334595343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24361447222765487556396895 36542170834148231334595343)
          ·
            refine ⟨54813256251222347001893015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36542170834148231334595343 54813256251222347001893015)
            ·
              refine ⟨82219884376833520502839523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54813256251222347001893015 82219884376833520502839523)
              ·
                refine ⟨123329826565250280754259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82219884376833520502839523 123329826565250280754259285)
                ·
                  refine ⟨90329462816345420474311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 123329826565250280754259285 90329462816345420474311)
                  ·
                    rfl

theorem cell23_1583244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_1583244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583244 prefixEnd_1583244 := by exact prefixLift 1583244
  have htrace : WordTrace (prefixWord ++ tailWord_1583244) baseStart_1583244 baseEnd_1583244 := by
    simpa [prefixWord, tailWord_1583244, baseEnd_1583244] using wordTrace_append hprefix tailTrace_1583244
  have hstable : (prefixWord ++ tailWord_1583244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583244).length < 2 ^ (prefixWord ++ tailWord_1583244).sum := by decide
  have hdescent : baseEnd_1583244 < baseStart_1583244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583252 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1583252 : Nat := 118140960795 + 1583252 * 2 ^ 59
def prefixEnd_1583252 : Nat := 4983230072969 + 3 ^ 40 * 1583252 * 2
def baseEnd_1583252 : Nat := 270989757730781584322921

theorem tailTrace_1583252 : CollatzResearch.WordTrace tailWord_1583252 prefixEnd_1583252 270989757730781584322921 := by
  unfold tailWord_1583252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28872972230077938379616005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38497296306770584506154673 28872972230077938379616005)
  ·
    refine ⟨5413682293139613446178001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28872972230077938379616005 5413682293139613446178001)
    ·
      refine ⟨4060261719854710084633501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5413682293139613446178001 4060261719854710084633501)
      ·
        refine ⟨1522598144945516281737563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4060261719854710084633501 1522598144945516281737563)
        ·
          refine ⟨2283897217418274422606345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522598144945516281737563 2283897217418274422606345)
          ·
            refine ⟨1712922913063705816954759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283897217418274422606345 1712922913063705816954759)
            ·
              refine ⟨2569384369595558725432139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712922913063705816954759 2569384369595558725432139)
              ·
                refine ⟨3854076554393338088148209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569384369595558725432139 3854076554393338088148209)
                ·
                  refine ⟨2890557415795003566111157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854076554393338088148209 2890557415795003566111157)
                  ·
                    refine ⟨270989757730781584322921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2890557415795003566111157 270989757730781584322921)
                    ·
                      rfl

theorem cell23_1583252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1583252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583252 prefixEnd_1583252 := by exact prefixLift 1583252
  have htrace : WordTrace (prefixWord ++ tailWord_1583252) baseStart_1583252 baseEnd_1583252 := by
    simpa [prefixWord, tailWord_1583252, baseEnd_1583252] using wordTrace_append hprefix tailTrace_1583252
  have hstable : (prefixWord ++ tailWord_1583252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583252).length < 2 ^ (prefixWord ++ tailWord_1583252).sum := by decide
  have hdescent : baseEnd_1583252 < baseStart_1583252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583255 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1583255 : Nat := 118140960795 + 1583255 * 2 ^ 59
def prefixEnd_1583255 : Nat := 4983230072969 + 3 ^ 40 * 1583255 * 2
def baseEnd_1583255 : Nat := 812970813634308241231249

theorem tailTrace_1583255 : CollatzResearch.WordTrace tailWord_1583255 prefixEnd_1583255 812970813634308241231249 := by
  unfold tailWord_1583255
  simp only [CollatzResearch.WordTrace]
  refine ⟨57746053879145008271591219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38497369252763338847727479 57746053879145008271591219)
  ·
    refine ⟨86619080818717512407386829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57746053879145008271591219 86619080818717512407386829)
    ·
      refine ⟨32482155307019067152770061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86619080818717512407386829 32482155307019067152770061)
      ·
        refine ⟨12180808240132150182288773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32482155307019067152770061 12180808240132150182288773)
        ·
          refine ⟨2283901545024778159179145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12180808240132150182288773 2283901545024778159179145)
          ·
            refine ⟨1712926158768583619384359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283901545024778159179145 1712926158768583619384359)
            ·
              refine ⟨2569389238152875429076539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712926158768583619384359 2569389238152875429076539)
              ·
                refine ⟨3854083857229313143614809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569389238152875429076539 3854083857229313143614809)
                ·
                  refine ⟨2890562892921984857711107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854083857229313143614809 2890562892921984857711107)
                  ·
                    refine ⟨4335844339382977286566661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890562892921984857711107 4335844339382977286566661)
                    ·
                      refine ⟨812970813634308241231249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4335844339382977286566661 812970813634308241231249)
                      ·
                        rfl

theorem cell23_1583255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1583255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583255 prefixEnd_1583255 := by exact prefixLift 1583255
  have htrace : WordTrace (prefixWord ++ tailWord_1583255) baseStart_1583255 baseEnd_1583255 := by
    simpa [prefixWord, tailWord_1583255, baseEnd_1583255] using wordTrace_append hprefix tailTrace_1583255
  have hstable : (prefixWord ++ tailWord_1583255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583255).length < 2 ^ (prefixWord ++ tailWord_1583255).sum := by decide
  have hdescent : baseEnd_1583255 < baseStart_1583255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583265 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1583265 : Nat := 118140960795 + 1583265 * 2 ^ 59
def prefixEnd_1583265 : Nat := 4983230072969 + 3 ^ 40 * 1583265 * 2
def baseEnd_1583265 : Nat := 270991982813617734035401

theorem tailTrace_1583265 : CollatzResearch.WordTrace tailWord_1583265 prefixEnd_1583265 270991982813617734035401 := by
  unfold tailWord_1583265
  simp only [CollatzResearch.WordTrace]
  refine ⟨57746418609108779979455249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38497612406072519986303499 57746418609108779979455249)
  ·
    refine ⟨43309813956831584984591437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57746418609108779979455249 43309813956831584984591437)
    ·
      refine ⟨16241180233811844369221789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43309813956831584984591437 16241180233811844369221789)
      ·
        refine ⟨6090442587679441638458171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16241180233811844369221789 6090442587679441638458171)
        ·
          refine ⟨9135663881519162457687257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090442587679441638458171 9135663881519162457687257)
          ·
            refine ⟨6851747911139371843265443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9135663881519162457687257 6851747911139371843265443)
            ·
              refine ⟨10277621866709057764898165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6851747911139371843265443 10277621866709057764898165)
              ·
                refine ⟨963527050003974165459203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10277621866709057764898165 963527050003974165459203)
                ·
                  refine ⟨1445290575005961248188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963527050003974165459203 1445290575005961248188805)
                  ·
                    refine ⟨270991982813617734035401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445290575005961248188805 270991982813617734035401)
                    ·
                      rfl

theorem cell23_1583265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1583265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583265 prefixEnd_1583265 := by exact prefixLift 1583265
  have htrace : WordTrace (prefixWord ++ tailWord_1583265) baseStart_1583265 baseEnd_1583265 := by
    simpa [prefixWord, tailWord_1583265, baseEnd_1583265] using wordTrace_append hprefix tailTrace_1583265
  have hstable : (prefixWord ++ tailWord_1583265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583265).length < 2 ^ (prefixWord ++ tailWord_1583265).sum := by decide
  have hdescent : baseEnd_1583265 < baseStart_1583265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583321 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_1583321 : Nat := 118140960795 + 1583321 * 2 ^ 59
def prefixEnd_1583321 : Nat := 4983230072969 + 3 ^ 40 * 1583321 * 2
def baseEnd_1583321 : Nat := 271001567785834994335315

theorem tailTrace_1583321 : CollatzResearch.WordTrace tailWord_1583321 prefixEnd_1583321 271001567785834994335315 := by
  unfold tailWord_1583321
  simp only [CollatzResearch.WordTrace]
  refine ⟨57748461096905901543493817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38498974064603934362329211 57748461096905901543493817)
  ·
    refine ⟨43311345822679426157620363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57748461096905901543493817 43311345822679426157620363)
    ·
      refine ⟨64967018734019139236430545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43311345822679426157620363 64967018734019139236430545)
      ·
        refine ⟨48725264050514354427322909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64967018734019139236430545 48725264050514354427322909)
        ·
          refine ⟨18271974018942882910246091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48725264050514354427322909 18271974018942882910246091)
          ·
            refine ⟨27407961028414324365369137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271974018942882910246091 27407961028414324365369137)
            ·
              refine ⟨20555970771310743274026853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27407961028414324365369137 20555970771310743274026853)
              ·
                refine ⟨3854244519620764363880035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20555970771310743274026853 3854244519620764363880035)
                ·
                  refine ⟨5781366779431146545820053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854244519620764363880035 5781366779431146545820053)
                  ·
                    refine ⟨271001567785834994335315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5781366779431146545820053 271001567785834994335315)
                    ·
                      rfl

theorem cell23_1583321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_1583321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583321 prefixEnd_1583321 := by exact prefixLift 1583321
  have htrace : WordTrace (prefixWord ++ tailWord_1583321) baseStart_1583321 baseEnd_1583321 := by
    simpa [prefixWord, tailWord_1583321, baseEnd_1583321] using wordTrace_append hprefix tailTrace_1583321
  have hstable : (prefixWord ++ tailWord_1583321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583321).length < 2 ^ (prefixWord ++ tailWord_1583321).sum := by decide
  have hdescent : baseEnd_1583321 < baseStart_1583321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583322 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_1583322 : Nat := 118140960795 + 1583322 * 2 ^ 59
def prefixEnd_1583322 : Nat := 4983230072969 + 3 ^ 40 * 1583322 * 2
def baseEnd_1583322 : Nat := 813005216838159479093441

theorem tailTrace_1583322 : CollatzResearch.WordTrace tailWord_1583322 prefixEnd_1583322 813005216838159479093441 := by
  unfold tailWord_1583322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437124392475569678570055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38498998379934852476186813 14437124392475569678570055)
  ·
    refine ⟨21655686588713354517855083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437124392475569678570055 21655686588713354517855083)
    ·
      refine ⟨32483529883070031776782625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655686588713354517855083 32483529883070031776782625)
      ·
        refine ⟨24362647412302523832586969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32483529883070031776782625 24362647412302523832586969)
        ·
          refine ⟨18271985559226892874440227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24362647412302523832586969 18271985559226892874440227)
          ·
            refine ⟨27407978338840339311660341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271985559226892874440227 27407978338840339311660341)
            ·
              refine ⟨2569497969266281810468157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27407978338840339311660341 2569497969266281810468157)
              ·
                refine ⟨963561738474855678925559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569497969266281810468157 963561738474855678925559)
                ·
                  refine ⟨1445342607712283518388339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963561738474855678925559 1445342607712283518388339)
                  ·
                    refine ⟨2168013911568425277582509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445342607712283518388339 2168013911568425277582509)
                    ·
                      refine ⟨813005216838159479093441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168013911568425277582509 813005216838159479093441)
                      ·
                        rfl

theorem cell23_1583322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_1583322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583322 prefixEnd_1583322 := by exact prefixLift 1583322
  have htrace : WordTrace (prefixWord ++ tailWord_1583322) baseStart_1583322 baseEnd_1583322 := by
    simpa [prefixWord, tailWord_1583322, baseEnd_1583322] using wordTrace_append hprefix tailTrace_1583322
  have hstable : (prefixWord ++ tailWord_1583322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583322).length < 2 ^ (prefixWord ++ tailWord_1583322).sum := by decide
  have hdescent : baseEnd_1583322 < baseStart_1583322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583325 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1583325 : Nat := 118140960795 + 1583325 * 2 ^ 59
def prefixEnd_1583325 : Nat := 4983230072969 + 3 ^ 40 * 1583325 * 2
def baseEnd_1583325 : Nat := 271002252426707655785309

theorem tailTrace_1583325 : CollatzResearch.WordTrace tailWord_1583325 prefixEnd_1583325 271002252426707655785309 := by
  unfold tailWord_1583325
  simp only [CollatzResearch.WordTrace]
  refine ⟨57748606988891410226639429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38499071325927606817759619 57748606988891410226639429)
  ·
    refine ⟨10827863810417139417494893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57748606988891410226639429 10827863810417139417494893)
    ·
      refine ⟨4060448928906427281560585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10827863810417139417494893 4060448928906427281560585)
      ·
        refine ⟨3045336696679820461170439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060448928906427281560585 3045336696679820461170439)
        ·
          refine ⟨4568005045019730691755659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045336696679820461170439 4568005045019730691755659)
          ·
            refine ⟨6852007567529596037633489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568005045019730691755659 6852007567529596037633489)
            ·
              refine ⟨5139005675647197028225117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852007567529596037633489 5139005675647197028225117)
              ·
                refine ⟨1927127128367698885584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5139005675647197028225117 1927127128367698885584419)
                ·
                  refine ⟨2890690692551548328376629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927127128367698885584419 2890690692551548328376629)
                  ·
                    refine ⟨271002252426707655785309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2890690692551548328376629 271002252426707655785309)
                    ·
                      rfl

theorem cell23_1583325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1583325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583325 prefixEnd_1583325 := by exact prefixLift 1583325
  have htrace : WordTrace (prefixWord ++ tailWord_1583325) baseStart_1583325 baseEnd_1583325 := by
    simpa [prefixWord, tailWord_1583325, baseEnd_1583325] using wordTrace_append hprefix tailTrace_1583325
  have hstable : (prefixWord ++ tailWord_1583325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583325).length < 2 ^ (prefixWord ++ tailWord_1583325).sum := by decide
  have hdescent : baseEnd_1583325 < baseStart_1583325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583328 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_1583328 : Nat := 118140960795 + 1583328 * 2 ^ 59
def prefixEnd_1583328 : Nat := 4983230072969 + 3 ^ 40 * 1583328 * 2
def baseEnd_1583328 : Nat := 813008297722086455618413

theorem tailTrace_1583328 : CollatzResearch.WordTrace tailWord_1583328 prefixEnd_1583328 813008297722086455618413 := by
  unfold tailWord_1583328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28874358203940270869499319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38499144271920361159332425 28874358203940270869499319)
  ·
    refine ⟨43311537305910406304248979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28874358203940270869499319 43311537305910406304248979)
    ·
      refine ⟨64967305958865609456373469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43311537305910406304248979 64967305958865609456373469)
      ·
        refine ⟨24362739734574603546140051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64967305958865609456373469 24362739734574603546140051)
        ·
          refine ⟨36544109601861905319210077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24362739734574603546140051 36544109601861905319210077)
          ·
            refine ⟨13704041100698214494703779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36544109601861905319210077 13704041100698214494703779)
            ·
              refine ⟨20556061651047321742055669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704041100698214494703779 20556061651047321742055669)
              ·
                refine ⟨1927130779785686413317719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20556061651047321742055669 1927130779785686413317719)
                ·
                  refine ⟨2890696169678529619976579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927130779785686413317719 2890696169678529619976579)
                  ·
                    refine ⟨4336044254517794429964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890696169678529619976579 4336044254517794429964869)
                    ·
                      refine ⟨813008297722086455618413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4336044254517794429964869 813008297722086455618413)
                      ·
                        rfl

theorem cell23_1583328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_1583328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583328 prefixEnd_1583328 := by exact prefixLift 1583328
  have htrace : WordTrace (prefixWord ++ tailWord_1583328) baseStart_1583328 baseEnd_1583328 := by
    simpa [prefixWord, tailWord_1583328, baseEnd_1583328] using wordTrace_append hprefix tailTrace_1583328
  have hstable : (prefixWord ++ tailWord_1583328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583328).length < 2 ^ (prefixWord ++ tailWord_1583328).sum := by decide
  have hdescent : baseEnd_1583328 < baseStart_1583328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583338 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1583338 : Nat := 118140960795 + 1583338 * 2 ^ 59
def prefixEnd_1583338 : Nat := 4983230072969 + 3 ^ 40 * 1583338 * 2
def baseEnd_1583338 : Nat := 271004477509543805497789

theorem tailTrace_1583338 : CollatzResearch.WordTrace tailWord_1583338 prefixEnd_1583338 271004477509543805497789 := by
  unfold tailWord_1583338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437270284461078361715667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38499387425229542297908445 14437270284461078361715667)
  ·
    refine ⟨21655905426691617542573501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437270284461078361715667 21655905426691617542573501)
    ·
      refine ⟨8120964535009356578465063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21655905426691617542573501 8120964535009356578465063)
      ·
        refine ⟨12181446802514034867697595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120964535009356578465063 12181446802514034867697595)
        ·
          refine ⟨18272170203771052301546393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12181446802514034867697595 18272170203771052301546393)
          ·
            refine ⟨13704127652828289226159795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18272170203771052301546393 13704127652828289226159795)
            ·
              refine ⟨20556191479242433839239693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704127652828289226159795 20556191479242433839239693)
              ·
                refine ⟨7708571804715912689714885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20556191479242433839239693 7708571804715912689714885)
                ·
                  refine ⟨1445357213384233629321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7708571804715912689714885 1445357213384233629321541)
                  ·
                    refine ⟨271004477509543805497789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445357213384233629321541 271004477509543805497789)
                    ·
                      rfl

theorem cell23_1583338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1583338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583338 prefixEnd_1583338 := by exact prefixLift 1583338
  have htrace : WordTrace (prefixWord ++ tailWord_1583338) baseStart_1583338 baseEnd_1583338 := by
    simpa [prefixWord, tailWord_1583338, baseEnd_1583338] using wordTrace_append hprefix tailTrace_1583338
  have hstable : (prefixWord ++ tailWord_1583338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583338).length < 2 ^ (prefixWord ++ tailWord_1583338).sum := by decide
  have hdescent : baseEnd_1583338 < baseStart_1583338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583358 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1583358 : Nat := 118140960795 + 1583358 * 2 ^ 59
def prefixEnd_1583358 : Nat := 4983230072969 + 3 ^ 40 * 1583358 * 2
def baseEnd_1583358 : Nat := 813023702141721338243275

theorem tailTrace_1583358 : CollatzResearch.WordTrace tailWord_1583358 prefixEnd_1583358 813023702141721338243275 := by
  unfold tailWord_1583358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218726324721482107823841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38499873731847904575060485 7218726324721482107823841)
  ·
    refine ⟨5414044743541111580867881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218726324721482107823841 5414044743541111580867881)
    ·
      refine ⟨4060533557655833685650911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414044743541111580867881 4060533557655833685650911)
      ·
        refine ⟨6090800336483750528476367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060533557655833685650911 6090800336483750528476367)
        ·
          refine ⟨9136200504725625792714551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090800336483750528476367 9136200504725625792714551)
          ·
            refine ⟨13704300757088438689071827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9136200504725625792714551 13704300757088438689071827)
            ·
              refine ⟨20556451135632658033607741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13704300757088438689071827 20556451135632658033607741)
              ·
                refine ⟨7708669175862246762602903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20556451135632658033607741 7708669175862246762602903)
                ·
                  refine ⟨11563003763793370143904355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7708669175862246762602903 11563003763793370143904355)
                  ·
                    refine ⟨17344505645690055215856533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11563003763793370143904355 17344505645690055215856533)
                    ·
                      refine ⟨813023702141721338243275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17344505645690055215856533 813023702141721338243275)
                      ·
                        rfl

theorem cell23_1583358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1583358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583358 prefixEnd_1583358 := by exact prefixLift 1583358
  have htrace : WordTrace (prefixWord ++ tailWord_1583358) baseStart_1583358 baseEnd_1583358 := by
    simpa [prefixWord, tailWord_1583358, baseEnd_1583358] using wordTrace_append hprefix tailTrace_1583358
  have hstable : (prefixWord ++ tailWord_1583358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583358).length < 2 ^ (prefixWord ++ tailWord_1583358).sum := by decide
  have hdescent : baseEnd_1583358 < baseStart_1583358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583362 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1583362 : Nat := 118140960795 + 1583362 * 2 ^ 59
def prefixEnd_1583362 : Nat := 4983230072969 + 3 ^ 40 * 1583362 * 2
def baseEnd_1583362 : Nat := 813025756064339322593257

theorem tailTrace_1583362 : CollatzResearch.WordTrace tailWord_1583362 prefixEnd_1583362 813025756064339322593257 := by
  unfold tailWord_1583362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437489122439341386434085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38499970993171577030490893 14437489122439341386434085)
  ·
    refine ⟨2707029210457376509956391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14437489122439341386434085 2707029210457376509956391)
    ·
      refine ⟨4060543815686064764934587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707029210457376509956391 4060543815686064764934587)
      ·
        refine ⟨6090815723529097147401881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060543815686064764934587 6090815723529097147401881)
        ·
          refine ⟨4568111792646822860551411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6090815723529097147401881 4568111792646822860551411)
          ·
            refine ⟨6852167688970234290827117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568111792646822860551411 6852167688970234290827117)
            ·
              refine ⟨2569562883363837859060169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6852167688970234290827117 2569562883363837859060169)
              ·
                refine ⟨1927172162522878394295127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569562883363837859060169 1927172162522878394295127)
                ·
                  refine ⟨2890758243784317591442691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927172162522878394295127 2890758243784317591442691)
                  ·
                    refine ⟨4336137365676476387164037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2890758243784317591442691 4336137365676476387164037)
                    ·
                      refine ⟨813025756064339322593257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4336137365676476387164037 813025756064339322593257)
                      ·
                        rfl

theorem cell23_1583362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1583362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583362 prefixEnd_1583362 := by exact prefixLift 1583362
  have htrace : WordTrace (prefixWord ++ tailWord_1583362) baseStart_1583362 baseEnd_1583362 := by
    simpa [prefixWord, tailWord_1583362, baseEnd_1583362] using wordTrace_append hprefix tailTrace_1583362
  have hstable : (prefixWord ++ tailWord_1583362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583362).length < 2 ^ (prefixWord ++ tailWord_1583362).sum := by decide
  have hdescent : baseEnd_1583362 < baseStart_1583362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583396 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_1583396 : Nat := 118140960795 + 1583396 * 2 ^ 59
def prefixEnd_1583396 : Nat := 4983230072969 + 3 ^ 40 * 1583396 * 2
def baseEnd_1583396 : Nat := 813043214406592189568101

theorem tailTrace_1583396 : CollatzResearch.WordTrace tailWord_1583396 prefixEnd_1583396 813043214406592189568101 := by
  unfold tailWord_1583396
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875598285817094676237021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38500797714422792901649361 28875598285817094676237021)
  ·
    refine ⟨10828349357181410503588883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28875598285817094676237021 10828349357181410503588883)
    ·
      refine ⟨16242524035772115755383325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10828349357181410503588883 16242524035772115755383325)
      ·
        refine ⟨6090946513414543408268747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16242524035772115755383325 6090946513414543408268747)
        ·
          refine ⟨9136419770121815112403121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090946513414543408268747 9136419770121815112403121)
          ·
            refine ⟨6852314827591361334302341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9136419770121815112403121 6852314827591361334302341)
            ·
              refine ⟨1284809030173380250181689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6852314827591361334302341 1284809030173380250181689)
              ·
                refine ⟨963606772630035187636267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284809030173380250181689 963606772630035187636267)
                ·
                  refine ⟨1445410158945052781454401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963606772630035187636267 1445410158945052781454401)
                  ·
                    refine ⟨1084057619208789586090801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445410158945052781454401 1084057619208789586090801)
                    ·
                      refine ⟨813043214406592189568101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084057619208789586090801 813043214406592189568101)
                      ·
                        rfl

theorem cell23_1583396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_1583396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583396 prefixEnd_1583396 := by exact prefixLift 1583396
  have htrace : WordTrace (prefixWord ++ tailWord_1583396) baseStart_1583396 baseEnd_1583396 := by
    simpa [prefixWord, tailWord_1583396, baseEnd_1583396] using wordTrace_append hprefix tailTrace_1583396
  have hstable : (prefixWord ++ tailWord_1583396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583396).length < 2 ^ (prefixWord ++ tailWord_1583396).sum := by decide
  have hdescent : baseEnd_1583396 < baseStart_1583396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583402 : List Nat := [3, 1, 4, 2, 3, 1, 1, 8]
def baseStart_1583402 : Nat := 118140960795 + 1583402 * 2 ^ 59
def prefixEnd_1583402 : Nat := 4983230072969 + 3 ^ 40 * 1583402 * 2
def baseEnd_1583402 : Nat := 30112825751500709855299

theorem tailTrace_1583402 : CollatzResearch.WordTrace tailWord_1583402 prefixEnd_1583402 30112825751500709855299 := by
  unfold tailWord_1583402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437853852403113094298115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38500943606408301584794973 14437853852403113094298115)
  ·
    refine ⟨21656780778604669641447173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437853852403113094298115 21656780778604669641447173)
    ·
      refine ⟨4060646395988375557771345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21656780778604669641447173 4060646395988375557771345)
      ·
        refine ⟨3045484796991281668328509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060646395988375557771345 3045484796991281668328509)
        ·
          refine ⟨1142056798871730625623191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3045484796991281668328509 1142056798871730625623191)
          ·
            refine ⟨1713085198307595938434787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142056798871730625623191 1713085198307595938434787)
            ·
              refine ⟨2569627797461393907652181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713085198307595938434787 2569627797461393907652181)
              ·
                refine ⟨30112825751500709855299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2569627797461393907652181 30112825751500709855299)
                ·
                  rfl

theorem cell23_1583402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_1583402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583402 prefixEnd_1583402 := by exact prefixLift 1583402
  have htrace : WordTrace (prefixWord ++ tailWord_1583402) baseStart_1583402 baseEnd_1583402 := by
    simpa [prefixWord, tailWord_1583402, baseEnd_1583402] using wordTrace_append hprefix tailTrace_1583402
  have hstable : (prefixWord ++ tailWord_1583402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583402).length < 2 ^ (prefixWord ++ tailWord_1583402).sum := by decide
  have hdescent : baseEnd_1583402 < baseStart_1583402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583412 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1583412 : Nat := 118140960795 + 1583412 * 2 ^ 59
def prefixEnd_1583412 : Nat := 4983230072969 + 3 ^ 40 * 1583412 * 2
def baseEnd_1583412 : Nat := 813051430097064126968027

theorem tailTrace_1583412 : CollatzResearch.WordTrace tailWord_1583412 prefixEnd_1583412 813051430097064126968027 := by
  unfold tailWord_1583412
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875890069788112042528245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38501186759717482723370993 28875890069788112042528245)
  ·
    refine ⟨2707114694042635503987023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28875890069788112042528245 2707114694042635503987023)
    ·
      refine ⟨4060672041063953255980535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707114694042635503987023 4060672041063953255980535)
      ·
        refine ⟨6091008061595929883970803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060672041063953255980535 6091008061595929883970803)
        ·
          refine ⟨9136512092393894825956205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091008061595929883970803 9136512092393894825956205)
          ·
            refine ⟨3426192034647710559733577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9136512092393894825956205 3426192034647710559733577)
            ·
              refine ⟨2569644025985782919800183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426192034647710559733577 2569644025985782919800183)
              ·
                refine ⟨3854466038978674379700275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569644025985782919800183 3854466038978674379700275)
                ·
                  refine ⟨5781699058468011569550413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3854466038978674379700275 5781699058468011569550413)
                  ·
                    refine ⟨2168137146925504338581405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5781699058468011569550413 2168137146925504338581405)
                    ·
                      refine ⟨813051430097064126968027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168137146925504338581405 813051430097064126968027)
                      ·
                        rfl

theorem cell23_1583412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1583412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583412 prefixEnd_1583412 := by exact prefixLift 1583412
  have htrace : WordTrace (prefixWord ++ tailWord_1583412) baseStart_1583412 baseEnd_1583412 := by
    simpa [prefixWord, tailWord_1583412, baseEnd_1583412] using wordTrace_append hprefix tailTrace_1583412
  have hstable : (prefixWord ++ tailWord_1583412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583412).length < 2 ^ (prefixWord ++ tailWord_1583412).sum := by decide
  have hdescent : baseEnd_1583412 < baseStart_1583412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583422 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_1583422 : Nat := 118140960795 + 1583422 * 2 ^ 59
def prefixEnd_1583422 : Nat := 4983230072969 + 3 ^ 40 * 1583422 * 2
def baseEnd_1583422 : Nat := 813056564903609087842981

theorem tailTrace_1583422 : CollatzResearch.WordTrace tailWord_1583422 prefixEnd_1583422 813056564903609087842981 := by
  unfold tailWord_1583422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219018108692499474115065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38501429913026663861947013 7219018108692499474115065)
  ·
    refine ⟨5414263581519374605586299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7219018108692499474115065 5414263581519374605586299)
    ·
      refine ⟨8121395372279061908379449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5414263581519374605586299 8121395372279061908379449)
      ·
        refine ⟨6091046529209296431284587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8121395372279061908379449 6091046529209296431284587)
        ·
          refine ⟨9136569793813944646926881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091046529209296431284587 9136569793813944646926881)
          ·
            refine ⟨6852427345360458485195161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9136569793813944646926881 6852427345360458485195161)
            ·
              refine ⟨5139320509020343863896371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6852427345360458485195161 5139320509020343863896371)
              ·
                refine ⟨7708980763530515795844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5139320509020343863896371 7708980763530515795844557)
                ·
                  refine ⟨2890867786323943423441709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7708980763530515795844557 2890867786323943423441709)
                  ·
                    refine ⟨1084075419871478783790641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2890867786323943423441709 1084075419871478783790641)
                    ·
                      refine ⟨813056564903609087842981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084075419871478783790641 813056564903609087842981)
                      ·
                        rfl

theorem cell23_1583422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_1583422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583422 prefixEnd_1583422 := by exact prefixLift 1583422
  have htrace : WordTrace (prefixWord ++ tailWord_1583422) baseStart_1583422 baseEnd_1583422 := by
    simpa [prefixWord, tailWord_1583422, baseEnd_1583422] using wordTrace_append hprefix tailTrace_1583422
  have hstable : (prefixWord ++ tailWord_1583422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583422).length < 2 ^ (prefixWord ++ tailWord_1583422).sum := by decide
  have hdescent : baseEnd_1583422 < baseStart_1583422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583438 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1583438 : Nat := 118140960795 + 1583438 * 2 ^ 59
def prefixEnd_1583438 : Nat := 4983230072969 + 3 ^ 40 * 1583438 * 2
def baseEnd_1583438 : Nat := 813064780594081025242907

theorem tailTrace_1583438 : CollatzResearch.WordTrace tailWord_1583438 prefixEnd_1583438 813064780594081025242907 := by
  unfold tailWord_1583438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219091054685253815687871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38501818958321353683668645 7219091054685253815687871)
  ·
    refine ⟨10828636582027880723531807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219091054685253815687871 10828636582027880723531807)
    ·
      refine ⟨16242954873041821085297711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10828636582027880723531807 16242954873041821085297711)
      ·
        refine ⟨24364432309562731627946567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16242954873041821085297711 24364432309562731627946567)
        ·
          refine ⟨36546648464344097441919851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24364432309562731627946567 36546648464344097441919851)
          ·
            refine ⟨54819972696516146162879777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36546648464344097441919851 54819972696516146162879777)
            ·
              refine ⟨41114979522387109622159833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54819972696516146162879777 41114979522387109622159833)
              ·
                refine ⟨30836234641790332216619875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41114979522387109622159833 30836234641790332216619875)
                ·
                  refine ⟨46254351962685498324929813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30836234641790332216619875 46254351962685498324929813)
                  ·
                    refine ⟨2168172748250882733981085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46254351962685498324929813 2168172748250882733981085)
                    ·
                      refine ⟨813064780594081025242907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168172748250882733981085 813064780594081025242907)
                      ·
                        rfl

theorem cell23_1583438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1583438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583438 prefixEnd_1583438 := by exact prefixLift 1583438
  have htrace : WordTrace (prefixWord ++ tailWord_1583438) baseStart_1583438 baseEnd_1583438 := by
    simpa [prefixWord, tailWord_1583438, baseEnd_1583438] using wordTrace_append hprefix tailTrace_1583438
  have hstable : (prefixWord ++ tailWord_1583438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583438).length < 2 ^ (prefixWord ++ tailWord_1583438).sum := by decide
  have hdescent : baseEnd_1583438 < baseStart_1583438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583525 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_1583525 : Nat := 118140960795 + 1583525 * 2 ^ 59
def prefixEnd_1583525 : Nat := 4983230072969 + 3 ^ 40 * 1583525 * 2
def baseEnd_1583525 : Nat := 813109453411022184855007

theorem tailTrace_1583525 : CollatzResearch.WordTrace tailWord_1583525 prefixEnd_1583525 813109453411022184855007 := by
  unfold tailWord_1583525
  simp only [CollatzResearch.WordTrace]
  refine ⟨57755901588166844383920029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38503934392111229589280019 57755901588166844383920029)
  ·
    refine ⟨21658463095562566643970011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57755901588166844383920029 21658463095562566643970011)
    ·
      refine ⟨32487694643343849965955017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21658463095562566643970011 32487694643343849965955017)
      ·
        refine ⟨24365770982507887474466263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32487694643343849965955017 24365770982507887474466263)
        ·
          refine ⟨36548656473761831211699395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24365770982507887474466263 36548656473761831211699395)
          ·
            refine ⟨54822984710642746817549093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36548656473761831211699395 54822984710642746817549093)
            ·
              refine ⟨10279309633245515028290455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54822984710642746817549093 10279309633245515028290455)
              ·
                refine ⟨15418964449868272542435683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279309633245515028290455 15418964449868272542435683)
                ·
                  refine ⟨23128446674802408813653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15418964449868272542435683 23128446674802408813653525)
                  ·
                    refine ⟨1084145937881362913140009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23128446674802408813653525 1084145937881362913140009)
                    ·
                      refine ⟨813109453411022184855007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084145937881362913140009 813109453411022184855007)
                      ·
                        rfl

theorem cell23_1583525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_1583525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583525 prefixEnd_1583525 := by exact prefixLift 1583525
  have htrace : WordTrace (prefixWord ++ tailWord_1583525) baseStart_1583525 baseEnd_1583525 := by
    simpa [prefixWord, tailWord_1583525, baseEnd_1583525] using wordTrace_append hprefix tailTrace_1583525
  have hstable : (prefixWord ++ tailWord_1583525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583525).length < 2 ^ (prefixWord ++ tailWord_1583525).sum := by decide
  have hdescent : baseEnd_1583525 < baseStart_1583525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583552 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 1, 4]
def baseStart_1583552 : Nat := 118140960795 + 1583552 * 2 ^ 59
def prefixEnd_1583552 : Nat := 4983230072969 + 3 ^ 40 * 1583552 * 2
def baseEnd_1583552 : Nat := 271041105796231193072461

theorem tailTrace_1583552 : CollatzResearch.WordTrace tailWord_1583552 prefixEnd_1583552 271041105796231193072461 := by
  unfold tailWord_1583552
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878443179534513997576455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38504590906046018663435273 28878443179534513997576455)
  ·
    refine ⟨43317664769301770996364683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28878443179534513997576455 43317664769301770996364683)
    ·
      refine ⟨64976497153952656494547025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43317664769301770996364683 64976497153952656494547025)
      ·
        refine ⟨48732372865464492370910269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64976497153952656494547025 48732372865464492370910269)
        ·
          refine ⟨18274639824549184639091351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48732372865464492370910269 18274639824549184639091351)
          ·
            refine ⟨27411959736823776958637027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18274639824549184639091351 27411959736823776958637027)
            ·
              refine ⟨41117939605235665437955541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27411959736823776958637027 41117939605235665437955541)
              ·
                refine ⟨963701709497710908702083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41117939605235665437955541 963701709497710908702083)
                ·
                  refine ⟨1445552564246566363053125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963701709497710908702083 1445552564246566363053125)
                  ·
                    refine ⟨271041105796231193072461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445552564246566363053125 271041105796231193072461)
                    ·
                      rfl

theorem cell23_1583552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_1583552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583552 prefixEnd_1583552 := by exact prefixLift 1583552
  have htrace : WordTrace (prefixWord ++ tailWord_1583552) baseStart_1583552 baseEnd_1583552 := by
    simpa [prefixWord, tailWord_1583552, baseEnd_1583552] using wordTrace_append hprefix tailTrace_1583552
  have hstable : (prefixWord ++ tailWord_1583552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583552).length < 2 ^ (prefixWord ++ tailWord_1583552).sum := by decide
  have hdescent : baseEnd_1583552 < baseStart_1583552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583586 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1583586 : Nat := 118140960795 + 1583586 * 2 ^ 59
def prefixEnd_1583586 : Nat := 4983230072969 + 3 ^ 40 * 1583586 * 2
def baseEnd_1583586 : Nat := 271046925243648815397409

theorem tailTrace_1583586 : CollatzResearch.WordTrace tailWord_1583586 prefixEnd_1583586 271046925243648815397409 := by
  unfold tailWord_1583586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14439531610236462950472653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38505417627297234534593741 14439531610236462950472653)
  ·
    refine ⟨5414824353838673606427245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14439531610236462950472653 5414824353838673606427245)
    ·
      refine ⟨2030559132689502602410217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5414824353838673606427245 2030559132689502602410217)
      ·
        refine ⟨1522919349517126951807663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2030559132689502602410217 1522919349517126951807663)
        ·
          refine ⟨2284379024275690427711495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522919349517126951807663 2284379024275690427711495)
          ·
            refine ⟨3426568536413535641567243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284379024275690427711495 3426568536413535641567243)
            ·
              refine ⟨5139852804620303462350865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426568536413535641567243 5139852804620303462350865)
              ·
                refine ⟨3854889603465227596763149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139852804620303462350865 3854889603465227596763149)
                ·
                  refine ⟨1445583601299460348786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3854889603465227596763149 1445583601299460348786181)
                  ·
                    refine ⟨271046925243648815397409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445583601299460348786181 271046925243648815397409)
                    ·
                      rfl

theorem cell23_1583586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1583586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583586 prefixEnd_1583586 := by exact prefixLift 1583586
  have htrace : WordTrace (prefixWord ++ tailWord_1583586) baseStart_1583586 baseEnd_1583586 := by
    simpa [prefixWord, tailWord_1583586, baseEnd_1583586] using wordTrace_append hprefix tailTrace_1583586
  have hstable : (prefixWord ++ tailWord_1583586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583586).length < 2 ^ (prefixWord ++ tailWord_1583586).sum := by decide
  have hdescent : baseEnd_1583586 < baseStart_1583586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583592 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1583592 : Nat := 118140960795 + 1583592 * 2 ^ 59
def prefixEnd_1583592 : Nat := 4983230072969 + 3 ^ 40 * 1583592 * 2
def baseEnd_1583592 : Nat := 813143856614873422717199

theorem tailTrace_1583592 : CollatzResearch.WordTrace tailWord_1583592 prefixEnd_1583592 813143856614873422717199 := by
  unfold tailWord_1583592
  simp only [CollatzResearch.WordTrace]
  refine ⟨28879172639462057413304515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38505563519282743217739353 28879172639462057413304515)
  ·
    refine ⟨43318758959193086119956773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28879172639462057413304515 43318758959193086119956773)
    ·
      refine ⟨8122267304848703647491895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43318758959193086119956773 8122267304848703647491895)
      ·
        refine ⟨12183400957273055471237843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122267304848703647491895 12183400957273055471237843)
        ·
          refine ⟨18275101435909583206856765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183400957273055471237843 18275101435909583206856765)
          ·
            refine ⟨6853163038466093702571287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18275101435909583206856765 6853163038466093702571287)
            ·
              refine ⟨10279744557699140553856931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853163038466093702571287 10279744557699140553856931)
              ·
                refine ⟨15419616836548710830785397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279744557699140553856931 15419616836548710830785397)
                ·
                  refine ⟨1445589078426441640386131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15419616836548710830785397 1445589078426441640386131)
                  ·
                    refine ⟨2168383617639662460579197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445589078426441640386131 2168383617639662460579197)
                    ·
                      refine ⟨813143856614873422717199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168383617639662460579197 813143856614873422717199)
                      ·
                        rfl

theorem cell23_1583592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1583592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583592 prefixEnd_1583592 := by exact prefixLift 1583592
  have htrace : WordTrace (prefixWord ++ tailWord_1583592) baseStart_1583592 baseEnd_1583592 := by
    simpa [prefixWord, tailWord_1583592, baseEnd_1583592] using wordTrace_append hprefix tailTrace_1583592
  have hstable : (prefixWord ++ tailWord_1583592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583592).length < 2 ^ (prefixWord ++ tailWord_1583592).sum := by decide
  have hdescent : baseEnd_1583592 < baseStart_1583592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583595 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 1, 5]
def baseStart_1583595 : Nat := 118140960795 + 1583595 * 2 ^ 59
def prefixEnd_1583595 : Nat := 4983230072969 + 3 ^ 40 * 1583595 * 2
def baseEnd_1583595 : Nat := 271048465685612303659895

theorem tailTrace_1583595 : CollatzResearch.WordTrace tailWord_1583595 prefixEnd_1583595 271048465685612303659895 := by
  unfold tailWord_1583595
  simp only [CollatzResearch.WordTrace]
  refine ⟨57758454697913246338968239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38505636465275497559312159 57758454697913246338968239)
  ·
    refine ⟨86637682046869869508452359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57758454697913246338968239 86637682046869869508452359)
    ·
      refine ⟨129956523070304804262678539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86637682046869869508452359 129956523070304804262678539)
      ·
        refine ⟨194934784605457206394017809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129956523070304804262678539 194934784605457206394017809)
        ·
          refine ⟨146201088454092904795513357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194934784605457206394017809 146201088454092904795513357)
          ·
            refine ⟨54825408170284839298317509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146201088454092904795513357 54825408170284839298317509)
            ·
              refine ⟨10279764031928407368434533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54825408170284839298317509 10279764031928407368434533)
              ·
                refine ⟨1927455755986576381581475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10279764031928407368434533 1927455755986576381581475)
                ·
                  refine ⟨2891183633979864572372213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927455755986576381581475 2891183633979864572372213)
                  ·
                    refine ⟨271048465685612303659895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2891183633979864572372213 271048465685612303659895)
                    ·
                      rfl

theorem cell23_1583595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 5].length) (baseStart_1583595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583595 prefixEnd_1583595 := by exact prefixLift 1583595
  have htrace : WordTrace (prefixWord ++ tailWord_1583595) baseStart_1583595 baseEnd_1583595 := by
    simpa [prefixWord, tailWord_1583595, baseEnd_1583595] using wordTrace_append hprefix tailTrace_1583595
  have hstable : (prefixWord ++ tailWord_1583595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583595).length < 2 ^ (prefixWord ++ tailWord_1583595).sum := by decide
  have hdescent : baseEnd_1583595 < baseStart_1583595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583609 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 1, 1, 3]
def baseStart_1583609 : Nat := 118140960795 + 1583609 * 2 ^ 59
def prefixEnd_1583609 : Nat := 4983230072969 + 3 ^ 40 * 1583609 * 2
def baseEnd_1583609 : Nat := 813152585785999856204621

theorem tailTrace_1583609 : CollatzResearch.WordTrace tailWord_1583609 prefixEnd_1583609 813152585785999856204621 := by
  unfold tailWord_1583609
  simp only [CollatzResearch.WordTrace]
  refine ⟨57758965319862526729977881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38505976879908351153318587 57758965319862526729977881)
  ·
    refine ⟨43319223989896895047483411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57758965319862526729977881 43319223989896895047483411)
    ·
      refine ⟨64978835984845342571225117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43319223989896895047483411 64978835984845342571225117)
      ·
        refine ⟨24367063494317003464209419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64978835984845342571225117 24367063494317003464209419)
        ·
          refine ⟨36550595241475505196314129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24367063494317003464209419 36550595241475505196314129)
          ·
            refine ⟨27412946431106628897235597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36550595241475505196314129 27412946431106628897235597)
            ·
              refine ⟨10279854911664985836463349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27412946431106628897235597 10279854911664985836463349)
              ·
                refine ⟨963736397968592422168439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10279854911664985836463349 963736397968592422168439)
                ·
                  refine ⟨1445604596952888633252659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963736397968592422168439 1445604596952888633252659)
                  ·
                    refine ⟨2168406895429332949878989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445604596952888633252659 2168406895429332949878989)
                    ·
                      refine ⟨813152585785999856204621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168406895429332949878989 813152585785999856204621)
                      ·
                        rfl

theorem cell23_1583609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_1583609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583609 prefixEnd_1583609 := by exact prefixLift 1583609
  have htrace : WordTrace (prefixWord ++ tailWord_1583609) baseStart_1583609 baseEnd_1583609 := by
    simpa [prefixWord, tailWord_1583609, baseEnd_1583609] using wordTrace_append hprefix tailTrace_1583609
  have hstable : (prefixWord ++ tailWord_1583609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583609).length < 2 ^ (prefixWord ++ tailWord_1583609).sum := by decide
  have hdescent : baseEnd_1583609 < baseStart_1583609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583635 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_1583635 : Nat := 118140960795 + 1583635 * 2 ^ 59
def prefixEnd_1583635 : Nat := 4983230072969 + 3 ^ 40 * 1583635 * 2
def baseEnd_1583635 : Nat := 813165936283016754479501

theorem tailTrace_1583635 : CollatzResearch.WordTrace tailWord_1583635 prefixEnd_1583635 813165936283016754479501 := by
  unfold tailWord_1583635
  simp only [CollatzResearch.WordTrace]
  refine ⟨57759913617768333170424359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38506609078512222113616239 57759913617768333170424359)
  ·
    refine ⟨86639870426652499755636539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57759913617768333170424359 86639870426652499755636539)
    ·
      refine ⟨129959805639978749633454809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86639870426652499755636539 129959805639978749633454809)
      ·
        refine ⟨97469854229984062225091107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129959805639978749633454809 97469854229984062225091107)
        ·
          refine ⟨146204781344976093337636661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97469854229984062225091107 146204781344976093337636661)
          ·
            refine ⟨13706698251091508750403437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146204781344976093337636661 13706698251091508750403437)
            ·
              refine ⟨5140011844159315781401289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13706698251091508750403437 5140011844159315781401289)
              ·
                refine ⟨3855008883119486836050967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5140011844159315781401289 3855008883119486836050967)
                ·
                  refine ⟨5782513324679230254076451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855008883119486836050967 5782513324679230254076451)
                  ·
                    refine ⟨8673769987018845381114677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5782513324679230254076451 8673769987018845381114677)
                    ·
                      refine ⟨813165936283016754479501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8673769987018845381114677 813165936283016754479501)
                      ·
                        rfl

theorem cell23_1583635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_1583635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583635 prefixEnd_1583635 := by exact prefixLift 1583635
  have htrace : WordTrace (prefixWord ++ tailWord_1583635) baseStart_1583635 baseEnd_1583635 := by
    simpa [prefixWord, tailWord_1583635, baseEnd_1583635] using wordTrace_append hprefix tailTrace_1583635
  have hstable : (prefixWord ++ tailWord_1583635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583635).length < 2 ^ (prefixWord ++ tailWord_1583635).sum := by decide
  have hdescent : baseEnd_1583635 < baseStart_1583635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583642 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_1583642 : Nat := 118140960795 + 1583642 * 2 ^ 59
def prefixEnd_1583642 : Nat := 4983230072969 + 3 ^ 40 * 1583642 * 2
def baseEnd_1583642 : Nat := 271056510215866075697323

theorem tailTrace_1583642 : CollatzResearch.WordTrace tailWord_1583642 prefixEnd_1583642 271056510215866075697323 := by
  unfold tailWord_1583642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14440042232185743341482295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38506779285828648910619453 14440042232185743341482295)
  ·
    refine ⟨21660063348278615012223443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14440042232185743341482295 21660063348278615012223443)
    ·
      refine ⟨32490095022417922518335165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21660063348278615012223443 32490095022417922518335165)
      ·
        refine ⟨12183785633406720944375687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32490095022417922518335165 12183785633406720944375687)
        ·
          refine ⟨18275678450110081416563531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183785633406720944375687 18275678450110081416563531)
          ·
            refine ⟨27413517675165122124845297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18275678450110081416563531 27413517675165122124845297)
            ·
              refine ⟨20560138256373841593633973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27413517675165122124845297 20560138256373841593633973)
              ·
                refine ⟨1927512961535047649403185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20560138256373841593633973 1927512961535047649403185)
                ·
                  refine ⟨1445634721151285737052389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927512961535047649403185 1445634721151285737052389)
                  ·
                    refine ⟨271056510215866075697323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445634721151285737052389 271056510215866075697323)
                    ·
                      rfl

theorem cell23_1583642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_1583642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583642 prefixEnd_1583642 := by exact prefixLift 1583642
  have htrace : WordTrace (prefixWord ++ tailWord_1583642) baseStart_1583642 baseEnd_1583642 := by
    simpa [prefixWord, tailWord_1583642, baseEnd_1583642] using wordTrace_append hprefix tailTrace_1583642
  have hstable : (prefixWord ++ tailWord_1583642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583642).length < 2 ^ (prefixWord ++ tailWord_1583642).sum := by decide
  have hdescent : baseEnd_1583642 < baseStart_1583642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583649 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1583649 : Nat := 118140960795 + 1583649 * 2 ^ 59
def prefixEnd_1583649 : Nat := 4983230072969 + 3 ^ 40 * 1583649 * 2
def baseEnd_1583649 : Nat := 813173125012179699704437

theorem tailTrace_1583649 : CollatzResearch.WordTrace tailWord_1583649 prefixEnd_1583649 813173125012179699704437 := by
  unfold tailWord_1583649
  simp only [CollatzResearch.WordTrace]
  refine ⟨57760424239717613561434001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38506949493145075707622667 57760424239717613561434001)
  ·
    refine ⟨43320318179788210171075501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57760424239717613561434001 43320318179788210171075501)
    ·
      refine ⟨16245119317420578814153313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43320318179788210171075501 16245119317420578814153313)
      ·
        refine ⟨12183839488065434110614985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16245119317420578814153313 12183839488065434110614985)
        ·
          refine ⟨9137879616049075582961239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183839488065434110614985 9137879616049075582961239)
          ·
            refine ⟨13706819424073613374441859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137879616049075582961239 13706819424073613374441859)
            ·
              refine ⟨20560229136110420061662789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13706819424073613374441859 20560229136110420061662789)
              ·
                refine ⟨3855042963020703761561773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20560229136110420061662789 3855042963020703761561773)
                ·
                  refine ⟨1445641111132763910585665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3855042963020703761561773 1445641111132763910585665)
                  ·
                    refine ⟨1084230833349572932939249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445641111132763910585665 1084230833349572932939249)
                    ·
                      refine ⟨813173125012179699704437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084230833349572932939249 813173125012179699704437)
                      ·
                        rfl

theorem cell23_1583649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1583649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583649 prefixEnd_1583649 := by exact prefixLift 1583649
  have htrace : WordTrace (prefixWord ++ tailWord_1583649) baseStart_1583649 baseEnd_1583649 := by
    simpa [prefixWord, tailWord_1583649, baseEnd_1583649] using wordTrace_append hprefix tailTrace_1583649
  have hstable : (prefixWord ++ tailWord_1583649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583649).length < 2 ^ (prefixWord ++ tailWord_1583649).sum := by decide
  have hdescent : baseEnd_1583649 < baseStart_1583649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583693 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1583693 : Nat := 118140960795 + 1583693 * 2 ^ 59
def prefixEnd_1583693 : Nat := 4983230072969 + 3 ^ 40 * 1583693 * 2
def baseEnd_1583693 : Nat := 271065239386992509184745

theorem tailTrace_1583693 : CollatzResearch.WordTrace tailWord_1583693 prefixEnd_1583693 271065239386992509184745 := by
  unfold tailWord_1583693
  simp only [CollatzResearch.WordTrace]
  refine ⟨57762029051558209076035733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38508019367705472717357155 57762029051558209076035733)
  ·
    refine ⟨2707595111791791050439175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57762029051558209076035733 2707595111791791050439175)
    ·
      refine ⟨4061392667687686575658763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707595111791791050439175 4061392667687686575658763)
      ·
        refine ⟨6092089001531529863488145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061392667687686575658763 6092089001531529863488145)
        ·
          refine ⟨4569066751148647397616109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6092089001531529863488145 4569066751148647397616109)
          ·
            refine ⟨1713400031680742774106041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4569066751148647397616109 1713400031680742774106041)
            ·
              refine ⟨1285050023760557080579531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713400031680742774106041 1285050023760557080579531)
              ·
                refine ⟨1927575035640835620869297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285050023760557080579531 1927575035640835620869297)
                ·
                  refine ⟨1445681276730626715651973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927575035640835620869297 1445681276730626715651973)
                  ·
                    refine ⟨271065239386992509184745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445681276730626715651973 271065239386992509184745)
                    ·
                      rfl

theorem cell23_1583693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1583693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583693 prefixEnd_1583693 := by exact prefixLift 1583693
  have htrace : WordTrace (prefixWord ++ tailWord_1583693) baseStart_1583693 baseEnd_1583693 := by
    simpa [prefixWord, tailWord_1583693, baseEnd_1583693] using wordTrace_append hprefix tailTrace_1583693
  have hstable : (prefixWord ++ tailWord_1583693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583693).length < 2 ^ (prefixWord ++ tailWord_1583693).sum := by decide
  have hdescent : baseEnd_1583693 < baseStart_1583693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583733 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1583733 : Nat := 118140960795 + 1583733 * 2 ^ 59
def prefixEnd_1583733 : Nat := 4983230072969 + 3 ^ 40 * 1583733 * 2
def baseEnd_1583733 : Nat := 813216257387157371054051

theorem tailTrace_1583733 : CollatzResearch.WordTrace tailWord_1583733 prefixEnd_1583733 813216257387157371054051 := by
  unfold tailWord_1583733
  simp only [CollatzResearch.WordTrace]
  refine ⟨57763487971413295907491853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38508991980942197271661235 57763487971413295907491853)
  ·
    refine ⟨21661307989279985965309445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57763487971413295907491853 21661307989279985965309445)
    ·
      refine ⟨4061495247989997368495521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21661307989279985965309445 4061495247989997368495521)
      ·
        refine ⟨3046121435992498026371641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4061495247989997368495521 3046121435992498026371641)
        ·
          refine ⟨2284591076994373519778731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046121435992498026371641 2284591076994373519778731)
          ·
            refine ⟨3426886615491560279668097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284591076994373519778731 3426886615491560279668097)
            ·
              refine ⟨2570164961618670209751073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426886615491560279668097 2570164961618670209751073)
              ·
                refine ⟨1927623721214002657313305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570164961618670209751073 1927623721214002657313305)
                ·
                  refine ⟨1445717790910501992984979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927623721214002657313305 1445717790910501992984979)
                  ·
                    refine ⟨2168576686365752989477469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445717790910501992984979 2168576686365752989477469)
                    ·
                      refine ⟨813216257387157371054051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168576686365752989477469 813216257387157371054051)
                      ·
                        rfl

theorem cell23_1583733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1583733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583733 prefixEnd_1583733 := by exact prefixLift 1583733
  have htrace : WordTrace (prefixWord ++ tailWord_1583733) baseStart_1583733 baseEnd_1583733 := by
    simpa [prefixWord, tailWord_1583733, baseEnd_1583733] using wordTrace_append hprefix tailTrace_1583733
  have hstable : (prefixWord ++ tailWord_1583733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583733).length < 2 ^ (prefixWord ++ tailWord_1583733).sum := by decide
  have hdescent : baseEnd_1583733 < baseStart_1583733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583734 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1583734 : Nat := 118140960795 + 1583734 * 2 ^ 59
def prefixEnd_1583734 : Nat := 4983230072969 + 3 ^ 40 * 1583734 * 2
def baseEnd_1583734 : Nat := 813216770867811867141547

theorem tailTrace_1583734 : CollatzResearch.WordTrace tailWord_1583734 prefixEnd_1583734 813216770867811867141547 := by
  unfold tailWord_1583734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610220277775604567392391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38509016296273115385518837 3610220277775604567392391)
  ·
    refine ⟨5415330416663406851088587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610220277775604567392391 5415330416663406851088587)
    ·
      refine ⟨8122995624995110276632881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5415330416663406851088587 8122995624995110276632881)
      ·
        refine ⟨6092246718746332707474661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8122995624995110276632881 6092246718746332707474661)
        ·
          refine ⟨1142296259764937382651499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6092246718746332707474661 1142296259764937382651499)
          ·
            refine ⟨1713444389647406073977249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142296259764937382651499 1713444389647406073977249)
            ·
              refine ⟨1285083292235554555482937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713444389647406073977249 1285083292235554555482937)
              ·
                refine ⟨963812469176665916612203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285083292235554555482937 963812469176665916612203)
                ·
                  refine ⟨1445718703764998874918305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963812469176665916612203 1445718703764998874918305)
                  ·
                    refine ⟨1084289027823749156188729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445718703764998874918305 1084289027823749156188729)
                    ·
                      refine ⟨813216770867811867141547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084289027823749156188729 813216770867811867141547)
                      ·
                        rfl

theorem cell23_1583734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1583734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583734 prefixEnd_1583734 := by exact prefixLift 1583734
  have htrace : WordTrace (prefixWord ++ tailWord_1583734) baseStart_1583734 baseEnd_1583734 := by
    simpa [prefixWord, tailWord_1583734, baseEnd_1583734] using wordTrace_append hprefix tailTrace_1583734
  have hstable : (prefixWord ++ tailWord_1583734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583734).length < 2 ^ (prefixWord ++ tailWord_1583734).sum := by decide
  have hdescent : baseEnd_1583734 < baseStart_1583734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583762 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_1583762 : Nat := 118140960795 + 1583762 * 2 ^ 59
def prefixEnd_1583762 : Nat := 4983230072969 + 3 ^ 40 * 1583762 * 2
def baseEnd_1583762 : Nat := 90359016480681973065713

theorem tailTrace_1583762 : CollatzResearch.WordTrace tailWord_1583762 prefixEnd_1583762 90359016480681973065713 := by
  unfold tailWord_1583762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441136422077058465074385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38509697125538822573531693 14441136422077058465074385)
  ·
    refine ⟨10830852316557793848805789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14441136422077058465074385 10830852316557793848805789)
    ·
      refine ⟨4061569618709172693302171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10830852316557793848805789 4061569618709172693302171)
      ·
        refine ⟨6092354428063759039953257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061569618709172693302171 6092354428063759039953257)
        ·
          refine ⟨4569265821047819279964943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6092354428063759039953257 4569265821047819279964943)
          ·
            refine ⟨6853898731571728919947415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569265821047819279964943 6853898731571728919947415)
            ·
              refine ⟨10280848097357593379921123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853898731571728919947415 10280848097357593379921123)
              ·
                refine ⟨15421272146036390069881685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280848097357593379921123 15421272146036390069881685)
                ·
                  refine ⟨90359016480681973065713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15421272146036390069881685 90359016480681973065713)
                  ·
                    rfl

theorem cell23_1583762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_1583762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583762 prefixEnd_1583762 := by exact prefixLift 1583762
  have htrace : WordTrace (prefixWord ++ tailWord_1583762) baseStart_1583762 baseEnd_1583762 := by
    simpa [prefixWord, tailWord_1583762, baseEnd_1583762] using wordTrace_append hprefix tailTrace_1583762
  have hstable : (prefixWord ++ tailWord_1583762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583762).length < 2 ^ (prefixWord ++ tailWord_1583762).sum := by decide
  have hdescent : baseEnd_1583762 < baseStart_1583762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583789 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1583789 : Nat := 118140960795 + 1583789 * 2 ^ 59
def prefixEnd_1583789 : Nat := 4983230072969 + 3 ^ 40 * 1583789 * 2
def baseEnd_1583789 : Nat := 813245012303809151953793

theorem tailTrace_1583789 : CollatzResearch.WordTrace tailWord_1583789 prefixEnd_1583789 813245012303809151953793 := by
  unfold tailWord_1583789
  simp only [CollatzResearch.WordTrace]
  refine ⟨57765530459210417471530421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38510353639473611647686947 57765530459210417471530421)
  ·
    refine ⟨5415518480550976637955977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57765530459210417471530421 5415518480550976637955977)
    ·
      refine ⟨4061638860413232478466983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5415518480550976637955977 4061638860413232478466983)
      ·
        refine ⟨6092458290619848717700475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061638860413232478466983 6092458290619848717700475)
        ·
          refine ⟨9138687435929773076550713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092458290619848717700475 9138687435929773076550713)
          ·
            refine ⟨6854015576947329807413035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9138687435929773076550713 6854015576947329807413035)
            ·
              refine ⟨10281023365420994711119553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854015576947329807413035 10281023365420994711119553)
              ·
                refine ⟨7710767524065746033339665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281023365420994711119553 7710767524065746033339665)
                ·
                  refine ⟨5783075643049309525004749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710767524065746033339665 5783075643049309525004749)
                  ·
                    refine ⟨2168653366143491071876781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783075643049309525004749 2168653366143491071876781)
                    ·
                      refine ⟨813245012303809151953793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168653366143491071876781 813245012303809151953793)
                      ·
                        rfl

theorem cell23_1583789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1583789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583789 prefixEnd_1583789 := by exact prefixLift 1583789
  have htrace : WordTrace (prefixWord ++ tailWord_1583789) baseStart_1583789 baseEnd_1583789 := by
    simpa [prefixWord, tailWord_1583789, baseEnd_1583789] using wordTrace_append hprefix tailTrace_1583789
  have hstable : (prefixWord ++ tailWord_1583789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583789).length < 2 ^ (prefixWord ++ tailWord_1583789).sum := by decide
  have hdescent : baseEnd_1583789 < baseStart_1583789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583790 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1583790 : Nat := 118140960795 + 1583790 * 2 ^ 59
def prefixEnd_1583790 : Nat := 4983230072969 + 3 ^ 40 * 1583790 * 2
def baseEnd_1583790 : Nat := 813245525784463648041289

theorem tailTrace_1583790 : CollatzResearch.WordTrace tailWord_1583790 prefixEnd_1583790 813245525784463648041289 := by
  unfold tailWord_1583790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220695866525849330289603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38510377954804529761544549 7220695866525849330289603)
  ·
    refine ⟨10831043799788773995434405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220695866525849330289603 10831043799788773995434405)
    ·
      refine ⟨2030820712460395124143951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10831043799788773995434405 2030820712460395124143951)
      ·
        refine ⟨3046231068690592686215927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030820712460395124143951 3046231068690592686215927)
        ·
          refine ⟨4569346603035889029323891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046231068690592686215927 4569346603035889029323891)
          ·
            refine ⟨6854019904553833543985837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569346603035889029323891 6854019904553833543985837)
            ·
              refine ⟨2570257464207687578994689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854019904553833543985837 2570257464207687578994689)
              ·
                refine ⟨1927693098155765684246017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570257464207687578994689 1927693098155765684246017)
                ·
                  refine ⟨1445769823616824263184513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927693098155765684246017 1445769823616824263184513)
                  ·
                    refine ⟨1084327367712618197388385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445769823616824263184513 1084327367712618197388385)
                    ·
                      refine ⟨813245525784463648041289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084327367712618197388385 813245525784463648041289)
                      ·
                        rfl

theorem cell23_1583790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1583790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583790 prefixEnd_1583790 := by exact prefixLift 1583790
  have htrace : WordTrace (prefixWord ++ tailWord_1583790) baseStart_1583790 baseEnd_1583790 := by
    simpa [prefixWord, tailWord_1583790, baseEnd_1583790] using wordTrace_append hprefix tailTrace_1583790
  have hstable : (prefixWord ++ tailWord_1583790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583790).length < 2 ^ (prefixWord ++ tailWord_1583790).sum := by decide
  have hdescent : baseEnd_1583790 < baseStart_1583790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583852 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 6]
def baseStart_1583852 : Nat := 118140960795 + 1583852 * 2 ^ 59
def prefixEnd_1583852 : Nat := 4983230072969 + 3 ^ 40 * 1583852 * 2
def baseEnd_1583852 : Nat := 90364151287226933940667

theorem tailTrace_1583852 : CollatzResearch.WordTrace tailWord_1583852 prefixEnd_1583852 90364151287226933940667 := by
  unfold tailWord_1583852
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883914128991089615536905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38511885505321452820715873 28883914128991089615536905)
  ·
    refine ⟨21662935596743317211652679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28883914128991089615536905 21662935596743317211652679)
    ·
      refine ⟨32494403395114975817479019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21662935596743317211652679 32494403395114975817479019)
      ·
        refine ⟨48741605092672463726218529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32494403395114975817479019 48741605092672463726218529)
        ·
          refine ⟨36556203819504347794663897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48741605092672463726218529 36556203819504347794663897)
          ·
            refine ⟨27417152864628260845997923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36556203819504347794663897 27417152864628260845997923)
            ·
              refine ⟨41125729296942391268996885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27417152864628260845997923 41125729296942391268996885)
              ·
                refine ⟨1927768560794174590734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41125729296942391268996885 1927768560794174590734229)
                ·
                  refine ⟨90364151287226933940667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1927768560794174590734229 90364151287226933940667)
                  ·
                    rfl

theorem cell23_1583852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_1583852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583852 prefixEnd_1583852 := by exact prefixLift 1583852
  have htrace : WordTrace (prefixWord ++ tailWord_1583852) baseStart_1583852 baseEnd_1583852 := by
    simpa [prefixWord, tailWord_1583852, baseEnd_1583852] using wordTrace_append hprefix tailTrace_1583852
  have hstable : (prefixWord ++ tailWord_1583852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583852).length < 2 ^ (prefixWord ++ tailWord_1583852).sum := by decide
  have hdescent : baseEnd_1583852 < baseStart_1583852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583889 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_1583889 : Nat := 118140960795 + 1583889 * 2 ^ 59
def prefixEnd_1583889 : Nat := 4983230072969 + 3 ^ 40 * 1583889 * 2
def baseEnd_1583889 : Nat := 813296360369258760703333

theorem tailTrace_1583889 : CollatzResearch.WordTrace tailWord_1583889 prefixEnd_1583889 813296360369258760703333 := by
  unfold tailWord_1583889
  simp only [CollatzResearch.WordTrace]
  refine ⟨57769177758848134550170721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38512785172565423033447147 57769177758848134550170721)
  ·
    refine ⟨43326883319136100912628041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57769177758848134550170721 43326883319136100912628041)
    ·
      refine ⟨32495162489352075684471031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43326883319136100912628041 32495162489352075684471031)
      ·
        refine ⟨48742743734028113526706547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32495162489352075684471031 48742743734028113526706547)
        ·
          refine ⟨73114115601042170290059821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48742743734028113526706547 73114115601042170290059821)
          ·
            refine ⟨27417793350390813858772433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73114115601042170290059821 27417793350390813858772433)
            ·
              refine ⟨20563345012793110394079325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27417793350390813858772433 20563345012793110394079325)
              ·
                refine ⟨7711254379797416397779747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20563345012793110394079325 7711254379797416397779747)
                ·
                  refine ⟨11566881569696124596669621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711254379797416397779747 11566881569696124596669621)
                  ·
                    refine ⟨1084395147159011680937777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11566881569696124596669621 1084395147159011680937777)
                    ·
                      refine ⟨813296360369258760703333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084395147159011680937777 813296360369258760703333)
                      ·
                        rfl

theorem cell23_1583889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_1583889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583889 prefixEnd_1583889 := by exact prefixLift 1583889
  have htrace : WordTrace (prefixWord ++ tailWord_1583889) baseStart_1583889 baseEnd_1583889 := by
    simpa [prefixWord, tailWord_1583889, baseEnd_1583889] using wordTrace_append hprefix tailTrace_1583889
  have hstable : (prefixWord ++ tailWord_1583889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583889).length < 2 ^ (prefixWord ++ tailWord_1583889).sum := by decide
  have hdescent : baseEnd_1583889 < baseStart_1583889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583939 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1583939 : Nat := 118140960795 + 1583939 * 2 ^ 59
def prefixEnd_1583939 : Nat := 4983230072969 + 3 ^ 40 * 1583939 * 2
def baseEnd_1583939 : Nat := 813322034401983565078103

theorem tailTrace_1583939 : CollatzResearch.WordTrace tailWord_1583939 prefixEnd_1583939 813322034401983565078103 := by
  unfold tailWord_1583939
  simp only [CollatzResearch.WordTrace]
  refine ⟨57771001408666993089490871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38514000939111328726327247 57771001408666993089490871)
  ·
    refine ⟨86656502113000489634236307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57771001408666993089490871 86656502113000489634236307)
    ·
      refine ⟨129984753169500734451354461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86656502113000489634236307 129984753169500734451354461)
      ·
        refine ⟨48744282438562775419257923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129984753169500734451354461 48744282438562775419257923)
        ·
          refine ⟨73116423657844163128886885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48744282438562775419257923 73116423657844163128886885)
          ·
            refine ⟨13709329435845780586666291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73116423657844163128886885 13709329435845780586666291)
            ·
              refine ⟨20563994153768670879999437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709329435845780586666291 20563994153768670879999437)
              ·
                refine ⟨7711497807663251579999789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20563994153768670879999437 7711497807663251579999789)
                ·
                  refine ⟨2891811677873719342499921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7711497807663251579999789 2891811677873719342499921)
                  ·
                    refine ⟨2168858758405289506874941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2891811677873719342499921 2168858758405289506874941)
                    ·
                      refine ⟨813322034401983565078103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168858758405289506874941 813322034401983565078103)
                      ·
                        rfl

theorem cell23_1583939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1583939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583939 prefixEnd_1583939 := by exact prefixLift 1583939
  have htrace : WordTrace (prefixWord ++ tailWord_1583939) baseStart_1583939 baseEnd_1583939 := by
    simpa [prefixWord, tailWord_1583939, baseEnd_1583939] using wordTrace_append hprefix tailTrace_1583939
  have hstable : (prefixWord ++ tailWord_1583939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583939).length < 2 ^ (prefixWord ++ tailWord_1583939).sum := by decide
  have hdescent : baseEnd_1583939 < baseStart_1583939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583940 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1583940 : Nat := 118140960795 + 1583940 * 2 ^ 59
def prefixEnd_1583940 : Nat := 4983230072969 + 3 ^ 40 * 1583940 * 2
def baseEnd_1583940 : Nat := 813322547882638061165599

theorem tailTrace_1583940 : CollatzResearch.WordTrace tailWord_1583940 prefixEnd_1583940 813322547882638061165599 := by
  unfold tailWord_1583940
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885518940831685130138637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38514025254442246840184849 28885518940831685130138637)
  ·
    refine ⟨10832069602811881923801989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28885518940831685130138637 10832069602811881923801989)
    ·
      refine ⟨2031013050527227860712873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10832069602811881923801989 2031013050527227860712873)
      ·
        refine ⟨1523259787895420895534655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2031013050527227860712873 1523259787895420895534655)
        ·
          refine ⟨2284889681843131343301983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523259787895420895534655 2284889681843131343301983)
          ·
            refine ⟨3427334522764697014952975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284889681843131343301983 3427334522764697014952975)
            ·
              refine ⟨5141001784147045522429463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427334522764697014952975 5141001784147045522429463)
              ·
                refine ⟨7711502676220568283644195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141001784147045522429463 7711502676220568283644195)
                ·
                  refine ⟨11567254014330852425466293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711502676220568283644195 11567254014330852425466293)
                  ·
                    refine ⟨1084430063843517414887465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11567254014330852425466293 1084430063843517414887465)
                    ·
                      refine ⟨813322547882638061165599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084430063843517414887465 813322547882638061165599)
                      ·
                        rfl

theorem cell23_1583940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1583940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583940 prefixEnd_1583940 := by exact prefixLift 1583940
  have htrace : WordTrace (prefixWord ++ tailWord_1583940) baseStart_1583940 baseEnd_1583940 := by
    simpa [prefixWord, tailWord_1583940, baseEnd_1583940] using wordTrace_append hprefix tailTrace_1583940
  have hstable : (prefixWord ++ tailWord_1583940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583940).length < 2 ^ (prefixWord ++ tailWord_1583940).sum := by decide
  have hdescent : baseEnd_1583940 < baseStart_1583940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583986 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1583986 : Nat := 118140960795 + 1583986 * 2 ^ 59
def prefixEnd_1583986 : Nat := 4983230072969 + 3 ^ 40 * 1583986 * 2
def baseEnd_1583986 : Nat := 813346167992744881190387

theorem tailTrace_1583986 : CollatzResearch.WordTrace tailWord_1583986 prefixEnd_1583986 813346167992744881190387 := by
  unfold tailWord_1583986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443178909874180029112953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38515143759664480077634541 14443178909874180029112953)
  ·
    refine ⟨10832384182405635021834715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14443178909874180029112953 10832384182405635021834715)
    ·
      refine ⟨16248576273608452532752073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832384182405635021834715 16248576273608452532752073)
      ·
        refine ⟨12186432205206339399564055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16248576273608452532752073 12186432205206339399564055)
        ·
          refine ⟨18279648307809509099346083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186432205206339399564055 18279648307809509099346083)
          ·
            refine ⟨27419472461714263649019125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279648307809509099346083 27419472461714263649019125)
            ·
              refine ⟨2570575543285712217095543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27419472461714263649019125 2570575543285712217095543)
              ·
                refine ⟨3855863314928568325643315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570575543285712217095543 3855863314928568325643315)
                ·
                  refine ⟨5783794972392852488464973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3855863314928568325643315 5783794972392852488464973)
                  ·
                    refine ⟨2168923114647319683174365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5783794972392852488464973 2168923114647319683174365)
                    ·
                      refine ⟨813346167992744881190387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168923114647319683174365 813346167992744881190387)
                      ·
                        rfl

theorem cell23_1583986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1583986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583986 prefixEnd_1583986 := by exact prefixLift 1583986
  have htrace : WordTrace (prefixWord ++ tailWord_1583986) baseStart_1583986 baseEnd_1583986 := by
    simpa [prefixWord, tailWord_1583986, baseEnd_1583986] using wordTrace_append hprefix tailTrace_1583986
  have hstable : (prefixWord ++ tailWord_1583986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583986).length < 2 ^ (prefixWord ++ tailWord_1583986).sum := by decide
  have hdescent : baseEnd_1583986 < baseStart_1583986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583990 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1583990 : Nat := 118140960795 + 1583990 * 2 ^ 59
def prefixEnd_1583990 : Nat := 4983230072969 + 3 ^ 40 * 1583990 * 2
def baseEnd_1583990 : Nat := 813348221915362865540369

theorem tailTrace_1583990 : CollatzResearch.WordTrace tailWord_1583990 prefixEnd_1583990 813348221915362865540369 := by
  unfold tailWord_1583990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610803845717639299974839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38515241020988152533064949 3610803845717639299974839)
  ·
    refine ⟨5416205768576458949962259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610803845717639299974839 5416205768576458949962259)
    ·
      refine ⟨8124308652864688424943389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416205768576458949962259 8124308652864688424943389)
      ·
        refine ⟨3046615744824258159353771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8124308652864688424943389 3046615744824258159353771)
        ·
          refine ⟨4569923617236387239030657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046615744824258159353771 4569923617236387239030657)
          ·
            refine ⟨3427442712927290429272993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4569923617236387239030657 3427442712927290429272993)
            ·
              refine ⟨2570582034695467821954745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427442712927290429272993 2570582034695467821954745)
              ·
                refine ⟨1927936526021600866466059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570582034695467821954745 1927936526021600866466059)
                ·
                  refine ⟨2891904789032401299699089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927936526021600866466059 2891904789032401299699089)
                  ·
                    refine ⟨2168928591774300974774317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2891904789032401299699089 2168928591774300974774317)
                    ·
                      refine ⟨813348221915362865540369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2168928591774300974774317 813348221915362865540369)
                      ·
                        rfl

theorem cell23_1583990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1583990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583990 prefixEnd_1583990 := by exact prefixLift 1583990
  have htrace : WordTrace (prefixWord ++ tailWord_1583990) baseStart_1583990 baseEnd_1583990 := by
    simpa [prefixWord, tailWord_1583990, baseEnd_1583990] using wordTrace_append hprefix tailTrace_1583990
  have hstable : (prefixWord ++ tailWord_1583990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583990).length < 2 ^ (prefixWord ++ tailWord_1583990).sum := by decide
  have hdescent : baseEnd_1583990 < baseStart_1583990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583992 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1583992 : Nat := 118140960795 + 1583992 * 2 ^ 59
def prefixEnd_1583992 : Nat := 4983230072969 + 3 ^ 40 * 1583992 * 2
def baseEnd_1583992 : Nat := 813349248876671857715359

theorem tailTrace_1583992 : CollatzResearch.WordTrace tailWord_1583992 prefixEnd_1583992 813349248876671857715359 := by
  unfold tailWord_1583992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886467238737491570585115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38515289651649988760780153 28886467238737491570585115)
  ·
    refine ⟨43329700858106237355877673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28886467238737491570585115 43329700858106237355877673)
    ·
      refine ⟨32497275643579678016908255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43329700858106237355877673 32497275643579678016908255)
      ·
        refine ⟨48745913465369517025362383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32497275643579678016908255 48745913465369517025362383)
        ·
          refine ⟨73118870198054275538043575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48745913465369517025362383 73118870198054275538043575)
          ·
            refine ⟨109678305297081413307065363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73118870198054275538043575 109678305297081413307065363)
            ·
              refine ⟨164517457945622119960598045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109678305297081413307065363 164517457945622119960598045)
              ·
                refine ⟨61694046729608294985224267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164517457945622119960598045 61694046729608294985224267)
                ·
                  refine ⟨92541070094412442477836401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61694046729608294985224267 92541070094412442477836401)
                  ·
                    refine ⟨69405802570809331858377301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92541070094412442477836401 69405802570809331858377301)
                    ·
                      refine ⟨813349248876671857715359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69405802570809331858377301 813349248876671857715359)
                      ·
                        rfl

theorem cell23_1583992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1583992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583992 prefixEnd_1583992 := by exact prefixLift 1583992
  have htrace : WordTrace (prefixWord ++ tailWord_1583992) baseStart_1583992 baseEnd_1583992 := by
    simpa [prefixWord, tailWord_1583992, baseEnd_1583992] using wordTrace_append hprefix tailTrace_1583992
  have hstable : (prefixWord ++ tailWord_1583992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583992).length < 2 ^ (prefixWord ++ tailWord_1583992).sum := by decide
  have hdescent : baseEnd_1583992 < baseStart_1583992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_1583996 : Nat := 118140960795 + 1583996 * 2 ^ 59
def prefixEnd_1583996 : Nat := 4983230072969 + 3 ^ 40 * 1583996 * 2
def baseEnd_1583996 : Nat := 813351302799289842065341

theorem tailTrace_1583996 : CollatzResearch.WordTrace tailWord_1583996 prefixEnd_1583996 813351302799289842065341 := by
  unfold tailWord_1583996
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886540184730245912157921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38515386912973661216210561 28886540184730245912157921)
  ·
    refine ⟨21664905138547684434118441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28886540184730245912157921 21664905138547684434118441)
    ·
      refine ⟨16248678853910763325588831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21664905138547684434118441 16248678853910763325588831)
      ·
        refine ⟨24373018280866144988383247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248678853910763325588831 24373018280866144988383247)
        ·
          refine ⟨36559527421299217482574871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24373018280866144988383247 36559527421299217482574871)
          ·
            refine ⟨54839291131948826223862307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36559527421299217482574871 54839291131948826223862307)
            ·
              refine ⟨82258936697923239335793461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54839291131948826223862307 82258936697923239335793461)
              ·
                refine ⟨7711775315430303687730637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82258936697923239335793461 7711775315430303687730637)
                ·
                  refine ⟨2891915743286363882898989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7711775315430303687730637 2891915743286363882898989)
                  ·
                    refine ⟨1084468403732386456087121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2891915743286363882898989 1084468403732386456087121)
                    ·
                      refine ⟨813351302799289842065341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084468403732386456087121 813351302799289842065341)
                      ·
                        rfl

theorem cell23_1583996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_1583996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1583996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1583996 prefixEnd_1583996 := by exact prefixLift 1583996
  have htrace : WordTrace (prefixWord ++ tailWord_1583996) baseStart_1583996 baseEnd_1583996 := by
    simpa [prefixWord, tailWord_1583996, baseEnd_1583996] using wordTrace_append hprefix tailTrace_1583996
  have hstable : (prefixWord ++ tailWord_1583996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583996).length < 2 ^ (prefixWord ++ tailWord_1583996).sum := by decide
  have hdescent : baseEnd_1583996 < baseStart_1583996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584029 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1584029 : Nat := 118140960795 + 1584029 * 2 ^ 59
def prefixEnd_1584029 : Nat := 4983230072969 + 3 ^ 40 * 1584029 * 2
def baseEnd_1584029 : Nat := 813368247660888212952689

theorem tailTrace_1584029 : CollatzResearch.WordTrace tailWord_1584029 prefixEnd_1584029 813368247660888212952689 := by
  unfold tailWord_1584029
  simp only [CollatzResearch.WordTrace]
  refine ⟨57774283978340938460267141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38516189318893958973511427 57774283978340938460267141)
  ·
    refine ⟨10832678245938925961300089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57774283978340938460267141 10832678245938925961300089)
    ·
      refine ⟨8124508684454194470975067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10832678245938925961300089 8124508684454194470975067)
      ·
        refine ⟨12186763026681291706462601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124508684454194470975067 12186763026681291706462601)
        ·
          refine ⟨9140072270010968779846951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12186763026681291706462601 9140072270010968779846951)
          ·
            refine ⟨13710108405016453169770427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140072270010968779846951 13710108405016453169770427)
            ·
              refine ⟨20565162607524679754655641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13710108405016453169770427 20565162607524679754655641)
              ·
                refine ⟨15423871955643509815991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20565162607524679754655641 15423871955643509815991731)
                ·
                  refine ⟨23135807933465264723987597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15423871955643509815991731 23135807933465264723987597)
                  ·
                    refine ⟨8675927975049474271495349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23135807933465264723987597 8675927975049474271495349)
                    ·
                      refine ⟨813368247660888212952689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8675927975049474271495349 813368247660888212952689)
                      ·
                        rfl

theorem cell23_1584029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1584029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584029 prefixEnd_1584029 := by exact prefixLift 1584029
  have htrace : WordTrace (prefixWord ++ tailWord_1584029) baseStart_1584029 baseEnd_1584029 := by
    simpa [prefixWord, tailWord_1584029, baseEnd_1584029] using wordTrace_append hprefix tailTrace_1584029
  have hstable : (prefixWord ++ tailWord_1584029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584029).length < 2 ^ (prefixWord ++ tailWord_1584029).sum := by decide
  have hdescent : baseEnd_1584029 < baseStart_1584029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584043 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 2, 2, 2]
def baseStart_1584043 : Nat := 118140960795 + 1584043 * 2 ^ 59
def prefixEnd_1584043 : Nat := 4983230072969 + 3 ^ 40 * 1584043 * 2
def baseEnd_1584043 : Nat := 813375436390051158177625

theorem tailTrace_1584043 : CollatzResearch.WordTrace tailWord_1584043 prefixEnd_1584043 813375436390051158177625 := by
  unfold tailWord_1584043
  simp only [CollatzResearch.WordTrace]
  refine ⟨57774794600290218851276783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38516529733526812567517855 57774794600290218851276783)
  ·
    refine ⟨86662191900435328276915175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57774794600290218851276783 86662191900435328276915175)
    ·
      refine ⟨129993287850652992415372763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86662191900435328276915175 129993287850652992415372763)
      ·
        refine ⟨194989931775979488623059145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129993287850652992415372763 194989931775979488623059145)
        ·
          refine ⟨146242448831984616467294359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194989931775979488623059145 146242448831984616467294359)
          ·
            refine ⟨219363673247976924700941539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146242448831984616467294359 219363673247976924700941539)
            ·
              refine ⟨329045509871965387051412309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219363673247976924700941539 329045509871965387051412309)
              ·
                refine ⟨1928001034406047189754369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 329045509871965387051412309 1928001034406047189754369)
                ·
                  refine ⟨1446000775804535392315777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1928001034406047189754369 1446000775804535392315777)
                  ·
                    refine ⟨1084500581853401544236833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446000775804535392315777 1084500581853401544236833)
                    ·
                      refine ⟨813375436390051158177625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084500581853401544236833 813375436390051158177625)
                      ·
                        rfl

theorem cell23_1584043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2, 2].length) (baseStart_1584043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584043 prefixEnd_1584043 := by exact prefixLift 1584043
  have htrace : WordTrace (prefixWord ++ tailWord_1584043) baseStart_1584043 baseEnd_1584043 := by
    simpa [prefixWord, tailWord_1584043, baseEnd_1584043] using wordTrace_append hprefix tailTrace_1584043
  have hstable : (prefixWord ++ tailWord_1584043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584043).length < 2 ^ (prefixWord ++ tailWord_1584043).sum := by decide
  have hdescent : baseEnd_1584043 < baseStart_1584043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584076 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1584076 : Nat := 118140960795 + 1584076 * 2 ^ 59
def prefixEnd_1584076 : Nat := 4983230072969 + 3 ^ 40 * 1584076 * 2
def baseEnd_1584076 : Nat := 813392381251649529064973

theorem tailTrace_1584076 : CollatzResearch.WordTrace tailWord_1584076 prefixEnd_1584076 813392381251649529064973 := by
  unfold tailWord_1584076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887999104585332743614041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38517332139447110324818721 28887999104585332743614041)
  ·
    refine ⟨21665999328438999557710531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28887999104585332743614041 21665999328438999557710531)
    ·
      refine ⟨32498998992658499336565797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21665999328438999557710531 32498998992658499336565797)
      ·
        refine ⟨6093562311123468625606087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32498998992658499336565797 6093562311123468625606087)
        ·
          refine ⟨9140343466685202938409131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6093562311123468625606087 9140343466685202938409131)
          ·
            refine ⟨13710515200027804407613697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140343466685202938409131 13710515200027804407613697)
            ·
              refine ⟨10282886400020853305710273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13710515200027804407613697 10282886400020853305710273)
              ·
                refine ⟨7712164800015639979282705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10282886400020853305710273 7712164800015639979282705)
                ·
                  refine ⟨5784123600011729984462029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712164800015639979282705 5784123600011729984462029)
                  ·
                    refine ⟨2169046350004398744173261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5784123600011729984462029 2169046350004398744173261)
                    ·
                      refine ⟨813392381251649529064973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2169046350004398744173261 813392381251649529064973)
                      ·
                        rfl

theorem cell23_1584076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1584076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584076 prefixEnd_1584076 := by exact prefixLift 1584076
  have htrace : WordTrace (prefixWord ++ tailWord_1584076) baseStart_1584076 baseEnd_1584076 := by
    simpa [prefixWord, tailWord_1584076, baseEnd_1584076] using wordTrace_append hprefix tailTrace_1584076
  have hstable : (prefixWord ++ tailWord_1584076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584076).length < 2 ^ (prefixWord ++ tailWord_1584076).sum := by decide
  have hdescent : baseEnd_1584076 < baseStart_1584076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584093 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1584093 : Nat := 118140960795 + 1584093 * 2 ^ 59
def prefixEnd_1584093 : Nat := 4983230072969 + 3 ^ 40 * 1584093 * 2
def baseEnd_1584093 : Nat := 813401110422775962552395

theorem tailTrace_1584093 : CollatzResearch.WordTrace tailWord_1584093 prefixEnd_1584093 813401110422775962552395 := by
  unfold tailWord_1584093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57776618250109077390596933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38517745500072718260397955 57776618250109077390596933)
  ·
    refine ⟨10833115921895452010736925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57776618250109077390596933 10833115921895452010736925)
    ·
      refine ⟨4062418470710794504026347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10833115921895452010736925 4062418470710794504026347)
      ·
        refine ⟨6093627706066191756039521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062418470710794504026347 6093627706066191756039521)
        ·
          refine ⟨4570220779549643817029641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093627706066191756039521 4570220779549643817029641)
          ·
            refine ⟨3427665584662232862772231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570220779549643817029641 3427665584662232862772231)
            ·
              refine ⟨5141498376993349294158347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427665584662232862772231 5141498376993349294158347)
              ·
                refine ⟨7712247565490023941237521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5141498376993349294158347 7712247565490023941237521)
                ·
                  refine ⟨5784185674117517955928141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712247565490023941237521 5784185674117517955928141)
                  ·
                    refine ⟨2169069627794069233473053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5784185674117517955928141 2169069627794069233473053)
                    ·
                      refine ⟨813401110422775962552395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2169069627794069233473053 813401110422775962552395)
                      ·
                        rfl

theorem cell23_1584093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1584093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584093 prefixEnd_1584093 := by exact prefixLift 1584093
  have htrace : WordTrace (prefixWord ++ tailWord_1584093) baseStart_1584093 baseEnd_1584093 := by
    simpa [prefixWord, tailWord_1584093, baseEnd_1584093] using wordTrace_append hprefix tailTrace_1584093
  have hstable : (prefixWord ++ tailWord_1584093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584093).length < 2 ^ (prefixWord ++ tailWord_1584093).sum := by decide
  have hdescent : baseEnd_1584093 < baseStart_1584093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584113 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_1584113 : Nat := 118140960795 + 1584113 * 2 ^ 59
def prefixEnd_1584113 : Nat := 4983230072969 + 3 ^ 40 * 1584113 * 2
def baseEnd_1584113 : Nat := 271137126678621961434101

theorem tailTrace_1584113 : CollatzResearch.WordTrace tailWord_1584113 prefixEnd_1584113 271137126678621961434101 := by
  unfold tailWord_1584113
  simp only [CollatzResearch.WordTrace]
  refine ⟨57777347710036620806324993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38518231806691080537549995 57777347710036620806324993)
  ·
    refine ⟨43333010782527465604743745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57777347710036620806324993 43333010782527465604743745)
    ·
      refine ⟨32499758086895599203557809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43333010782527465604743745 32499758086895599203557809)
      ·
        refine ⟨24374818565171699402668357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32499758086895599203557809 24374818565171699402668357)
        ·
          refine ⟨4570278480969693638000317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24374818565171699402668357 4570278480969693638000317)
          ·
            refine ⟨1713854430363635114250119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4570278480969693638000317 1713854430363635114250119)
            ·
              refine ⟨2570781645545452671375179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713854430363635114250119 2570781645545452671375179)
              ·
                refine ⟨3856172468318179007062769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570781645545452671375179 3856172468318179007062769)
                ·
                  refine ⟨2892129351238634255297077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856172468318179007062769 2892129351238634255297077)
                  ·
                    refine ⟨271137126678621961434101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2892129351238634255297077 271137126678621961434101)
                    ·
                      rfl

theorem cell23_1584113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_1584113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584113 prefixEnd_1584113 := by exact prefixLift 1584113
  have htrace : WordTrace (prefixWord ++ tailWord_1584113) baseStart_1584113 baseEnd_1584113 := by
    simpa [prefixWord, tailWord_1584113, baseEnd_1584113] using wordTrace_append hprefix tailTrace_1584113
  have hstable : (prefixWord ++ tailWord_1584113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584113).length < 2 ^ (prefixWord ++ tailWord_1584113).sum := by decide
  have hdescent : baseEnd_1584113 < baseStart_1584113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584117 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 5]
def baseStart_1584117 : Nat := 118140960795 + 1584117 * 2 ^ 59
def prefixEnd_1584117 : Nat := 4983230072969 + 3 ^ 40 * 1584117 * 2
def baseEnd_1584117 : Nat := 90379270439831540961365

theorem tailTrace_1584117 : CollatzResearch.WordTrace tailWord_1584117 prefixEnd_1584117 90379270439831540961365 := by
  unfold tailWord_1584117
  simp only [CollatzResearch.WordTrace]
  refine ⟨57777493602022129489470605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38518329068014752992980403 57777493602022129489470605)
  ·
    refine ⟨21666560100758298558551477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57777493602022129489470605 21666560100758298558551477)
    ·
      refine ⟨2031240009446090489864201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21666560100758298558551477 2031240009446090489864201)
      ·
        refine ⟨1523430007084567867398151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2031240009446090489864201 1523430007084567867398151)
        ·
          refine ⟨2285145010626851801097227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523430007084567867398151 2285145010626851801097227)
          ·
            refine ⟨3427717515940277701645841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285145010626851801097227 3427717515940277701645841)
            ·
              refine ⟨2570788136955208276234381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427717515940277701645841 2570788136955208276234381)
              ·
                refine ⟨964045551358203103587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2570788136955208276234381 964045551358203103587893)
                ·
                  refine ⟨90379270439831540961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 964045551358203103587893 90379270439831540961365)
                  ·
                    rfl

theorem cell23_1584117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_1584117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584117 prefixEnd_1584117 := by exact prefixLift 1584117
  have htrace : WordTrace (prefixWord ++ tailWord_1584117) baseStart_1584117 baseEnd_1584117 := by
    simpa [prefixWord, tailWord_1584117, baseEnd_1584117] using wordTrace_append hprefix tailTrace_1584117
  have hstable : (prefixWord ++ tailWord_1584117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584117).length < 2 ^ (prefixWord ++ tailWord_1584117).sum := by decide
  have hdescent : baseEnd_1584117 < baseStart_1584117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584216 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_1584216 : Nat := 118140960795 + 1584216 * 2 ^ 59
def prefixEnd_1584216 : Nat := 4983230072969 + 3 ^ 40 * 1584216 * 2
def baseEnd_1584216 : Nat := 271154756181092993771443

theorem tailTrace_1584216 : CollatzResearch.WordTrace tailWord_1584216 prefixEnd_1584216 271154756181092993771443 := by
  unfold tailWord_1584216
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890552214331734698662251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38520736285775646264883001 28890552214331734698662251)
  ·
    refine ⟨43335828321497602047993377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28890552214331734698662251 43335828321497602047993377)
    ·
      refine ⟨32501871241123201535995033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43335828321497602047993377 32501871241123201535995033)
      ·
        refine ⟨24376403430842401151996275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32501871241123201535995033 24376403430842401151996275)
        ·
          refine ⟨36564605146263601727994413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24376403430842401151996275 36564605146263601727994413)
          ·
            refine ⟨13711726929848850647997905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36564605146263601727994413 13711726929848850647997905)
            ·
              refine ⟨10283795197386637985998429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13711726929848850647997905 10283795197386637985998429)
              ·
                refine ⟨3856423199019989244749411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10283795197386637985998429 3856423199019989244749411)
                ·
                  refine ⟨5784634798529983867124117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856423199019989244749411 5784634798529983867124117)
                  ·
                    refine ⟨271154756181092993771443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5784634798529983867124117 271154756181092993771443)
                    ·
                      rfl

theorem cell23_1584216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_1584216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584216 prefixEnd_1584216 := by exact prefixLift 1584216
  have htrace : WordTrace (prefixWord ++ tailWord_1584216) baseStart_1584216 baseEnd_1584216 := by
    simpa [prefixWord, tailWord_1584216, baseEnd_1584216] using wordTrace_append hprefix tailTrace_1584216
  have hstable : (prefixWord ++ tailWord_1584216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584216).length < 2 ^ (prefixWord ++ tailWord_1584216).sum := by decide
  have hdescent : baseEnd_1584216 < baseStart_1584216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584240 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4]
def baseStart_1584240 : Nat := 118140960795 + 1584240 * 2 ^ 59
def prefixEnd_1584240 : Nat := 4983230072969 + 3 ^ 40 * 1584240 * 2
def baseEnd_1584240 : Nat := 813476592078986887414219

theorem tailTrace_1584240 : CollatzResearch.WordTrace tailWord_1584240 prefixEnd_1584240 813476592078986887414219 := by
  unfold tailWord_1584240
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890989890288260748099087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38521319853717680997465449 28890989890288260748099087)
  ·
    refine ⟨43336484835432391122148631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28890989890288260748099087 43336484835432391122148631)
    ·
      refine ⟨65004727253148586683222947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43336484835432391122148631 65004727253148586683222947)
      ·
        refine ⟨97507090879722880024834421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65004727253148586683222947 97507090879722880024834421)
        ·
          refine ⟨9141289769974020002328227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97507090879722880024834421 9141289769974020002328227)
          ·
            refine ⟨13711934654961030003492341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141289769974020002328227 13711934654961030003492341)
            ·
              refine ⟨1285493873902596562827407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13711934654961030003492341 1285493873902596562827407)
              ·
                refine ⟨1928240810853894844241111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285493873902596562827407 1928240810853894844241111)
                ·
                  refine ⟨2892361216280842266361667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928240810853894844241111 2892361216280842266361667)
                  ·
                    refine ⟨4338541824421263399542501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892361216280842266361667 4338541824421263399542501)
                    ·
                      refine ⟨813476592078986887414219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4338541824421263399542501 813476592078986887414219)
                      ·
                        rfl

theorem cell23_1584240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4].length) (baseStart_1584240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584240 prefixEnd_1584240 := by exact prefixLift 1584240
  have htrace : WordTrace (prefixWord ++ tailWord_1584240) baseStart_1584240 baseEnd_1584240 := by
    simpa [prefixWord, tailWord_1584240, baseEnd_1584240] using wordTrace_append hprefix tailTrace_1584240
  have hstable : (prefixWord ++ tailWord_1584240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584240).length < 2 ^ (prefixWord ++ tailWord_1584240).sum := by decide
  have hdescent : baseEnd_1584240 < baseStart_1584240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584270 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1584270 : Nat := 118140960795 + 1584270 * 2 ^ 59
def prefixEnd_1584270 : Nat := 4983230072969 + 3 ^ 40 * 1584270 * 2
def baseEnd_1584270 : Nat := 813491996498621770039081

theorem tailTrace_1584270 : CollatzResearch.WordTrace tailWord_1584270 prefixEnd_1584270 813491996498621770039081 := by
  unfold tailWord_1584270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222884246308479577473783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38522049313645224413193509 7222884246308479577473783)
  ·
    refine ⟨10834326369462719366210675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7222884246308479577473783 10834326369462719366210675)
    ·
      refine ⟨16251489554194079049316013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834326369462719366210675 16251489554194079049316013)
      ·
        refine ⟨6094308582822779643493505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16251489554194079049316013 6094308582822779643493505)
        ·
          refine ⟨4570731437117084732620129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6094308582822779643493505 4570731437117084732620129)
          ·
            refine ⟨3428048577837813549465097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570731437117084732620129 3428048577837813549465097)
            ·
              refine ⟨2571036433378360162098823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428048577837813549465097 2571036433378360162098823)
              ·
                refine ⟨3856554650067540243148235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571036433378360162098823 3856554650067540243148235)
                ·
                  refine ⟨5784831975101310364722353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856554650067540243148235 5784831975101310364722353)
                  ·
                    refine ⟨4338623981325982773541765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5784831975101310364722353 4338623981325982773541765)
                    ·
                      refine ⟨813491996498621770039081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4338623981325982773541765 813491996498621770039081)
                      ·
                        rfl

theorem cell23_1584270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1584270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584270 prefixEnd_1584270 := by exact prefixLift 1584270
  have htrace : WordTrace (prefixWord ++ tailWord_1584270) baseStart_1584270 baseEnd_1584270 := by
    simpa [prefixWord, tailWord_1584270, baseEnd_1584270] using wordTrace_append hprefix tailTrace_1584270
  have hstable : (prefixWord ++ tailWord_1584270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584270).length < 2 ^ (prefixWord ++ tailWord_1584270).sum := by decide
  have hdescent : baseEnd_1584270 < baseStart_1584270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584324 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_1584324 : Nat := 118140960795 + 1584324 * 2 ^ 59
def prefixEnd_1584324 : Nat := 4983230072969 + 3 ^ 40 * 1584324 * 2
def baseEnd_1584324 : Nat := 813519724453964558763833

theorem tailTrace_1584324 : CollatzResearch.WordTrace tailWord_1584324 prefixEnd_1584324 813519724453964558763833 := by
  unfold tailWord_1584324
  simp only [CollatzResearch.WordTrace]
  refine ⟨28892521756136101921128013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38523362341514802561504017 28892521756136101921128013)
  ·
    refine ⟨10834695658551038220423005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28892521756136101921128013 10834695658551038220423005)
    ·
      refine ⟨4063010871956639332658627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10834695658551038220423005 4063010871956639332658627)
      ·
        refine ⟨6094516307934958998987941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063010871956639332658627 6094516307934958998987941)
        ·
          refine ⟨1142721807737804812310239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6094516307934958998987941 1142721807737804812310239)
          ·
            refine ⟨1714082711606707218465359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142721807737804812310239 1714082711606707218465359)
            ·
              refine ⟨2571124067410060827698039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714082711606707218465359 2571124067410060827698039)
              ·
                refine ⟨3856686101115091241547059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571124067410060827698039 3856686101115091241547059)
                ·
                  refine ⟨5785029151672636862320589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856686101115091241547059 5785029151672636862320589)
                  ·
                    refine ⟨2169385931877238823370221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5785029151672636862320589 2169385931877238823370221)
                    ·
                      refine ⟨813519724453964558763833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2169385931877238823370221 813519724453964558763833)
                      ·
                        rfl

theorem cell23_1584324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_1584324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584324 prefixEnd_1584324 := by exact prefixLift 1584324
  have htrace : WordTrace (prefixWord ++ tailWord_1584324) baseStart_1584324 baseEnd_1584324 := by
    simpa [prefixWord, tailWord_1584324, baseEnd_1584324] using wordTrace_append hprefix tailTrace_1584324
  have hstable : (prefixWord ++ tailWord_1584324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584324).length < 2 ^ (prefixWord ++ tailWord_1584324).sum := by decide
  have hdescent : baseEnd_1584324 < baseStart_1584324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584334 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_1584334 : Nat := 118140960795 + 1584334 * 2 ^ 59
def prefixEnd_1584334 : Nat := 4983230072969 + 3 ^ 40 * 1584334 * 2
def baseEnd_1584334 : Nat := 813524859260509519638787

theorem tailTrace_1584334 : CollatzResearch.WordTrace tailWord_1584334 prefixEnd_1584334 813524859260509519638787 := by
  unfold tailWord_1584334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7223176030279496943765007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38523605494823983700080037 7223176030279496943765007)
  ·
    refine ⟨10834764045419245415647511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7223176030279496943765007 10834764045419245415647511)
    ·
      refine ⟨16252146068128868123471267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834764045419245415647511 16252146068128868123471267)
      ·
        refine ⟨24378219102193302185206901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16252146068128868123471267 24378219102193302185206901)
        ·
          refine ⟨2285458040830622079863147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24378219102193302185206901 2285458040830622079863147)
          ·
            refine ⟨3428187061245933119794721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285458040830622079863147 3428187061245933119794721)
            ·
              refine ⟨2571140295934449839846041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428187061245933119794721 2571140295934449839846041)
              ·
                refine ⟨1928355221950837379884531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571140295934449839846041 1928355221950837379884531)
                ·
                  refine ⟨2892532832926256069826797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928355221950837379884531 2892532832926256069826797)
                  ·
                    refine ⟨1084699812347346026185049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892532832926256069826797 1084699812347346026185049)
                    ·
                      refine ⟨813524859260509519638787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084699812347346026185049 813524859260509519638787)
                      ·
                        rfl

theorem cell23_1584334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_1584334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584334 prefixEnd_1584334 := by exact prefixLift 1584334
  have htrace : WordTrace (prefixWord ++ tailWord_1584334) baseStart_1584334 baseEnd_1584334 := by
    simpa [prefixWord, tailWord_1584334, baseEnd_1584334] using wordTrace_append hprefix tailTrace_1584334
  have hstable : (prefixWord ++ tailWord_1584334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584334).length < 2 ^ (prefixWord ++ tailWord_1584334).sum := by decide
  have hdescent : baseEnd_1584334 < baseStart_1584334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584420 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1584420 : Nat := 118140960795 + 1584420 * 2 ^ 59
def prefixEnd_1584420 : Nat := 4983230072969 + 3 ^ 40 * 1584420 * 2
def baseEnd_1584420 : Nat := 813569018596796183163391

theorem tailTrace_1584420 : CollatzResearch.WordTrace tailWord_1584420 prefixEnd_1584420 813569018596796183163391 := by
  unfold tailWord_1584420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28894272459962206118875357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38525696613282941491833809 28894272459962206118875357)
  ·
    refine ⟨10835352172485827294578259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28894272459962206118875357 10835352172485827294578259)
    ·
      refine ⟨16253028258728740941867389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835352172485827294578259 16253028258728740941867389)
      ·
        refine ⟨6094885597023277853200271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16253028258728740941867389 6094885597023277853200271)
        ·
          refine ⟨9142328395534916779800407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6094885597023277853200271 9142328395534916779800407)
          ·
            refine ⟨13713492593302375169700611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9142328395534916779800407 13713492593302375169700611)
            ·
              refine ⟨20570238889953562754550917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13713492593302375169700611 20570238889953562754550917)
              ·
                refine ⟨3856919791866293016478297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20570238889953562754550917 3856919791866293016478297)
                ·
                  refine ⟨2892689843899719762358723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856919791866293016478297 2892689843899719762358723)
                  ·
                    refine ⟨4339034765849579643538085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892689843899719762358723 4339034765849579643538085)
                    ·
                      refine ⟨813569018596796183163391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4339034765849579643538085 813569018596796183163391)
                      ·
                        rfl

theorem cell23_1584420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1584420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584420 prefixEnd_1584420 := by exact prefixLift 1584420
  have htrace : WordTrace (prefixWord ++ tailWord_1584420) baseStart_1584420 baseEnd_1584420 := by
    simpa [prefixWord, tailWord_1584420, baseEnd_1584420] using wordTrace_append hprefix tailTrace_1584420
  have hstable : (prefixWord ++ tailWord_1584420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584420).length < 2 ^ (prefixWord ++ tailWord_1584420).sum := by decide
  have hdescent : baseEnd_1584420 < baseStart_1584420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584437 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_1584437 : Nat := 118140960795 + 1584437 * 2 ^ 59
def prefixEnd_1584437 : Nat := 4983230072969 + 3 ^ 40 * 1584437 * 2
def baseEnd_1584437 : Nat := 813577747767922616650813

theorem tailTrace_1584437 : CollatzResearch.WordTrace tailWord_1584437 prefixEnd_1584437 813577747767922616650813 := by
  unfold tailWord_1584437
  simp only [CollatzResearch.WordTrace]
  refine ⟨57789164960862824141119565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38526109973908549427413043 57789164960862824141119565)
  ·
    refine ⟨21670936860323559052919837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57789164960862824141119565 21670936860323559052919837)
    ·
      refine ⟨8126601322621334644844939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21670936860323559052919837 8126601322621334644844939)
      ·
        refine ⟨12189901983932001967267409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126601322621334644844939 12189901983932001967267409)
        ·
          refine ⟨9142426487949001475450557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12189901983932001967267409 9142426487949001475450557)
          ·
            refine ⟨3428409932980875553293959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9142426487949001475450557 3428409932980875553293959)
            ·
              refine ⟨5142614899471313329940939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428409932980875553293959 5142614899471313329940939)
              ·
                refine ⟨7713922349206969994911409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142614899471313329940939 7713922349206969994911409)
                ·
                  refine ⟨5785441761905227496183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713922349206969994911409 5785441761905227496183557)
                  ·
                    refine ⟨1084770330357230155534417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5785441761905227496183557 1084770330357230155534417)
                    ·
                      refine ⟨813577747767922616650813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084770330357230155534417 813577747767922616650813)
                      ·
                        rfl

theorem cell23_1584437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_1584437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584437 prefixEnd_1584437 := by exact prefixLift 1584437
  have htrace : WordTrace (prefixWord ++ tailWord_1584437) baseStart_1584437 baseEnd_1584437 := by
    simpa [prefixWord, tailWord_1584437, baseEnd_1584437] using wordTrace_append hprefix tailTrace_1584437
  have hstable : (prefixWord ++ tailWord_1584437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584437).length < 2 ^ (prefixWord ++ tailWord_1584437).sum := by decide
  have hdescent : baseEnd_1584437 < baseStart_1584437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584533 : List Nat := [1, 3, 2, 1, 1, 2, 13]
def baseStart_1584533 : Nat := 118140960795 + 1584533 * 2 ^ 59
def prefixEnd_1584533 : Nat := 4983230072969 + 3 ^ 40 * 1584533 * 2
def baseEnd_1584533 : Nat := 10044778295194496803091

theorem tailTrace_1584533 : CollatzResearch.WordTrace tailWord_1584533 prefixEnd_1584533 10044778295194496803091 := by
  unfold tailWord_1584533
  simp only [CollatzResearch.WordTrace]
  refine ⟨57792666368515032536614253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38528444245676688357742835 57792666368515032536614253)
  ·
    refine ⟨21672249888193137201230345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57792666368515032536614253 21672249888193137201230345)
    ·
      refine ⟨16254187416144852900922759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21672249888193137201230345 16254187416144852900922759)
      ·
        refine ⟨24381281124217279351384139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254187416144852900922759 24381281124217279351384139)
        ·
          refine ⟨36571921686325919027076209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24381281124217279351384139 36571921686325919027076209)
          ·
            refine ⟨27428941264744439270307157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36571921686325919027076209 27428941264744439270307157)
            ·
              refine ⟨10044778295194496803091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 27428941264744439270307157 10044778295194496803091)
              ·
                rfl

theorem cell23_1584533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 13].length) (baseStart_1584533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584533 prefixEnd_1584533 := by exact prefixLift 1584533
  have htrace : WordTrace (prefixWord ++ tailWord_1584533) baseStart_1584533 baseEnd_1584533 := by
    simpa [prefixWord, tailWord_1584533, baseEnd_1584533] using wordTrace_append hprefix tailTrace_1584533
  have hstable : (prefixWord ++ tailWord_1584533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584533).length < 2 ^ (prefixWord ++ tailWord_1584533).sum := by decide
  have hdescent : baseEnd_1584533 < baseStart_1584533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584557 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1584557 : Nat := 118140960795 + 1584557 * 2 ^ 59
def prefixEnd_1584557 : Nat := 4983230072969 + 3 ^ 40 * 1584557 * 2
def baseEnd_1584557 : Nat := 813639365446462147150261

theorem tailTrace_1584557 : CollatzResearch.WordTrace tailWord_1584557 prefixEnd_1584557 813639365446462147150261 := by
  unfold tailWord_1584557
  simp only [CollatzResearch.WordTrace]
  refine ⟨57793541720428084635487925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38529027813618723090325283 57793541720428084635487925)
  ·
    refine ⟨5418144536290132934576993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57793541720428084635487925 5418144536290132934576993)
    ·
      refine ⟨4063608402217599700932745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5418144536290132934576993 4063608402217599700932745)
      ·
        refine ⟨3047706301663199775699559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4063608402217599700932745 3047706301663199775699559)
        ·
          refine ⟨4571559452494799663549339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047706301663199775699559 4571559452494799663549339)
          ·
            refine ⟨6857339178742199495324009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571559452494799663549339 6857339178742199495324009)
            ·
              refine ⟨5143004384056649621493007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6857339178742199495324009 5143004384056649621493007)
              ·
                refine ⟨7714506576084974432239511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143004384056649621493007 7714506576084974432239511)
                ·
                  refine ⟨11571759864127461648359267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714506576084974432239511 11571759864127461648359267)
                  ·
                    refine ⟨17357639796191192472538901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11571759864127461648359267 17357639796191192472538901)
                    ·
                      refine ⟨813639365446462147150261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17357639796191192472538901 813639365446462147150261)
                      ·
                        rfl

theorem cell23_1584557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1584557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584557 prefixEnd_1584557 := by exact prefixLift 1584557
  have htrace : WordTrace (prefixWord ++ tailWord_1584557) baseStart_1584557 baseEnd_1584557 := by
    simpa [prefixWord, tailWord_1584557, baseEnd_1584557] using wordTrace_append hprefix tailTrace_1584557
  have hstable : (prefixWord ++ tailWord_1584557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584557).length < 2 ^ (prefixWord ++ tailWord_1584557).sum := by decide
  have hdescent : baseEnd_1584557 < baseStart_1584557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584590 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1584590 : Nat := 118140960795 + 1584590 * 2 ^ 59
def prefixEnd_1584590 : Nat := 4983230072969 + 3 ^ 40 * 1584590 * 2
def baseEnd_1584590 : Nat := 813656310308060518037609

theorem tailTrace_1584590 : CollatzResearch.WordTrace tailWord_1584590 prefixEnd_1584590 813656310308060518037609 := by
  unfold tailWord_1584590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224343166163566408929903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38529830219539020847626149 7224343166163566408929903)
  ·
    refine ⟨10836514749245349613394855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224343166163566408929903 10836514749245349613394855)
    ·
      refine ⟨16254772123868024420092283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836514749245349613394855 16254772123868024420092283)
      ·
        refine ⟨24382158185802036630138425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254772123868024420092283 24382158185802036630138425)
        ·
          refine ⟨18286618639351527472603819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24382158185802036630138425 18286618639351527472603819)
          ·
            refine ⟨27429927959027291208905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286618639351527472603819 27429927959027291208905729)
            ·
              refine ⟨20572445969270468406679297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27429927959027291208905729 20572445969270468406679297)
              ·
                refine ⟨15429334476952851305009473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20572445969270468406679297 15429334476952851305009473)
                ·
                  refine ⟨11572000857714638478757105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15429334476952851305009473 11572000857714638478757105)
                  ·
                    refine ⟨8679000643285978859067829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11572000857714638478757105 8679000643285978859067829)
                    ·
                      refine ⟨813656310308060518037609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8679000643285978859067829 813656310308060518037609)
                      ·
                        rfl

theorem cell23_1584590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1584590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584590 prefixEnd_1584590 := by exact prefixLift 1584590
  have htrace : WordTrace (prefixWord ++ tailWord_1584590) baseStart_1584590 baseEnd_1584590 := by
    simpa [prefixWord, tailWord_1584590, baseEnd_1584590] using wordTrace_append hprefix tailTrace_1584590
  have hstable : (prefixWord ++ tailWord_1584590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584590).length < 2 ^ (prefixWord ++ tailWord_1584590).sum := by decide
  have hdescent : baseEnd_1584590 < baseStart_1584590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584600 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1584600 : Nat := 118140960795 + 1584600 * 2 ^ 59
def prefixEnd_1584600 : Nat := 4983230072969 + 3 ^ 40 * 1584600 * 2
def baseEnd_1584600 : Nat := 813661445114605478912563

theorem tailTrace_1584600 : CollatzResearch.WordTrace tailWord_1584600 prefixEnd_1584600 813661445114605478912563 := by
  unfold tailWord_1584600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897555029636151489651627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38530073372848201986202169 28897555029636151489651627)
  ·
    refine ⟨43346332544454227234477441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28897555029636151489651627 43346332544454227234477441)
    ·
      refine ⟨32509749408340670425858081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43346332544454227234477441 32509749408340670425858081)
      ·
        refine ⟨24382312056255502819393561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32509749408340670425858081 24382312056255502819393561)
        ·
          refine ⟨18286734042191627114545171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24382312056255502819393561 18286734042191627114545171)
          ·
            refine ⟨27430101063287440671817757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286734042191627114545171 27430101063287440671817757)
            ·
              refine ⟨10286287898732790251931659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27430101063287440671817757 10286287898732790251931659)
              ·
                refine ⟨15429431848099185377897489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286287898732790251931659 15429431848099185377897489)
                ·
                  refine ⟨11572073886074389033423117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15429431848099185377897489 11572073886074389033423117)
                  ·
                    refine ⟨4339527707277895887533669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11572073886074389033423117 4339527707277895887533669)
                    ·
                      refine ⟨813661445114605478912563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4339527707277895887533669 813661445114605478912563)
                      ·
                        rfl

theorem cell23_1584600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1584600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584600 prefixEnd_1584600 := by exact prefixLift 1584600
  have htrace : WordTrace (prefixWord ++ tailWord_1584600) baseStart_1584600 baseEnd_1584600 := by
    simpa [prefixWord, tailWord_1584600, baseEnd_1584600] using wordTrace_append hprefix tailTrace_1584600
  have hstable : (prefixWord ++ tailWord_1584600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584600).length < 2 ^ (prefixWord ++ tailWord_1584600).sum := by decide
  have hdescent : baseEnd_1584600 < baseStart_1584600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584620 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1584620 : Nat := 118140960795 + 1584620 * 2 ^ 59
def prefixEnd_1584620 : Nat := 4983230072969 + 3 ^ 40 * 1584620 * 2
def baseEnd_1584620 : Nat := 813671714727695400662471

theorem tailTrace_1584620 : CollatzResearch.WordTrace tailWord_1584620 prefixEnd_1584620 813671714727695400662471 := by
  unfold tailWord_1584620
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897919759599923197515657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38530559679466564263354209 28897919759599923197515657)
  ·
    refine ⟨21673439819699942398136743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28897919759599923197515657 21673439819699942398136743)
    ·
      refine ⟨32510159729549913597205115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673439819699942398136743 32510159729549913597205115)
      ·
        refine ⟨48765239594324870395807673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32510159729549913597205115 48765239594324870395807673)
        ·
          refine ⟨36573929695743652796855755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48765239594324870395807673 36573929695743652796855755)
          ·
            refine ⟨54860894543615479195283633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36573929695743652796855755 54860894543615479195283633)
            ·
              refine ⟨41145670907711609396462725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54860894543615479195283633 41145670907711609396462725)
              ·
                refine ⟨7714813295195926761836761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41145670907711609396462725 7714813295195926761836761)
                ·
                  refine ⟨5786109971396945071377571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714813295195926761836761 5786109971396945071377571)
                  ·
                    refine ⟨8679164957095417607066357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5786109971396945071377571 8679164957095417607066357)
                    ·
                      refine ⟨813671714727695400662471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8679164957095417607066357 813671714727695400662471)
                      ·
                        rfl

theorem cell23_1584620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1584620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584620 prefixEnd_1584620 := by exact prefixLift 1584620
  have htrace : WordTrace (prefixWord ++ tailWord_1584620) baseStart_1584620 baseEnd_1584620 := by
    simpa [prefixWord, tailWord_1584620, baseEnd_1584620] using wordTrace_append hprefix tailTrace_1584620
  have hstable : (prefixWord ++ tailWord_1584620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584620).length < 2 ^ (prefixWord ++ tailWord_1584620).sum := by decide
  have hdescent : baseEnd_1584620 < baseStart_1584620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584634 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_1584634 : Nat := 118140960795 + 1584634 * 2 ^ 59
def prefixEnd_1584634 : Nat := 4983230072969 + 3 ^ 40 * 1584634 * 2
def baseEnd_1584634 : Nat := 813678903456858345887407

theorem tailTrace_1584634 : CollatzResearch.WordTrace tailWord_1584634 prefixEnd_1584634 813678903456858345887407 := by
  unfold tailWord_1584634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449087535287281696510239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38530900094099417857360637 14449087535287281696510239)
  ·
    refine ⟨21673631302930922544765359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14449087535287281696510239 21673631302930922544765359)
    ·
      refine ⟨32510446954396383817148039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673631302930922544765359 32510446954396383817148039)
      ·
        refine ⟨48765670431594575725722059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32510446954396383817148039 48765670431594575725722059)
        ·
          refine ⟨73148505647391863588583089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48765670431594575725722059 73148505647391863588583089)
          ·
            refine ⟨54861379235543897691437317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73148505647391863588583089 54861379235543897691437317)
            ·
              refine ⟨10286508606664480817144497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54861379235543897691437317 10286508606664480817144497)
              ·
                refine ⟨7714881454998360612858373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10286508606664480817144497 7714881454998360612858373)
                ·
                  refine ⟨1446540272812192614910945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7714881454998360612858373 1446540272812192614910945)
                  ·
                    refine ⟨1084905204609144461183209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446540272812192614910945 1084905204609144461183209)
                    ·
                      refine ⟨813678903456858345887407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084905204609144461183209 813678903456858345887407)
                      ·
                        rfl

theorem cell23_1584634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_1584634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584634 prefixEnd_1584634 := by exact prefixLift 1584634
  have htrace : WordTrace (prefixWord ++ tailWord_1584634) baseStart_1584634 baseEnd_1584634 := by
    simpa [prefixWord, tailWord_1584634, baseEnd_1584634] using wordTrace_append hprefix tailTrace_1584634
  have hstable : (prefixWord ++ tailWord_1584634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584634).length < 2 ^ (prefixWord ++ tailWord_1584634).sum := by decide
  have hdescent : baseEnd_1584634 < baseStart_1584634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584647 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1584647 : Nat := 118140960795 + 1584647 * 2 ^ 59
def prefixEnd_1584647 : Nat := 4983230072969 + 3 ^ 40 * 1584647 * 2
def baseEnd_1584647 : Nat := 813685578705366795024847

theorem tailTrace_1584647 : CollatzResearch.WordTrace tailWord_1584647 prefixEnd_1584647 813685578705366795024847 := by
  unfold tailWord_1584647
  simp only [CollatzResearch.WordTrace]
  refine ⟨57796824290102030006264195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38531216193401353337509463 57796824290102030006264195)
  ·
    refine ⟨86695236435153045009396293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57796824290102030006264195 86695236435153045009396293)
    ·
      refine ⟨16255356831591195939261805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86695236435153045009396293 16255356831591195939261805)
      ·
        refine ⟨6095758811846698477223177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16255356831591195939261805 6095758811846698477223177)
        ·
          refine ⟨4571819108885023857917383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6095758811846698477223177 4571819108885023857917383)
          ·
            refine ⟨6857728663327535786876075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571819108885023857917383 6857728663327535786876075)
            ·
              refine ⟨10286592994991303680314113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857728663327535786876075 10286592994991303680314113)
              ·
                refine ⟨7714944746243477760235585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10286592994991303680314113 7714944746243477760235585)
                ·
                  refine ⟨5786208559682608320176689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714944746243477760235585 5786208559682608320176689)
                  ·
                    refine ⟨4339656419761956240132517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786208559682608320176689 4339656419761956240132517)
                    ·
                      refine ⟨813685578705366795024847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4339656419761956240132517 813685578705366795024847)
                      ·
                        rfl

theorem cell23_1584647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1584647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584647 prefixEnd_1584647 := by exact prefixLift 1584647
  have htrace : WordTrace (prefixWord ++ tailWord_1584647) baseStart_1584647 baseEnd_1584647 := by
    simpa [prefixWord, tailWord_1584647, baseEnd_1584647] using wordTrace_append hprefix tailTrace_1584647
  have hstable : (prefixWord ++ tailWord_1584647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584647).length < 2 ^ (prefixWord ++ tailWord_1584647).sum := by decide
  have hdescent : baseEnd_1584647 < baseStart_1584647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584651 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 4, 2, 2]
def baseStart_1584651 : Nat := 118140960795 + 1584651 * 2 ^ 59
def prefixEnd_1584651 : Nat := 4983230072969 + 3 ^ 40 * 1584651 * 2
def baseEnd_1584651 : Nat := 813687632627984779374829

theorem tailTrace_1584651 : CollatzResearch.WordTrace tailWord_1584651 prefixEnd_1584651 813687632627984779374829 := by
  unfold tailWord_1584651
  simp only [CollatzResearch.WordTrace]
  refine ⟨57796970182087538689409807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38531313454725025792939871 57796970182087538689409807)
  ·
    refine ⟨86695455273131308034114711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57796970182087538689409807 86695455273131308034114711)
    ·
      refine ⟨130043182909696962051172067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86695455273131308034114711 130043182909696962051172067)
      ·
        refine ⟨195064774364545443076758101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130043182909696962051172067 195064774364545443076758101)
        ·
          refine ⟨2285915324584516911055759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 195064774364545443076758101 2285915324584516911055759)
          ·
            refine ⟨3428872986876775366583639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285915324584516911055759 3428872986876775366583639)
            ·
              refine ⟨5143309480315163049875459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428872986876775366583639 5143309480315163049875459)
              ·
                refine ⟨7714964220472744574813189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143309480315163049875459 7714964220472744574813189)
                ·
                  refine ⟨1446555791338639607777473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7714964220472744574813189 1446555791338639607777473)
                  ·
                    refine ⟨1084916843503979705833105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446555791338639607777473 1084916843503979705833105)
                    ·
                      refine ⟨813687632627984779374829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084916843503979705833105 813687632627984779374829)
                      ·
                        rfl

theorem cell23_1584651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 2, 2].length) (baseStart_1584651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584651 prefixEnd_1584651 := by exact prefixLift 1584651
  have htrace : WordTrace (prefixWord ++ tailWord_1584651) baseStart_1584651 baseEnd_1584651 := by
    simpa [prefixWord, tailWord_1584651, baseEnd_1584651] using wordTrace_append hprefix tailTrace_1584651
  have hstable : (prefixWord ++ tailWord_1584651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584651).length < 2 ^ (prefixWord ++ tailWord_1584651).sum := by decide
  have hdescent : baseEnd_1584651 < baseStart_1584651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584657 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 5]
def baseStart_1584657 : Nat := 118140960795 + 1584657 * 2 ^ 59
def prefixEnd_1584657 : Nat := 4983230072969 + 3 ^ 40 * 1584657 * 2
def baseEnd_1584657 : Nat := 90410079279101306211089

theorem tailTrace_1584657 : CollatzResearch.WordTrace tailWord_1584657 prefixEnd_1584657 90410079279101306211089 := by
  unfold tailWord_1584657
  simp only [CollatzResearch.WordTrace]
  refine ⟨57797189020065801714128225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38531459346710534476085483 57797189020065801714128225)
  ·
    refine ⟨43347891765049351285596169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57797189020065801714128225 43347891765049351285596169)
    ·
      refine ⟨32510918823787013464197127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43347891765049351285596169 32510918823787013464197127)
      ·
        refine ⟨48766378235680520196295691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32510918823787013464197127 48766378235680520196295691)
        ·
          refine ⟨73149567353520780294443537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48766378235680520196295691 73149567353520780294443537)
          ·
            refine ⟨54862175515140585220832653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73149567353520780294443537 54862175515140585220832653)
            ·
              refine ⟨20573315818177719457812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54862175515140585220832653 20573315818177719457812245)
              ·
                refine ⟨964374178977080599584949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20573315818177719457812245 964374178977080599584949)
                ·
                  refine ⟨90410079279101306211089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 964374178977080599584949 90410079279101306211089)
                  ·
                    rfl

theorem cell23_1584657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 5].length) (baseStart_1584657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584657 prefixEnd_1584657 := by exact prefixLift 1584657
  have htrace : WordTrace (prefixWord ++ tailWord_1584657) baseStart_1584657 baseEnd_1584657 := by
    simpa [prefixWord, tailWord_1584657, baseEnd_1584657] using wordTrace_append hprefix tailTrace_1584657
  have hstable : (prefixWord ++ tailWord_1584657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584657).length < 2 ^ (prefixWord ++ tailWord_1584657).sum := by decide
  have hdescent : baseEnd_1584657 < baseStart_1584657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584668 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1584668 : Nat := 118140960795 + 1584668 * 2 ^ 59
def prefixEnd_1584668 : Nat := 4983230072969 + 3 ^ 40 * 1584668 * 2
def baseEnd_1584668 : Nat := 813696361799111212862251

theorem tailTrace_1584668 : CollatzResearch.WordTrace tailWord_1584668 prefixEnd_1584668 813696361799111212862251 := by
  unfold tailWord_1584668
  simp only [CollatzResearch.WordTrace]
  refine ⟨28898795111512975296389329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38531726815350633728519105 28898795111512975296389329)
  ·
    refine ⟨21674096333634731472291997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28898795111512975296389329 21674096333634731472291997)
    ·
      refine ⟨8127786125113024302109499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21674096333634731472291997 8127786125113024302109499)
      ·
        refine ⟨12191679187669536453164249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8127786125113024302109499 12191679187669536453164249)
        ·
          refine ⟨9143759390752152339873187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12191679187669536453164249 9143759390752152339873187)
          ·
            refine ⟨13715639086128228509809781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143759390752152339873187 13715639086128228509809781)
            ·
              refine ⟨1285841164324521422794667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13715639086128228509809781 1285841164324521422794667)
              ·
                refine ⟨1928761746486782134192001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285841164324521422794667 1928761746486782134192001)
                ·
                  refine ⟨1446571309865086600644001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1928761746486782134192001 1446571309865086600644001)
                  ·
                    refine ⟨1084928482398814950483001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446571309865086600644001 1084928482398814950483001)
                    ·
                      refine ⟨813696361799111212862251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084928482398814950483001 813696361799111212862251)
                      ·
                        rfl

theorem cell23_1584668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1584668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584668 prefixEnd_1584668 := by exact prefixLift 1584668
  have htrace : WordTrace (prefixWord ++ tailWord_1584668) baseStart_1584668 baseEnd_1584668 := by
    simpa [prefixWord, tailWord_1584668, baseEnd_1584668] using wordTrace_append hprefix tailTrace_1584668
  have hstable : (prefixWord ++ tailWord_1584668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584668).length < 2 ^ (prefixWord ++ tailWord_1584668).sum := by decide
  have hdescent : baseEnd_1584668 < baseStart_1584668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584724 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_1584724 : Nat := 118140960795 + 1584724 * 2 ^ 59
def prefixEnd_1584724 : Nat := 4983230072969 + 3 ^ 40 * 1584724 * 2
def baseEnd_1584724 : Nat := 813725116715762993761993

theorem tailTrace_1584724 : CollatzResearch.WordTrace tailWord_1584724 prefixEnd_1584724 813725116715762993761993 := by
  unfold tailWord_1584724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28899816355411536078408613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38533088473882048104544817 28899816355411536078408613)
  ·
    refine ⟨5418715566639663014701615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28899816355411536078408613 5418715566639663014701615)
    ·
      refine ⟨8128073349959494522052423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5418715566639663014701615 8128073349959494522052423)
      ·
        refine ⟨12192110024939241783078635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128073349959494522052423 12192110024939241783078635)
        ·
          refine ⟨18288165037408862674617953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12192110024939241783078635 18288165037408862674617953)
          ·
            refine ⟨13716123778056647005963465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18288165037408862674617953 13716123778056647005963465)
            ·
              refine ⟨10287092833542485254472599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13716123778056647005963465 10287092833542485254472599)
              ·
                refine ⟨15430639250313727881708899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10287092833542485254472599 15430639250313727881708899)
                ·
                  refine ⟨23145958875470591822563349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15430639250313727881708899 23145958875470591822563349)
                  ·
                    refine ⟨1084966822287683991682657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23145958875470591822563349 1084966822287683991682657)
                    ·
                      refine ⟨813725116715762993761993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1084966822287683991682657 813725116715762993761993)
                      ·
                        rfl

theorem cell23_1584724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_1584724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584724 prefixEnd_1584724 := by exact prefixLift 1584724
  have htrace : WordTrace (prefixWord ++ tailWord_1584724) baseStart_1584724 baseEnd_1584724 := by
    simpa [prefixWord, tailWord_1584724, baseEnd_1584724] using wordTrace_append hprefix tailTrace_1584724
  have hstable : (prefixWord ++ tailWord_1584724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584724).length < 2 ^ (prefixWord ++ tailWord_1584724).sum := by decide
  have hdescent : baseEnd_1584724 < baseStart_1584724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584777 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_1584777 : Nat := 118140960795 + 1584777 * 2 ^ 59
def prefixEnd_1584777 : Nat := 4983230072969 + 3 ^ 40 * 1584777 * 2
def baseEnd_1584777 : Nat := 271250777063483762133083

theorem tailTrace_1584777 : CollatzResearch.WordTrace tailWord_1584777 prefixEnd_1584777 271250777063483762133083 := by
  unfold tailWord_1584777
  simp only [CollatzResearch.WordTrace]
  refine ⟨57801565779631062208496585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38534377186420708138997723 57801565779631062208496585)
  ·
    refine ⟨43351174334723296656372439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57801565779631062208496585 43351174334723296656372439)
    ·
      refine ⟨65026761502084944984558659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43351174334723296656372439 65026761502084944984558659)
      ·
        refine ⟨97540142253127417476837989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65026761502084944984558659 97540142253127417476837989)
        ·
          refine ⟨18288776672461390776907123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97540142253127417476837989 18288776672461390776907123)
          ·
            refine ⟨27433165008692086165360685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18288776672461390776907123 27433165008692086165360685)
            ·
              refine ⟨10287436878259532312010257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27433165008692086165360685 10287436878259532312010257)
              ·
                refine ⟨7715577658694649234007693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10287436878259532312010257 7715577658694649234007693)
                ·
                  refine ⟨2893341622010493462752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7715577658694649234007693 2893341622010493462752885)
                  ·
                    refine ⟨271250777063483762133083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2893341622010493462752885 271250777063483762133083)
                    ·
                      rfl

theorem cell23_1584777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_1584777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584777 prefixEnd_1584777 := by exact prefixLift 1584777
  have htrace : WordTrace (prefixWord ++ tailWord_1584777) baseStart_1584777 baseEnd_1584777 := by
    simpa [prefixWord, tailWord_1584777, baseEnd_1584777] using wordTrace_append hprefix tailTrace_1584777
  have hstable : (prefixWord ++ tailWord_1584777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584777).length < 2 ^ (prefixWord ++ tailWord_1584777).sum := by decide
  have hdescent : baseEnd_1584777 < baseStart_1584777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2]
def baseStart_1584784 : Nat := 118140960795 + 1584784 * 2 ^ 59
def prefixEnd_1584784 : Nat := 4983230072969 + 3 ^ 40 * 1584784 * 2
def baseEnd_1584784 : Nat := 813755925555032759011717

theorem tailTrace_1584784 : CollatzResearch.WordTrace tailWord_1584784 prefixEnd_1584784 813755925555032759011717 := by
  unfold tailWord_1584784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900910545302851202000703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38534547393737134936000937 28900910545302851202000703)
  ·
    refine ⟨43351365817954276803001055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28900910545302851202000703 43351365817954276803001055)
    ·
      refine ⟨65027048726931415204501583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43351365817954276803001055 65027048726931415204501583)
      ·
        refine ⟨97540573090397122806752375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65027048726931415204501583 97540573090397122806752375)
        ·
          refine ⟨146310859635595684210128563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97540573090397122806752375 146310859635595684210128563)
          ·
            refine ⟨219466289453393526315192845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146310859635595684210128563 219466289453393526315192845)
            ·
              refine ⟨82299858545022572368197317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219466289453393526315192845 82299858545022572368197317)
              ·
                refine ⟨15431223477191732319036997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82299858545022572368197317 15431223477191732319036997)
                ·
                  refine ⟨2893354401973449809819437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15431223477191732319036997 2893354401973449809819437)
                  ·
                    refine ⟨1085007900740043678682289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893354401973449809819437 1085007900740043678682289)
                    ·
                      refine ⟨813755925555032759011717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085007900740043678682289 813755925555032759011717)
                      ·
                        rfl

theorem cell23_1584784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2].length) (baseStart_1584784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584784 prefixEnd_1584784 := by exact prefixLift 1584784
  have htrace : WordTrace (prefixWord ++ tailWord_1584784) baseStart_1584784 baseEnd_1584784 := by
    simpa [prefixWord, tailWord_1584784, baseEnd_1584784] using wordTrace_append hprefix tailTrace_1584784
  have hstable : (prefixWord ++ tailWord_1584784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584784).length < 2 ^ (prefixWord ++ tailWord_1584784).sum := by decide
  have hdescent : baseEnd_1584784 < baseStart_1584784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584791 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1584791 : Nat := 118140960795 + 1584791 * 2 ^ 59
def prefixEnd_1584791 : Nat := 4983230072969 + 3 ^ 40 * 1584791 * 2
def baseEnd_1584791 : Nat := 813759519919614231624185

theorem tailTrace_1584791 : CollatzResearch.WordTrace tailWord_1584791 prefixEnd_1584791 813759519919614231624185 := by
  unfold tailWord_1584791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57802076401580342599506227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38534717601053561733004151 57802076401580342599506227)
  ·
    refine ⟨86703114602370513899259341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57802076401580342599506227 86703114602370513899259341)
    ·
      refine ⟨32513667975888942712222253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86703114602370513899259341 32513667975888942712222253)
      ·
        refine ⟨12192625490958353517083345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32513667975888942712222253 12192625490958353517083345)
        ·
          refine ⟨9144469118218765137812509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12192625490958353517083345 9144469118218765137812509)
          ·
            refine ⟨3429175919332036926679691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9144469118218765137812509 3429175919332036926679691)
            ·
              refine ⟨5143763878998055390019537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429175919332036926679691 5143763878998055390019537)
              ·
                refine ⟨3857822909248541542514653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143763878998055390019537 3857822909248541542514653)
                ·
                  refine ⟨1446683590968203078442995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3857822909248541542514653 1446683590968203078442995)
                  ·
                    refine ⟨2170025386452304617664493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1446683590968203078442995 2170025386452304617664493)
                    ·
                      refine ⟨813759519919614231624185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170025386452304617664493 813759519919614231624185)
                      ·
                        rfl

theorem cell23_1584791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1584791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584791 prefixEnd_1584791 := by exact prefixLift 1584791
  have htrace : WordTrace (prefixWord ++ tailWord_1584791) baseStart_1584791 baseEnd_1584791 := by
    simpa [prefixWord, tailWord_1584791, baseEnd_1584791] using wordTrace_append hprefix tailTrace_1584791
  have hstable : (prefixWord ++ tailWord_1584791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584791).length < 2 ^ (prefixWord ++ tailWord_1584791).sum := by decide
  have hdescent : baseEnd_1584791 < baseStart_1584791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584801 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1584801 : Nat := 118140960795 + 1584801 * 2 ^ 59
def prefixEnd_1584801 : Nat := 4983230072969 + 3 ^ 40 * 1584801 * 2
def baseEnd_1584801 : Nat := 813764654726159192499139

theorem tailTrace_1584801 : CollatzResearch.WordTrace tailWord_1584801 prefixEnd_1584801 813764654726159192499139 := by
  unfold tailWord_1584801
  simp only [CollatzResearch.WordTrace]
  refine ⟨57802441131544114307370257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38534960754362742871580171 57802441131544114307370257)
  ·
    refine ⟨43351830848658085730527693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57802441131544114307370257 43351830848658085730527693)
    ·
      refine ⟨16256936568246782148947885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43351830848658085730527693 16256936568246782148947885)
      ·
        refine ⟨6096351213092543305855457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16256936568246782148947885 6096351213092543305855457)
        ·
          refine ⟨4572263409819407479391593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6096351213092543305855457 4572263409819407479391593)
          ·
            refine ⟨3429197557364555609543695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4572263409819407479391593 3429197557364555609543695)
            ·
              refine ⟨5143796336046833414315543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429197557364555609543695 5143796336046833414315543)
              ·
                refine ⟨7715694504070250121473315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143796336046833414315543 7715694504070250121473315)
                ·
                  refine ⟨11573541756105375182209973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715694504070250121473315 11573541756105375182209973)
                  ·
                    refine ⟨1085019539634878923332185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11573541756105375182209973 1085019539634878923332185)
                    ·
                      refine ⟨813764654726159192499139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085019539634878923332185 813764654726159192499139)
                      ·
                        rfl

theorem cell23_1584801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1584801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584801 prefixEnd_1584801 := by exact prefixLift 1584801
  have htrace : WordTrace (prefixWord ++ tailWord_1584801) baseStart_1584801 baseEnd_1584801 := by
    simpa [prefixWord, tailWord_1584801, baseEnd_1584801] using wordTrace_append hprefix tailTrace_1584801
  have hstable : (prefixWord ++ tailWord_1584801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584801).length < 2 ^ (prefixWord ++ tailWord_1584801).sum := by decide
  have hdescent : baseEnd_1584801 < baseStart_1584801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584827 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_1584827 : Nat := 118140960795 + 1584827 * 2 ^ 59
def prefixEnd_1584827 : Nat := 4983230072969 + 3 ^ 40 * 1584827 * 2
def baseEnd_1584827 : Nat := 813778005223176090774019

theorem tailTrace_1584827 : CollatzResearch.WordTrace tailWord_1584827 prefixEnd_1584827 813778005223176090774019 := by
  unfold tailWord_1584827
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803389429449920747816735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38535592952966613831877823 57803389429449920747816735)
  ·
    refine ⟨86705084144174881121725103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57803389429449920747816735 86705084144174881121725103)
    ·
      refine ⟨130057626216262321682587655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86705084144174881121725103 130057626216262321682587655)
      ·
        refine ⟨195086439324393482523881483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130057626216262321682587655 195086439324393482523881483)
        ·
          refine ⟨292629658986590223785822225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195086439324393482523881483 292629658986590223785822225)
          ·
            refine ⟨219472244239942667839366669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292629658986590223785822225 219472244239942667839366669)
            ·
              refine ⟨82302091589978500439762501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219472244239942667839366669 82302091589978500439762501)
              ·
                refine ⟨15431642173120968832455469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82302091589978500439762501 15431642173120968832455469)
                ·
                  refine ⟨5786865814920363312170801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15431642173120968832455469 5786865814920363312170801)
                  ·
                    refine ⟨4340149361190272484128101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786865814920363312170801 4340149361190272484128101)
                    ·
                      refine ⟨813778005223176090774019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4340149361190272484128101 813778005223176090774019)
                      ·
                        rfl

theorem cell23_1584827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_1584827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584827 prefixEnd_1584827 := by exact prefixLift 1584827
  have htrace : WordTrace (prefixWord ++ tailWord_1584827) baseStart_1584827 baseEnd_1584827 := by
    simpa [prefixWord, tailWord_1584827, baseEnd_1584827] using wordTrace_append hprefix tailTrace_1584827
  have hstable : (prefixWord ++ tailWord_1584827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584827).length < 2 ^ (prefixWord ++ tailWord_1584827).sum := by decide
  have hdescent : baseEnd_1584827 < baseStart_1584827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584864 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1584864 : Nat := 118140960795 + 1584864 * 2 ^ 59
def prefixEnd_1584864 : Nat := 4983230072969 + 3 ^ 40 * 1584864 * 2
def baseEnd_1584864 : Nat := 813797004007392446011349

theorem tailTrace_1584864 : CollatzResearch.WordTrace tailWord_1584864 prefixEnd_1584864 813797004007392446011349 := by
  unfold tailWord_1584864
  simp only [CollatzResearch.WordTrace]
  refine ⟨28902369465157938033456823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38536492620210584044609097 28902369465157938033456823)
  ·
    refine ⟨43353554197736907050185235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28902369465157938033456823 43353554197736907050185235)
    ·
      refine ⟨65030331296605360575277853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43353554197736907050185235 65030331296605360575277853)
      ·
        refine ⟨24386374236227010215729195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65030331296605360575277853 24386374236227010215729195)
        ·
          refine ⟨36579561354340515323593793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24386374236227010215729195 36579561354340515323593793)
          ·
            refine ⟨27434671015755386492695345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36579561354340515323593793 27434671015755386492695345)
            ·
              refine ⟨20576003261816539869521509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27434671015755386492695345 20576003261816539869521509)
              ·
                refine ⟨3858000611590601225535283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20576003261816539869521509 3858000611590601225535283)
                ·
                  refine ⟨5787000917385901838302925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858000611590601225535283 5787000917385901838302925)
                  ·
                    refine ⟨2170125344019713189363597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5787000917385901838302925 2170125344019713189363597)
                    ·
                      refine ⟨813797004007392446011349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170125344019713189363597 813797004007392446011349)
                      ·
                        rfl

theorem cell23_1584864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1584864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584864 prefixEnd_1584864 := by exact prefixLift 1584864
  have htrace : WordTrace (prefixWord ++ tailWord_1584864) baseStart_1584864 baseEnd_1584864 := by
    simpa [prefixWord, tailWord_1584864, baseEnd_1584864] using wordTrace_append hprefix tailTrace_1584864
  have hstable : (prefixWord ++ tailWord_1584864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584864).length < 2 ^ (prefixWord ++ tailWord_1584864).sum := by decide
  have hdescent : baseEnd_1584864 < baseStart_1584864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584871 : List Nat := [1, 1, 5, 4, 1, 2, 9]
def baseStart_1584871 : Nat := 118140960795 + 1584871 * 2 ^ 59
def prefixEnd_1584871 : Nat := 4983230072969 + 3 ^ 40 * 1584871 * 2
def baseEnd_1584871 : Nat := 10046920967555233563257

theorem tailTrace_1584871 : CollatzResearch.WordTrace tailWord_1584871 prefixEnd_1584871 10046920967555233563257 := by
  unfold tailWord_1584871
  simp only [CollatzResearch.WordTrace]
  refine ⟨57804994241290516262418467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38536662827527010841612311 57804994241290516262418467)
  ·
    refine ⟨86707491361935774393627701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57804994241290516262418467 86707491361935774393627701)
    ·
      refine ⟨8128827315181478849402597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86707491361935774393627701 8128827315181478849402597)
      ·
        refine ⟨1524155121596527284262987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8128827315181478849402597 1524155121596527284262987)
        ·
          refine ⟨2286232682394790926394481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524155121596527284262987 2286232682394790926394481)
          ·
            refine ⟨1714674511796093194795861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286232682394790926394481 1714674511796093194795861)
            ·
              refine ⟨10046920967555233563257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1714674511796093194795861 10046920967555233563257)
              ·
                rfl

theorem cell23_1584871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 9].length) (baseStart_1584871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584871 prefixEnd_1584871 := by exact prefixLift 1584871
  have htrace : WordTrace (prefixWord ++ tailWord_1584871) baseStart_1584871 baseEnd_1584871 := by
    simpa [prefixWord, tailWord_1584871, baseEnd_1584871] using wordTrace_append hprefix tailTrace_1584871
  have hstable : (prefixWord ++ tailWord_1584871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584871).length < 2 ^ (prefixWord ++ tailWord_1584871).sum := by decide
  have hdescent : baseEnd_1584871 < baseStart_1584871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584881 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_1584881 : Nat := 118140960795 + 1584881 * 2 ^ 59
def prefixEnd_1584881 : Nat := 4983230072969 + 3 ^ 40 * 1584881 * 2
def baseEnd_1584881 : Nat := 813805733178518879498771

theorem tailTrace_1584881 : CollatzResearch.WordTrace tailWord_1584881 prefixEnd_1584881 813805733178518879498771 := by
  unfold tailWord_1584881
  simp only [CollatzResearch.WordTrace]
  refine ⟨57805358971254287970282497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38536905980836191980188331 57805358971254287970282497)
  ·
    refine ⟨43354019228440715977711873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57805358971254287970282497 43354019228440715977711873)
    ·
      refine ⟨32515514421330536983283905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43354019228440715977711873 32515514421330536983283905)
      ·
        refine ⟨24386635815997902737462929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32515514421330536983283905 24386635815997902737462929)
        ·
          refine ⟨18289976861998427053097197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24386635815997902737462929 18289976861998427053097197)
          ·
            refine ⟨6858741323249410144911449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18289976861998427053097197 6858741323249410144911449)
            ·
              refine ⟨5144055992437057608683587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6858741323249410144911449 5144055992437057608683587)
              ·
                refine ⟨7716083988655586413025381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144055992437057608683587 7716083988655586413025381)
                ·
                  refine ⟨1446765747872922452442259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7716083988655586413025381 1446765747872922452442259)
                  ·
                    refine ⟨2170148621809383678663389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1446765747872922452442259 2170148621809383678663389)
                    ·
                      refine ⟨813805733178518879498771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170148621809383678663389 813805733178518879498771)
                      ·
                        rfl

theorem cell23_1584881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_1584881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584881 prefixEnd_1584881 := by exact prefixLift 1584881
  have htrace : WordTrace (prefixWord ++ tailWord_1584881) baseStart_1584881 baseEnd_1584881 := by
    simpa [prefixWord, tailWord_1584881, baseEnd_1584881] using wordTrace_append hprefix tailTrace_1584881
  have hstable : (prefixWord ++ tailWord_1584881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584881).length < 2 ^ (prefixWord ++ tailWord_1584881).sum := by decide
  have hdescent : baseEnd_1584881 < baseStart_1584881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584882 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1584882 : Nat := 118140960795 + 1584882 * 2 ^ 59
def prefixEnd_1584882 : Nat := 4983230072969 + 3 ^ 40 * 1584882 * 2
def baseEnd_1584882 : Nat := 813806246659173375586267

theorem tailTrace_1584882 : CollatzResearch.WordTrace tailWord_1584882 prefixEnd_1584882 813806246659173375586267 := by
  unfold tailWord_1584882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14451348861062666285267225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38536930296167110094045933 14451348861062666285267225)
  ·
    refine ⟨10838511645796999713950419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14451348861062666285267225 10838511645796999713950419)
    ·
      refine ⟨16257767468695499570925629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10838511645796999713950419 16257767468695499570925629)
      ·
        refine ⟨6096662800760812339097111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16257767468695499570925629 6096662800760812339097111)
        ·
          refine ⟨9144994201141218508645667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6096662800760812339097111 9144994201141218508645667)
          ·
            refine ⟨13717491301711827762968501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144994201141218508645667 13717491301711827762968501)
            ·
              refine ⟨1286014809535483852778297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13717491301711827762968501 1286014809535483852778297)
              ·
                refine ⟨964511107151612889583723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286014809535483852778297 964511107151612889583723)
                ·
                  refine ⟨1446766660727419334375585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964511107151612889583723 1446766660727419334375585)
                  ·
                    refine ⟨1085074995545564500781689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446766660727419334375585 1085074995545564500781689)
                    ·
                      refine ⟨813806246659173375586267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085074995545564500781689 813806246659173375586267)
                      ·
                        rfl

theorem cell23_1584882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1584882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584882 prefixEnd_1584882 := by exact prefixLift 1584882
  have htrace : WordTrace (prefixWord ++ tailWord_1584882) baseStart_1584882 baseEnd_1584882 := by
    simpa [prefixWord, tailWord_1584882, baseEnd_1584882] using wordTrace_append hprefix tailTrace_1584882
  have hstable : (prefixWord ++ tailWord_1584882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584882).length < 2 ^ (prefixWord ++ tailWord_1584882).sum := by decide
  have hdescent : baseEnd_1584882 < baseStart_1584882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584908 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_1584908 : Nat := 118140960795 + 1584908 * 2 ^ 59
def prefixEnd_1584908 : Nat := 4983230072969 + 3 ^ 40 * 1584908 * 2
def baseEnd_1584908 : Nat := 813819597156190273861147

theorem tailTrace_1584908 : CollatzResearch.WordTrace tailWord_1584908 prefixEnd_1584908 813819597156190273861147 := by
  unfold tailWord_1584908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903171871078235790757689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38537562494770981054343585 28903171871078235790757689)
  ·
    refine ⟨21677378903308676843068267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28903171871078235790757689 21677378903308676843068267)
    ·
      refine ⟨32516068354963015264602401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21677378903308676843068267 32516068354963015264602401)
      ·
        refine ⟨24387051266222261448451801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32516068354963015264602401 24387051266222261448451801)
        ·
          refine ⟨18290288449666696086338851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24387051266222261448451801 18290288449666696086338851)
          ·
            refine ⟨27435432674500044129508277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18290288449666696086338851 27435432674500044129508277)
            ·
              refine ⟨2572071813234379137141401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27435432674500044129508277 2572071813234379137141401)
              ·
                refine ⟨1929053859925784352856051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572071813234379137141401 1929053859925784352856051)
                ·
                  refine ⟨2893580789888676529284077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929053859925784352856051 2893580789888676529284077)
                  ·
                    refine ⟨1085092796208253698481529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893580789888676529284077 1085092796208253698481529)
                    ·
                      refine ⟨813819597156190273861147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085092796208253698481529 813819597156190273861147)
                      ·
                        rfl

theorem cell23_1584908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_1584908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584908 prefixEnd_1584908 := by exact prefixLift 1584908
  have htrace : WordTrace (prefixWord ++ tailWord_1584908) baseStart_1584908 baseEnd_1584908 := by
    simpa [prefixWord, tailWord_1584908, baseEnd_1584908] using wordTrace_append hprefix tailTrace_1584908
  have hstable : (prefixWord ++ tailWord_1584908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584908).length < 2 ^ (prefixWord ++ tailWord_1584908).sum := by decide
  have hdescent : baseEnd_1584908 < baseStart_1584908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584924 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1584924 : Nat := 118140960795 + 1584924 * 2 ^ 59
def prefixEnd_1584924 : Nat := 4983230072969 + 3 ^ 40 * 1584924 * 2
def baseEnd_1584924 : Nat := 813827812846662211261073

theorem tailTrace_1584924 : CollatzResearch.WordTrace tailWord_1584924 prefixEnd_1584924 813827812846662211261073 := by
  unfold tailWord_1584924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903463655049253157048913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38537951540065670876065217 28903463655049253157048913)
  ·
    refine ⟨21677597741286939867786685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28903463655049253157048913 21677597741286939867786685)
    ·
      refine ⟨8129099152982602450420007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21677597741286939867786685 8129099152982602450420007)
      ·
        refine ⟨12193648729473903675630011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129099152982602450420007 12193648729473903675630011)
        ·
          refine ⟨18290473094210855513445017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12193648729473903675630011 18290473094210855513445017)
          ·
            refine ⟨13717854820658141635083763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18290473094210855513445017 13717854820658141635083763)
            ·
              refine ⟨20576782230987212452625645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13717854820658141635083763 20576782230987212452625645)
              ·
                refine ⟨7716293336620204669734617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20576782230987212452625645 7716293336620204669734617)
                ·
                  refine ⟨5787220002465153502300963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7716293336620204669734617 5787220002465153502300963)
                  ·
                    refine ⟨8680830003697730253451445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787220002465153502300963 8680830003697730253451445)
                    ·
                      refine ⟨813827812846662211261073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8680830003697730253451445 813827812846662211261073)
                      ·
                        rfl

theorem cell23_1584924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1584924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584924 prefixEnd_1584924 := by exact prefixLift 1584924
  have htrace : WordTrace (prefixWord ++ tailWord_1584924) baseStart_1584924 baseEnd_1584924 := by
    simpa [prefixWord, tailWord_1584924, baseEnd_1584924] using wordTrace_append hprefix tailTrace_1584924
  have hstable : (prefixWord ++ tailWord_1584924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584924).length < 2 ^ (prefixWord ++ tailWord_1584924).sum := by decide
  have hdescent : baseEnd_1584924 < baseStart_1584924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584978 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_1584978 : Nat := 118140960795 + 1584978 * 2 ^ 59
def prefixEnd_1584978 : Nat := 4983230072969 + 3 ^ 40 * 1584978 * 2
def baseEnd_1584978 : Nat := 90428393422444999998425

theorem tailTrace_1584978 : CollatzResearch.WordTrace tailWord_1584978 prefixEnd_1584978 90428393422444999998425 := by
  unfold tailWord_1584978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452224212975718384140897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38539264567935249024375725 14452224212975718384140897)
  ·
    refine ⟨10839168159731788788105673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14452224212975718384140897 10839168159731788788105673)
    ·
      refine ⟨8129376119798841591079255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10839168159731788788105673 8129376119798841591079255)
      ·
        refine ⟨12194064179698262386618883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129376119798841591079255 12194064179698262386618883)
        ·
          refine ⟨18291096269547393579928325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194064179698262386618883 18291096269547393579928325)
          ·
            refine ⟨3429580550540136296236561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18291096269547393579928325 3429580550540136296236561)
            ·
              refine ⟨2572185412905102222177421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429580550540136296236561 2572185412905102222177421)
              ·
                refine ⟨964569529839413333316533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2572185412905102222177421 964569529839413333316533)
                ·
                  refine ⟨90428393422444999998425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 964569529839413333316533 90428393422444999998425)
                  ·
                    rfl

theorem cell23_1584978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_1584978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1584978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1584978 prefixEnd_1584978 := by exact prefixLift 1584978
  have htrace : WordTrace (prefixWord ++ tailWord_1584978) baseStart_1584978 baseEnd_1584978 := by
    simpa [prefixWord, tailWord_1584978, baseEnd_1584978] using wordTrace_append hprefix tailTrace_1584978
  have hstable : (prefixWord ++ tailWord_1584978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584978).length < 2 ^ (prefixWord ++ tailWord_1584978).sum := by decide
  have hdescent : baseEnd_1584978 < baseStart_1584978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585024 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1585024 : Nat := 118140960795 + 1585024 * 2 ^ 59
def prefixEnd_1585024 : Nat := 4983230072969 + 3 ^ 40 * 1585024 * 2
def baseEnd_1585024 : Nat := 813879160912111820010613

theorem tailTrace_1585024 : CollatzResearch.WordTrace tailWord_1585024 prefixEnd_1585024 813879160912111820010613 := by
  unfold tailWord_1585024
  simp only [CollatzResearch.WordTrace]
  refine ⟨28905287304868111696369063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38540383073157482261825417 28905287304868111696369063)
  ·
    refine ⟨43357930957302167544553595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28905287304868111696369063 43357930957302167544553595)
    ·
      refine ⟨65036896435953251316830393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43357930957302167544553595 65036896435953251316830393)
      ·
        refine ⟨48777672326964938487622795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65036896435953251316830393 48777672326964938487622795)
        ·
          refine ⟨73166508490447407731434193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48777672326964938487622795 73166508490447407731434193)
          ·
            refine ⟨54874881367835555798575645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73166508490447407731434193 54874881367835555798575645)
            ·
              refine ⟨20578080512938333424465867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54874881367835555798575645 20578080512938333424465867)
              ·
                refine ⟨30867120769407500136698801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20578080512938333424465867 30867120769407500136698801)
                ·
                  refine ⟨23150340577055625102524101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30867120769407500136698801 23150340577055625102524101)
                  ·
                    refine ⟨4340688858197929706723269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23150340577055625102524101 4340688858197929706723269)
                    ·
                      refine ⟨813879160912111820010613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4340688858197929706723269 813879160912111820010613)
                      ·
                        rfl

theorem cell23_1585024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1585024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585024 prefixEnd_1585024 := by exact prefixLift 1585024
  have htrace : WordTrace (prefixWord ++ tailWord_1585024) baseStart_1585024 baseEnd_1585024 := by
    simpa [prefixWord, tailWord_1585024, baseEnd_1585024] using wordTrace_append hprefix tailTrace_1585024
  have hstable : (prefixWord ++ tailWord_1585024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585024).length < 2 ^ (prefixWord ++ tailWord_1585024).sum := by decide
  have hdescent : baseEnd_1585024 < baseStart_1585024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585055 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 3, 4]
def baseStart_1585055 : Nat := 118140960795 + 1585055 * 2 ^ 59
def prefixEnd_1585055 : Nat := 4983230072969 + 3 ^ 40 * 1585055 * 2
def baseEnd_1585055 : Nat := 271298359604133732907657

theorem tailTrace_1585055 : CollatzResearch.WordTrace tailWord_1585055 prefixEnd_1585055 271298359604133732907657 := by
  unfold tailWord_1585055
  simp only [CollatzResearch.WordTrace]
  refine ⟨57811705272623915687116619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38541136848415943791411079 57811705272623915687116619)
  ·
    refine ⟨86717557908935873530674929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57811705272623915687116619 86717557908935873530674929)
    ·
      refine ⟨65038168431701905148006197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86717557908935873530674929 65038168431701905148006197)
      ·
        refine ⟨6097328290472053607625581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65038168431701905148006197 6097328290472053607625581)
        ·
          refine ⟨2286498108927020102859593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6097328290472053607625581 2286498108927020102859593)
          ·
            refine ⟨1714873581695265077144695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286498108927020102859593 1714873581695265077144695)
            ·
              refine ⟨2572310372542897615717043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714873581695265077144695 2572310372542897615717043)
              ·
                refine ⟨3858465558814346423575565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572310372542897615717043 3858465558814346423575565)
                ·
                  refine ⟨1446924584555379908840837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3858465558814346423575565 1446924584555379908840837)
                  ·
                    refine ⟨271298359604133732907657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446924584555379908840837 271298359604133732907657)
                    ·
                      rfl

theorem cell23_1585055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_1585055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585055 prefixEnd_1585055 := by exact prefixLift 1585055
  have htrace : WordTrace (prefixWord ++ tailWord_1585055) baseStart_1585055 baseEnd_1585055 := by
    simpa [prefixWord, tailWord_1585055, baseEnd_1585055] using wordTrace_append hprefix tailTrace_1585055
  have hstable : (prefixWord ++ tailWord_1585055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585055).length < 2 ^ (prefixWord ++ tailWord_1585055).sum := by decide
  have hdescent : baseEnd_1585055 < baseStart_1585055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585081 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_1585081 : Nat := 118140960795 + 1585081 * 2 ^ 59
def prefixEnd_1585081 : Nat := 4983230072969 + 3 ^ 40 * 1585081 * 2
def baseEnd_1585081 : Nat := 271302809769806032332617

theorem tailTrace_1585081 : CollatzResearch.WordTrace tailWord_1585081 prefixEnd_1585081 271302809769806032332617 := by
  unfold tailWord_1585081
  simp only [CollatzResearch.WordTrace]
  refine ⟨57812653570529722127563097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38541769047019814751708731 57812653570529722127563097)
  ·
    refine ⟨43359490177897291595672323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57812653570529722127563097 43359490177897291595672323)
    ·
      refine ⟨65039235266845937393508485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43359490177897291595672323 65039235266845937393508485)
      ·
        refine ⟨12194856612533613261282841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65039235266845937393508485 12194856612533613261282841)
        ·
          refine ⟨9146142459400209945962131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12194856612533613261282841 9146142459400209945962131)
          ·
            refine ⟨13719213689100314918943197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9146142459400209945962131 13719213689100314918943197)
            ·
              refine ⟨5144705133412618094603699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13719213689100314918943197 5144705133412618094603699)
              ·
                refine ⟨7717057700118927141905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144705133412618094603699 7717057700118927141905549)
                ·
                  refine ⟨2893896637544597678214581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7717057700118927141905549 2893896637544597678214581)
                  ·
                    refine ⟨271302809769806032332617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2893896637544597678214581 271302809769806032332617)
                    ·
                      rfl

theorem cell23_1585081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_1585081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585081 prefixEnd_1585081 := by exact prefixLift 1585081
  have htrace : WordTrace (prefixWord ++ tailWord_1585081) baseStart_1585081 baseEnd_1585081 := by
    simpa [prefixWord, tailWord_1585081, baseEnd_1585081] using wordTrace_append hprefix tailTrace_1585081
  have hstable : (prefixWord ++ tailWord_1585081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585081).length < 2 ^ (prefixWord ++ tailWord_1585081).sum := by decide
  have hdescent : baseEnd_1585081 < baseStart_1585081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585095 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_1585095 : Nat := 118140960795 + 1585095 * 2 ^ 59
def prefixEnd_1585095 : Nat := 4983230072969 + 3 ^ 40 * 1585095 * 2
def baseEnd_1585095 : Nat := 813915618038581042222787

theorem tailTrace_1585095 : CollatzResearch.WordTrace tailWord_1585095 prefixEnd_1585095 813915618038581042222787 := by
  unfold tailWord_1585095
  simp only [CollatzResearch.WordTrace]
  refine ⟨57813164192479002518572739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38542109461652668345715159 57813164192479002518572739)
  ·
    refine ⟨86719746288718503777859109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57813164192479002518572739 86719746288718503777859109)
    ·
      refine ⟨16259952429134719458348583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86719746288718503777859109 16259952429134719458348583)
      ·
        refine ⟨24389928643702079187522875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16259952429134719458348583 24389928643702079187522875)
        ·
          refine ⟨36584892965553118781284313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24389928643702079187522875 36584892965553118781284313)
          ·
            refine ⟨27438669724164839085963235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36584892965553118781284313 27438669724164839085963235)
            ·
              refine ⟨41158004586247258628944853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27438669724164839085963235 41158004586247258628944853)
              ·
                refine ⟨964640732490170124115895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41158004586247258628944853 964640732490170124115895)
                ·
                  refine ⟨1446961098735255186173843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964640732490170124115895 1446961098735255186173843)
                  ·
                    refine ⟨2170441648102882779260765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1446961098735255186173843 2170441648102882779260765)
                    ·
                      refine ⟨813915618038581042222787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170441648102882779260765 813915618038581042222787)
                      ·
                        rfl

theorem cell23_1585095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_1585095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585095 prefixEnd_1585095 := by exact prefixLift 1585095
  have htrace : WordTrace (prefixWord ++ tailWord_1585095) baseStart_1585095 baseEnd_1585095 := by
    simpa [prefixWord, tailWord_1585095, baseEnd_1585095] using wordTrace_append hprefix tailTrace_1585095
  have hstable : (prefixWord ++ tailWord_1585095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585095).length < 2 ^ (prefixWord ++ tailWord_1585095).sum := by decide
  have hdescent : baseEnd_1585095 < baseStart_1585095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585106 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1585106 : Nat := 118140960795 + 1585106 * 2 ^ 59
def prefixEnd_1585106 : Nat := 4983230072969 + 3 ^ 40 * 1585106 * 2
def baseEnd_1585106 : Nat := 271307088775260166395079

theorem tailTrace_1585106 : CollatzResearch.WordTrace tailWord_1585106 prefixEnd_1585106 271307088775260166395079 := by
  unfold tailWord_1585106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453391348859787849305793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38542376930292767598148781 14453391348859787849305793)
  ·
    refine ⟨10840043511644840886979345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14453391348859787849305793 10840043511644840886979345)
    ·
      refine ⟨8130032633733630665234509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10840043511644840886979345 8130032633733630665234509)
      ·
        refine ⟨3048762237650111499462941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8130032633733630665234509 3048762237650111499462941)
        ·
          refine ⟨1143285839118791812298603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3048762237650111499462941 1143285839118791812298603)
          ·
            refine ⟨1714928758678187718447905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143285839118791812298603 1714928758678187718447905)
            ·
              refine ⟨1286196569008640788835929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714928758678187718447905 1286196569008640788835929)
              ·
                refine ⟨964647426756480591626947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286196569008640788835929 964647426756480591626947)
                ·
                  refine ⟨1446971140134720887440421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964647426756480591626947 1446971140134720887440421)
                  ·
                    refine ⟨271307088775260166395079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446971140134720887440421 271307088775260166395079)
                    ·
                      rfl

theorem cell23_1585106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1585106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585106 prefixEnd_1585106 := by exact prefixLift 1585106
  have htrace : WordTrace (prefixWord ++ tailWord_1585106) baseStart_1585106 baseEnd_1585106 := by
    simpa [prefixWord, tailWord_1585106, baseEnd_1585106] using wordTrace_append hprefix tailTrace_1585106
  have hstable : (prefixWord ++ tailWord_1585106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585106).length < 2 ^ (prefixWord ++ tailWord_1585106).sum := by decide
  have hdescent : baseEnd_1585106 < baseStart_1585106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585121 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1585121 : Nat := 118140960795 + 1585121 * 2 ^ 59
def prefixEnd_1585121 : Nat := 4983230072969 + 3 ^ 40 * 1585121 * 2
def baseEnd_1585121 : Nat := 813928968535597940497667

theorem tailTrace_1585121 : CollatzResearch.WordTrace tailWord_1585121 prefixEnd_1585121 813928968535597940497667 := by
  unfold tailWord_1585121
  simp only [CollatzResearch.WordTrace]
  refine ⟨57814112490384808959019217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38542741660256539306012811 57814112490384808959019217)
  ·
    refine ⟨43360584367788606719264413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57814112490384808959019217 43360584367788606719264413)
    ·
      refine ⟨16260219137920727519724155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43360584367788606719264413 16260219137920727519724155)
      ·
        refine ⟨24390328706881091279586233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260219137920727519724155 24390328706881091279586233)
        ·
          refine ⟨18292746530160818459689675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24390328706881091279586233 18292746530160818459689675)
          ·
            refine ⟨27439119795241227689534513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18292746530160818459689675 27439119795241227689534513)
            ·
              refine ⟨20579339846430920767150885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27439119795241227689534513 20579339846430920767150885)
              ·
                refine ⟨3858626221205797643840791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20579339846430920767150885 3858626221205797643840791)
                ·
                  refine ⟨5787939331808696465761187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858626221205797643840791 5787939331808696465761187)
                  ·
                    refine ⟨8681908997713044698641781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787939331808696465761187 8681908997713044698641781)
                    ·
                      refine ⟨813928968535597940497667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8681908997713044698641781 813928968535597940497667)
                      ·
                        rfl

theorem cell23_1585121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1585121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585121 prefixEnd_1585121 := by exact prefixLift 1585121
  have htrace : WordTrace (prefixWord ++ tailWord_1585121) baseStart_1585121 baseEnd_1585121 := by
    simpa [prefixWord, tailWord_1585121, baseEnd_1585121] using wordTrace_append hprefix tailTrace_1585121
  have hstable : (prefixWord ++ tailWord_1585121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585121).length < 2 ^ (prefixWord ++ tailWord_1585121).sum := by decide
  have hdescent : baseEnd_1585121 < baseStart_1585121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585135 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 3, 2, 2]
def baseStart_1585135 : Nat := 118140960795 + 1585135 * 2 ^ 59
def prefixEnd_1585135 : Nat := 4983230072969 + 3 ^ 40 * 1585135 * 2
def baseEnd_1585135 : Nat := 813936157264760885722603

theorem tailTrace_1585135 : CollatzResearch.WordTrace tailWord_1585135 prefixEnd_1585135 813936157264760885722603 := by
  unfold tailWord_1585135
  simp only [CollatzResearch.WordTrace]
  refine ⟨57814623112334089350028859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38543082074889392900019239 57814623112334089350028859)
  ·
    refine ⟨86721934668501134025043289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57814623112334089350028859 86721934668501134025043289)
    ·
      refine ⟨65041451001375850518782467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86721934668501134025043289 65041451001375850518782467)
      ·
        refine ⟨97562176502063775778173701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65041451001375850518782467 97562176502063775778173701)
        ·
          refine ⟨18292908094136957958407569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97562176502063775778173701 18292908094136957958407569)
          ·
            refine ⟨13719681070602718468805677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18292908094136957958407569 13719681070602718468805677)
            ·
              refine ⟨5144880401476019425802129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13719681070602718468805677 5144880401476019425802129)
              ·
                refine ⟨3858660301107014569351597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5144880401476019425802129 3858660301107014569351597)
                ·
                  refine ⟨1446997612915130463506849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3858660301107014569351597 1446997612915130463506849)
                  ·
                    refine ⟨1085248209686347847630137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446997612915130463506849 1085248209686347847630137)
                    ·
                      refine ⟨813936157264760885722603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085248209686347847630137 813936157264760885722603)
                      ·
                        rfl

theorem cell23_1585135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2, 2].length) (baseStart_1585135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585135 prefixEnd_1585135 := by exact prefixLift 1585135
  have htrace : WordTrace (prefixWord ++ tailWord_1585135) baseStart_1585135 baseEnd_1585135 := by
    simpa [prefixWord, tailWord_1585135, baseEnd_1585135] using wordTrace_append hprefix tailTrace_1585135
  have hstable : (prefixWord ++ tailWord_1585135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585135).length < 2 ^ (prefixWord ++ tailWord_1585135).sum := by decide
  have hdescent : baseEnd_1585135 < baseStart_1585135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585162 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1585162 : Nat := 118140960795 + 1585162 * 2 ^ 59
def prefixEnd_1585162 : Nat := 4983230072969 + 3 ^ 40 * 1585162 * 2
def baseEnd_1585162 : Nat := 271316673747477426694993

theorem tailTrace_1585162 : CollatzResearch.WordTrace tailWord_1585162 prefixEnd_1585162 271316673747477426694993 := by
  unfold tailWord_1585162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453901970809068240315435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38543738588824181974174493 14453901970809068240315435)
  ·
    refine ⟨21680852956213602360473153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14453901970809068240315435 21680852956213602360473153)
    ·
      refine ⟨16260639717160201770354865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21680852956213602360473153 16260639717160201770354865)
      ·
        refine ⟨12195479787870151327766149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16260639717160201770354865 12195479787870151327766149)
        ·
          refine ⟨2286652460225653373956153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12195479787870151327766149 2286652460225653373956153)
          ·
            refine ⟨1714989345169240030467115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286652460225653373956153 1714989345169240030467115)
            ·
              refine ⟨2572484017753860045700673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714989345169240030467115 2572484017753860045700673)
              ·
                refine ⟨1929363013315395034275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572484017753860045700673 1929363013315395034275505)
                ·
                  refine ⟨1447022259986546275706629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929363013315395034275505 1447022259986546275706629)
                  ·
                    refine ⟨271316673747477426694993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447022259986546275706629 271316673747477426694993)
                    ·
                      rfl

theorem cell23_1585162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1585162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585162 prefixEnd_1585162 := by exact prefixLift 1585162
  have htrace : WordTrace (prefixWord ++ tailWord_1585162) baseStart_1585162 baseEnd_1585162 := by
    simpa [prefixWord, tailWord_1585162, baseEnd_1585162] using wordTrace_append hprefix tailTrace_1585162
  have hstable : (prefixWord ++ tailWord_1585162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585162).length < 2 ^ (prefixWord ++ tailWord_1585162).sum := by decide
  have hdescent : baseEnd_1585162 < baseStart_1585162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_1585168 : Nat := 118140960795 + 1585168 * 2 ^ 59
def prefixEnd_1585168 : Nat := 4983230072969 + 3 ^ 40 * 1585168 * 2
def baseEnd_1585168 : Nat := 813953102126359256609951

theorem tailTrace_1585168 : CollatzResearch.WordTrace tailWord_1585168 prefixEnd_1585168 813953102126359256609951 := by
  unfold tailWord_1585168
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907913360607267992990079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38543884480809690657320105 28907913360607267992990079)
  ·
    refine ⟨43361870040910901989485119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28907913360607267992990079 43361870040910901989485119)
    ·
      refine ⟨65042805061366352984227679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43361870040910901989485119 65042805061366352984227679)
      ·
        refine ⟨97564207592049529476341519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65042805061366352984227679 97564207592049529476341519)
        ·
          refine ⟨146346311388074294214512279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97564207592049529476341519 146346311388074294214512279)
          ·
            refine ⟨219519467082111441321768419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146346311388074294214512279 219519467082111441321768419)
            ·
              refine ⟨329279200623167161982652629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219519467082111441321768419 329279200623167161982652629)
              ·
                refine ⟨7717481264605480358968421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329279200623167161982652629 7717481264605480358968421)
                ·
                  refine ⟨1447027737113527567306579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7717481264605480358968421 1447027737113527567306579)
                  ·
                    refine ⟨2170541605670291350959869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447027737113527567306579 2170541605670291350959869)
                    ·
                      refine ⟨813953102126359256609951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170541605670291350959869 813953102126359256609951)
                      ·
                        rfl

theorem cell23_1585168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_1585168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585168 prefixEnd_1585168 := by exact prefixLift 1585168
  have htrace : WordTrace (prefixWord ++ tailWord_1585168) baseStart_1585168 baseEnd_1585168 := by
    simpa [prefixWord, tailWord_1585168, baseEnd_1585168] using wordTrace_append hprefix tailTrace_1585168
  have hstable : (prefixWord ++ tailWord_1585168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585168).length < 2 ^ (prefixWord ++ tailWord_1585168).sum := by decide
  have hdescent : baseEnd_1585168 < baseStart_1585168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585172 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1585172 : Nat := 118140960795 + 1585172 * 2 ^ 59
def prefixEnd_1585172 : Nat := 4983230072969 + 3 ^ 40 * 1585172 * 2
def baseEnd_1585172 : Nat := 813955156048977240959933

theorem tailTrace_1585172 : CollatzResearch.WordTrace tailWord_1585172 prefixEnd_1585172 813955156048977240959933 := by
  unfold tailWord_1585172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907986306600022334562885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38543981742133363112750513 28907986306600022334562885)
  ·
    refine ⟨5420247432487504187730541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28907986306600022334562885 5420247432487504187730541)
    ·
      refine ⟨2032592787182814070398953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5420247432487504187730541 2032592787182814070398953)
      ·
        refine ⟨1524444590387110552799215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032592787182814070398953 1524444590387110552799215)
        ·
          refine ⟨2286666885580665829198823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524444590387110552799215 2286666885580665829198823)
          ·
            refine ⟨3430000328370998743798235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286666885580665829198823 3430000328370998743798235)
            ·
              refine ⟨5145000492556498115697353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430000328370998743798235 5145000492556498115697353)
              ·
                refine ⟨3858750369417373586773015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145000492556498115697353 3858750369417373586773015)
                ·
                  refine ⟨5788125554126060380159523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858750369417373586773015 5788125554126060380159523)
                  ·
                    refine ⟨8682188331189090570239285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788125554126060380159523 8682188331189090570239285)
                    ·
                      refine ⟨813955156048977240959933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8682188331189090570239285 813955156048977240959933)
                      ·
                        rfl

theorem cell23_1585172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1585172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585172 prefixEnd_1585172 := by exact prefixLift 1585172
  have htrace : WordTrace (prefixWord ++ tailWord_1585172) baseStart_1585172 baseEnd_1585172 := by
    simpa [prefixWord, tailWord_1585172, baseEnd_1585172] using wordTrace_append hprefix tailTrace_1585172
  have hstable : (prefixWord ++ tailWord_1585172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585172).length < 2 ^ (prefixWord ++ tailWord_1585172).sum := by decide
  have hdescent : baseEnd_1585172 < baseStart_1585172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585192 : List Nat := [2, 1, 5, 3, 1, 2, 2, 7]
def baseStart_1585192 : Nat := 118140960795 + 1585192 * 2 ^ 59
def prefixEnd_1585192 : Nat := 4983230072969 + 3 ^ 40 * 1585192 * 2
def baseEnd_1585192 : Nat := 30146867617113598618883

theorem tailTrace_1585192 : CollatzResearch.WordTrace tailWord_1585192 prefixEnd_1585192 30146867617113598618883 := by
  unfold tailWord_1585192
  simp only [CollatzResearch.WordTrace]
  refine ⟨28908351036563794042426915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38544468048751725389902553 28908351036563794042426915)
  ·
    refine ⟨43362526554845691063640373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28908351036563794042426915 43362526554845691063640373)
    ·
      refine ⟨4065236864516783537216285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43362526554845691063640373 4065236864516783537216285)
      ·
        refine ⟨1524463824193793826456107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4065236864516783537216285 1524463824193793826456107)
        ·
          refine ⟨2286695736290690739684161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524463824193793826456107 2286695736290690739684161)
          ·
            refine ⟨1715021802218018054763121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286695736290690739684161 1715021802218018054763121)
            ·
              refine ⟨1286266351663513541072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715021802218018054763121 1286266351663513541072341)
              ·
                refine ⟨30146867617113598618883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1286266351663513541072341 30146867617113598618883)
                ·
                  rfl

theorem cell23_1585192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 7].length) (baseStart_1585192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585192 prefixEnd_1585192 := by exact prefixLift 1585192
  have htrace : WordTrace (prefixWord ++ tailWord_1585192) baseStart_1585192 baseEnd_1585192 := by
    simpa [prefixWord, tailWord_1585192, baseEnd_1585192] using wordTrace_append hprefix tailTrace_1585192
  have hstable : (prefixWord ++ tailWord_1585192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585192).length < 2 ^ (prefixWord ++ tailWord_1585192).sum := by decide
  have hdescent : baseEnd_1585192 < baseStart_1585192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585198 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1585198 : Nat := 118140960795 + 1585198 * 2 ^ 59
def prefixEnd_1585198 : Nat := 4983230072969 + 3 ^ 40 * 1585198 * 2
def baseEnd_1585198 : Nat := 813968506545994139234813

theorem tailTrace_1585198 : CollatzResearch.WordTrace tailWord_1585198 prefixEnd_1585198 813968506545994139234813 := by
  unfold tailWord_1585198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227115113888231388696531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38544613940737234073048165 7227115113888231388696531)
  ·
    refine ⟨10840672670832347083044797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7227115113888231388696531 10840672670832347083044797)
    ·
      refine ⟨4065252251562130156141799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10840672670832347083044797 4065252251562130156141799)
      ·
        refine ⟨6097878377343195234212699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065252251562130156141799 6097878377343195234212699)
        ·
          refine ⟨9146817566014792851319049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097878377343195234212699 9146817566014792851319049)
          ·
            refine ⟨6860113174511094638489287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146817566014792851319049 6860113174511094638489287)
            ·
              refine ⟨10290169761766641957733931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860113174511094638489287 10290169761766641957733931)
              ·
                refine ⟨15435254642649962936600897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10290169761766641957733931 15435254642649962936600897)
                ·
                  refine ⟨11576440981987472202450673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15435254642649962936600897 11576440981987472202450673)
                  ·
                    refine ⟨8682330736490604151838005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11576440981987472202450673 8682330736490604151838005)
                    ·
                      refine ⟨813968506545994139234813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8682330736490604151838005 813968506545994139234813)
                      ·
                        rfl

theorem cell23_1585198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1585198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585198 prefixEnd_1585198 := by exact prefixLift 1585198
  have htrace : WordTrace (prefixWord ++ tailWord_1585198) baseStart_1585198 baseEnd_1585198 := by
    simpa [prefixWord, tailWord_1585198, baseEnd_1585198] using wordTrace_append hprefix tailTrace_1585198
  have hstable : (prefixWord ++ tailWord_1585198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585198).length < 2 ^ (prefixWord ++ tailWord_1585198).sum := by decide
  have hdescent : baseEnd_1585198 < baseStart_1585198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585211 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_1585211 : Nat := 118140960795 + 1585211 * 2 ^ 59
def prefixEnd_1585211 : Nat := 4983230072969 + 3 ^ 40 * 1585211 * 2
def baseEnd_1585211 : Nat := 813975181794502588372253

theorem tailTrace_1585211 : CollatzResearch.WordTrace tailWord_1585211 prefixEnd_1585211 813975181794502588372253 := by
  unfold tailWord_1585211
  simp only [CollatzResearch.WordTrace]
  refine ⟨57817395060058754329795487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38544930040039169553196991 57817395060058754329795487)
  ·
    refine ⟨86726092590088131494693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57817395060058754329795487 86726092590088131494693231)
    ·
      refine ⟨130089138885132197242039847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86726092590088131494693231 130089138885132197242039847)
      ·
        refine ⟨195133708327698295863059771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130089138885132197242039847 195133708327698295863059771)
        ·
          refine ⟨292700562491547443794589657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195133708327698295863059771 292700562491547443794589657)
          ·
            refine ⟨219525421868660582845942243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292700562491547443794589657 219525421868660582845942243)
            ·
              refine ⟨329288132802990874268913365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219525421868660582845942243 329288132802990874268913365)
              ·
                refine ⟨7717690612570098615677657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329288132802990874268913365 7717690612570098615677657)
                ·
                  refine ⟨5788267959427573961758243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717690612570098615677657 5788267959427573961758243)
                  ·
                    refine ⟨8682401939141360942637365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788267959427573961758243 8682401939141360942637365)
                    ·
                      refine ⟨813975181794502588372253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8682401939141360942637365 813975181794502588372253)
                      ·
                        rfl

theorem cell23_1585211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_1585211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585211 prefixEnd_1585211 := by exact prefixLift 1585211
  have htrace : WordTrace (prefixWord ++ tailWord_1585211) baseStart_1585211 baseEnd_1585211 := by
    simpa [prefixWord, tailWord_1585211, baseEnd_1585211] using wordTrace_append hprefix tailTrace_1585211
  have hstable : (prefixWord ++ tailWord_1585211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585211).length < 2 ^ (prefixWord ++ tailWord_1585211).sum := by decide
  have hdescent : baseEnd_1585211 < baseStart_1585211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585225 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 4, 2, 2]
def baseStart_1585225 : Nat := 118140960795 + 1585225 * 2 ^ 59
def prefixEnd_1585225 : Nat := 4983230072969 + 3 ^ 40 * 1585225 * 2
def baseEnd_1585225 : Nat := 813982370523665533597189

theorem tailTrace_1585225 : CollatzResearch.WordTrace tailWord_1585225 prefixEnd_1585225 813982370523665533597189 := by
  unfold tailWord_1585225
  simp only [CollatzResearch.WordTrace]
  refine ⟨57817905682008034720805129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38545270454672023147203419 57817905682008034720805129)
  ·
    refine ⟨43363429261506026040603847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57817905682008034720805129 43363429261506026040603847)
    ·
      refine ⟨65045143892259039060905771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43363429261506026040603847 65045143892259039060905771)
      ·
        refine ⟨97567715838388558591358657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65045143892259039060905771 97567715838388558591358657)
        ·
          refine ⟨73175786878791418943518993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97567715838388558591358657 73175786878791418943518993)
          ·
            refine ⟨54881840159093564207639245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73175786878791418943518993 54881840159093564207639245)
            ·
              refine ⟨20580690059660086577864717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54881840159093564207639245 20580690059660086577864717)
              ·
                refine ⟨7717758772372532466699269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20580690059660086577864717 7717758772372532466699269)
                ·
                  refine ⟨1447079769819849837506113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7717758772372532466699269 1447079769819849837506113)
                  ·
                    refine ⟨1085309827364887378129585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447079769819849837506113 1085309827364887378129585)
                    ·
                      refine ⟨813982370523665533597189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085309827364887378129585 813982370523665533597189)
                      ·
                        rfl

theorem cell23_1585225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2, 2].length) (baseStart_1585225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585225 prefixEnd_1585225 := by exact prefixLift 1585225
  have htrace : WordTrace (prefixWord ++ tailWord_1585225) baseStart_1585225 baseEnd_1585225 := by
    simpa [prefixWord, tailWord_1585225, baseEnd_1585225] using wordTrace_append hprefix tailTrace_1585225
  have hstable : (prefixWord ++ tailWord_1585225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585225).length < 2 ^ (prefixWord ++ tailWord_1585225).sum := by decide
  have hdescent : baseEnd_1585225 < baseStart_1585225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585242 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_1585242 : Nat := 118140960795 + 1585242 * 2 ^ 59
def prefixEnd_1585242 : Nat := 4983230072969 + 3 ^ 40 * 1585242 * 2
def baseEnd_1585242 : Nat := 813991099694791967084611

theorem tailTrace_1585242 : CollatzResearch.WordTrace tailWord_1585242 prefixEnd_1585242 813991099694791967084611 := by
  unfold tailWord_1585242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454631430736611656043495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38545683815297631082782653 14454631430736611656043495)
  ·
    refine ⟨21681947146104917484065243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14454631430736611656043495 21681947146104917484065243)
    ·
      refine ⟨32522920719157376226097865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21681947146104917484065243 32522920719157376226097865)
      ·
        refine ⟨24392190539368032169573399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32522920719157376226097865 24392190539368032169573399)
        ·
          refine ⟨36588285809052048254360099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24392190539368032169573399 36588285809052048254360099)
          ·
            refine ⟨54882428713578072381540149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36588285809052048254360099 54882428713578072381540149)
            ·
              refine ⟨5145227691897944285769389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54882428713578072381540149 5145227691897944285769389)
              ·
                refine ⟨1929460384461729107163521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145227691897944285769389 1929460384461729107163521)
                ·
                  refine ⟨1447095288346296830372641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929460384461729107163521 1447095288346296830372641)
                  ·
                    refine ⟨1085321466259722622779481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447095288346296830372641 1085321466259722622779481)
                    ·
                      refine ⟨813991099694791967084611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085321466259722622779481 813991099694791967084611)
                      ·
                        rfl

theorem cell23_1585242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_1585242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585242 prefixEnd_1585242 := by exact prefixLift 1585242
  have htrace : WordTrace (prefixWord ++ tailWord_1585242) baseStart_1585242 baseEnd_1585242 := by
    simpa [prefixWord, tailWord_1585242, baseEnd_1585242] using wordTrace_append hprefix tailTrace_1585242
  have hstable : (prefixWord ++ tailWord_1585242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585242).length < 2 ^ (prefixWord ++ tailWord_1585242).sum := by decide
  have hdescent : baseEnd_1585242 < baseStart_1585242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585245 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1585245 : Nat := 118140960795 + 1585245 * 2 ^ 59
def prefixEnd_1585245 : Nat := 4983230072969 + 3 ^ 40 * 1585245 * 2
def baseEnd_1585245 : Nat := 813992640136755455347097

theorem tailTrace_1585245 : CollatzResearch.WordTrace tailWord_1585245 prefixEnd_1585245 813992640136755455347097 := by
  unfold tailWord_1585245
  simp only [CollatzResearch.WordTrace]
  refine ⟨57818635141935578136533189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38545756761290385424355459 57818635141935578136533189)
  ·
    refine ⟨10840994089112920900599973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57818635141935578136533189 10840994089112920900599973)
    ·
      refine ⟨2032686391708672668862495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10840994089112920900599973 2032686391708672668862495)
      ·
        refine ⟨3049029587563009003293743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032686391708672668862495 3049029587563009003293743)
        ·
          refine ⟨4573544381344513504940615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049029587563009003293743 4573544381344513504940615)
          ·
            refine ⟨6860316572016770257410923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573544381344513504940615 6860316572016770257410923)
            ·
              refine ⟨10290474858025155386116385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860316572016770257410923 10290474858025155386116385)
              ·
                refine ⟨7717856143518866539587289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10290474858025155386116385 7717856143518866539587289)
                ·
                  refine ⟨5788392107639149904690467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717856143518866539587289 5788392107639149904690467)
                  ·
                    refine ⟨8682588161458724857035701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788392107639149904690467 8682588161458724857035701)
                    ·
                      refine ⟨813992640136755455347097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8682588161458724857035701 813992640136755455347097)
                      ·
                        rfl

theorem cell23_1585245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1585245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585245 prefixEnd_1585245 := by exact prefixLift 1585245
  have htrace : WordTrace (prefixWord ++ tailWord_1585245) baseStart_1585245 baseEnd_1585245 := by
    simpa [prefixWord, tailWord_1585245, baseEnd_1585245] using wordTrace_append hprefix tailTrace_1585245
  have hstable : (prefixWord ++ tailWord_1585245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585245).length < 2 ^ (prefixWord ++ tailWord_1585245).sum := by decide
  have hdescent : baseEnd_1585245 < baseStart_1585245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585246 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1585246 : Nat := 118140960795 + 1585246 * 2 ^ 59
def prefixEnd_1585246 : Nat := 4983230072969 + 3 ^ 40 * 1585246 * 2
def baseEnd_1585246 : Nat := 813993153617409951434593

theorem tailTrace_1585246 : CollatzResearch.WordTrace tailWord_1585246 prefixEnd_1585246 813993153617409951434593 := by
  unfold tailWord_1585246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227333951866494413414949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38545781076621303538213061 7227333951866494413414949)
  ·
    refine ⟨1355125115974967702515303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7227333951866494413414949 1355125115974967702515303)
    ·
      refine ⟨2032687673962451553772955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355125115974967702515303 2032687673962451553772955)
      ·
        refine ⟨3049031510943677330659433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032687673962451553772955 3049031510943677330659433)
        ·
          refine ⟨2286773633207757997994575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049031510943677330659433 2286773633207757997994575)
          ·
            refine ⟨3430160449811636996991863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286773633207757997994575 3430160449811636996991863)
            ·
              refine ⟨5145240674717455495487795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430160449811636996991863 5145240674717455495487795)
              ·
                refine ⟨7717861012076183243231693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145240674717455495487795 7717861012076183243231693)
                ·
                  refine ⟨2894197879528568716211885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7717861012076183243231693 2894197879528568716211885)
                  ·
                    refine ⟨1085324204823213268579457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2894197879528568716211885 1085324204823213268579457)
                    ·
                      refine ⟨813993153617409951434593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085324204823213268579457 813993153617409951434593)
                      ·
                        rfl

theorem cell23_1585246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1585246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585246 prefixEnd_1585246 := by exact prefixLift 1585246
  have htrace : WordTrace (prefixWord ++ tailWord_1585246) baseStart_1585246 baseEnd_1585246 := by
    simpa [prefixWord, tailWord_1585246, baseEnd_1585246] using wordTrace_append hprefix tailTrace_1585246
  have hstable : (prefixWord ++ tailWord_1585246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585246).length < 2 ^ (prefixWord ++ tailWord_1585246).sum := by decide
  have hdescent : baseEnd_1585246 < baseStart_1585246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585285 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_1585285 : Nat := 118140960795 + 1585285 * 2 ^ 59
def prefixEnd_1585285 : Nat := 4983230072969 + 3 ^ 40 * 1585285 * 2
def baseEnd_1585285 : Nat := 814013179362935298846913

theorem tailTrace_1585285 : CollatzResearch.WordTrace tailWord_1585285 prefixEnd_1585285 814013179362935298846913 := by
  unfold tailWord_1585285
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820094061790664967989309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38546729374527109978659539 57820094061790664967989309)
  ·
    refine ⟨21682535273171499362995991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57820094061790664967989309 21682535273171499362995991)
    ·
      refine ⟨32523802909757249044493987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21682535273171499362995991 32523802909757249044493987)
      ·
        refine ⟨48785704364635873566740981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32523802909757249044493987 48785704364635873566740981)
        ·
          refine ⟨4573659784184613146881967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48785704364635873566740981 4573659784184613146881967)
          ·
            refine ⟨6860489676276919720322951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573659784184613146881967 6860489676276919720322951)
            ·
              refine ⟨10290734514415379580484427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860489676276919720322951 10290734514415379580484427)
              ·
                refine ⟨15436101771623069370726641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10290734514415379580484427 15436101771623069370726641)
                ·
                  refine ⟨11577076328717302028044981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15436101771623069370726641 11577076328717302028044981)
                  ·
                    refine ⟨1085350905817247065129217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11577076328717302028044981 1085350905817247065129217)
                    ·
                      refine ⟨814013179362935298846913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085350905817247065129217 814013179362935298846913)
                      ·
                        rfl

theorem cell23_1585285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_1585285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585285 prefixEnd_1585285 := by exact prefixLift 1585285
  have htrace : WordTrace (prefixWord ++ tailWord_1585285) baseStart_1585285 baseEnd_1585285 := by
    simpa [prefixWord, tailWord_1585285, baseEnd_1585285] using wordTrace_append hprefix tailTrace_1585285
  have hstable : (prefixWord ++ tailWord_1585285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585285).length < 2 ^ (prefixWord ++ tailWord_1585285).sum := by decide
  have hdescent : baseEnd_1585285 < baseStart_1585285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585291 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 8]
def baseStart_1585291 : Nat := 118140960795 + 1585291 * 2 ^ 59
def prefixEnd_1585291 : Nat := 4983230072969 + 3 ^ 40 * 1585291 * 2
def baseEnd_1585291 : Nat := 271338753415620758457295

theorem tailTrace_1585291 : CollatzResearch.WordTrace tailWord_1585291 prefixEnd_1585291 271338753415620758457295 := by
  unfold tailWord_1585291
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820312899768927992707727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38546875266512618661805151 57820312899768927992707727)
  ·
    refine ⟨86730469349653391989061591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57820312899768927992707727 86730469349653391989061591)
    ·
      refine ⟨130095704024480087983592387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86730469349653391989061591 130095704024480087983592387)
      ·
        refine ⟨195143556036720131975388581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130095704024480087983592387 195143556036720131975388581)
        ·
          refine ⟨36589416756885024745385359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195143556036720131975388581 36589416756885024745385359)
          ·
            refine ⟨54884125135327537118078039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36589416756885024745385359 54884125135327537118078039)
            ·
              refine ⟨82326187702991305677117059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54884125135327537118078039 82326187702991305677117059)
              ·
                refine ⟨123489281554486958515675589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82326187702991305677117059 123489281554486958515675589)
                ·
                  refine ⟨23154240291466304721689173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123489281554486958515675589 23154240291466304721689173)
                  ·
                    refine ⟨271338753415620758457295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23154240291466304721689173 271338753415620758457295)
                    ·
                      rfl

theorem cell23_1585291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_1585291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585291 prefixEnd_1585291 := by exact prefixLift 1585291
  have htrace : WordTrace (prefixWord ++ tailWord_1585291) baseStart_1585291 baseEnd_1585291 := by
    simpa [prefixWord, tailWord_1585291, baseEnd_1585291] using wordTrace_append hprefix tailTrace_1585291
  have hstable : (prefixWord ++ tailWord_1585291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585291).length < 2 ^ (prefixWord ++ tailWord_1585291).sum := by decide
  have hdescent : baseEnd_1585291 < baseStart_1585291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585355 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 6]
def baseStart_1585355 : Nat := 118140960795 + 1585355 * 2 ^ 59
def prefixEnd_1585355 : Nat := 4983230072969 + 3 ^ 40 * 1585355 * 2
def baseEnd_1585355 : Nat := 90449902556527780552399

theorem tailTrace_1585355 : CollatzResearch.WordTrace tailWord_1585355 prefixEnd_1585355 90449902556527780552399 := by
  unfold tailWord_1585355
  simp only [CollatzResearch.WordTrace]
  refine ⟨57822647171537066923037519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38548431447691377948691679 57822647171537066923037519)
  ·
    refine ⟨86733970757305600384556279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57822647171537066923037519 86733970757305600384556279)
    ·
      refine ⟨130100956135958400576834419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86733970757305600384556279 130100956135958400576834419)
      ·
        refine ⟨195151434203937600865251629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130100956135958400576834419 195151434203937600865251629)
        ·
          refine ⟨73181787826476600324469361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195151434203937600865251629 73181787826476600324469361)
          ·
            refine ⟨54886340869857450243352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73181787826476600324469361 54886340869857450243352021)
            ·
              refine ⟨1286398614137283990078563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54886340869857450243352021 1286398614137283990078563)
              ·
                refine ⟨1929597921205925985117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286398614137283990078563 1929597921205925985117845)
                ·
                  refine ⟨90449902556527780552399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1929597921205925985117845 90449902556527780552399)
                  ·
                    rfl

theorem cell23_1585355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 6].length) (baseStart_1585355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585355 prefixEnd_1585355 := by exact prefixLift 1585355
  have htrace : WordTrace (prefixWord ++ tailWord_1585355) baseStart_1585355 baseEnd_1585355 := by
    simpa [prefixWord, tailWord_1585355, baseEnd_1585355] using wordTrace_append hprefix tailTrace_1585355
  have hstable : (prefixWord ++ tailWord_1585355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585355).length < 2 ^ (prefixWord ++ tailWord_1585355).sum := by decide
  have hdescent : baseEnd_1585355 < baseStart_1585355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585439 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 1, 1, 4]
def baseStart_1585439 : Nat := 118140960795 + 1585439 * 2 ^ 59
def prefixEnd_1585439 : Nat := 4983230072969 + 3 ^ 40 * 1585439 * 2
def baseEnd_1585439 : Nat := 814092255383727696321205

theorem tailTrace_1585439 : CollatzResearch.WordTrace tailWord_1585439 prefixEnd_1585439 814092255383727696321205 := by
  unfold tailWord_1585439
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825710903232749269095371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550473935488499512730247 57825710903232749269095371)
  ·
    refine ⟨86738566354849123903643057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825710903232749269095371 86738566354849123903643057)
    ·
      refine ⟨65053924766136842927732293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86738566354849123903643057 65053924766136842927732293)
      ·
        refine ⟨12197610893650658048949805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65053924766136842927732293 12197610893650658048949805)
        ·
          refine ⟨4574104085118996768356177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12197610893650658048949805 4574104085118996768356177)
          ·
            refine ⟨3430578063839247576267133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4574104085118996768356177 3430578063839247576267133)
            ·
              refine ⟨1286466773939717841100175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3430578063839247576267133 1286466773939717841100175)
              ·
                refine ⟨1929700160909576761650263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286466773939717841100175 1929700160909576761650263)
                ·
                  refine ⟨2894550241364365142475395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929700160909576761650263 2894550241364365142475395)
                  ·
                    refine ⟨4341825362046547713713093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2894550241364365142475395 4341825362046547713713093)
                    ·
                      refine ⟨814092255383727696321205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4341825362046547713713093 814092255383727696321205)
                      ·
                        rfl

theorem cell23_1585439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_1585439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585439 prefixEnd_1585439 := by exact prefixLift 1585439
  have htrace : WordTrace (prefixWord ++ tailWord_1585439) baseStart_1585439 baseEnd_1585439 := by
    simpa [prefixWord, tailWord_1585439, baseEnd_1585439] using wordTrace_append hprefix tailTrace_1585439
  have hstable : (prefixWord ++ tailWord_1585439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585439).length < 2 ^ (prefixWord ++ tailWord_1585439).sum := by decide
  have hdescent : baseEnd_1585439 < baseStart_1585439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585442 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1585442 : Nat := 118140960795 + 1585442 * 2 ^ 59
def prefixEnd_1585442 : Nat := 4983230072969 + 3 ^ 40 * 1585442 * 2
def baseEnd_1585442 : Nat := 814093795825691184583691

theorem tailTrace_1585442 : CollatzResearch.WordTrace tailWord_1585442 prefixEnd_1585442 814093795825691184583691 := by
  unfold tailWord_1585442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456455080555470195363645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38550546881481253854303053 14456455080555470195363645)
  ·
    refine ⟨5421170655208301323261367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14456455080555470195363645 5421170655208301323261367)
    ·
      refine ⟨8131755982812451984892051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5421170655208301323261367 8131755982812451984892051)
      ·
        refine ⟨12197633974218677977338077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131755982812451984892051 12197633974218677977338077)
        ·
          refine ⟨4574112740332004241501779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12197633974218677977338077 4574112740332004241501779)
          ·
            refine ⟨6861169110498006362252669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574112740332004241501779 6861169110498006362252669)
            ·
              refine ⟨2572938416436752385844751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6861169110498006362252669 2572938416436752385844751)
              ·
                refine ⟨3859407624655128578767127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572938416436752385844751 3859407624655128578767127)
                ·
                  refine ⟨5789111436982692868150691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859407624655128578767127 5789111436982692868150691)
                  ·
                    refine ⟨8683667155474039302226037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789111436982692868150691 8683667155474039302226037)
                    ·
                      refine ⟨814093795825691184583691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8683667155474039302226037 814093795825691184583691)
                      ·
                        rfl

theorem cell23_1585442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1585442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585442 prefixEnd_1585442 := by exact prefixLift 1585442
  have htrace : WordTrace (prefixWord ++ tailWord_1585442) baseStart_1585442 baseEnd_1585442 := by
    simpa [prefixWord, tailWord_1585442, baseEnd_1585442] using wordTrace_append hprefix tailTrace_1585442
  have hstable : (prefixWord ++ tailWord_1585442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585442).length < 2 ^ (prefixWord ++ tailWord_1585442).sum := by decide
  have hdescent : baseEnd_1585442 < baseStart_1585442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
