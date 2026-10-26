import V185TrunkScan23Chunk0371

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2200122 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_2200122 : Nat := 118140960795 + 2200122 * 2 ^ 59
def prefixEnd_2200122 : Nat := 4983230072969 + 3 ^ 40 * 2200122 * 2
def baseEnd_2200122 : Nat := 1129720084531346246256829

theorem tailTrace_2200122 : CollatzResearch.WordTrace tailWord_2200122 prefixEnd_2200122 1129720084531346246256829 := by
  unfold tailWord_2200122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20061260433835304941912655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53496694490227479845100413 20061260433835304941912655)
  ·
    refine ⟨30091890650752957412868983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20061260433835304941912655 30091890650752957412868983)
    ·
      refine ⟨45137835976129436119303475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30091890650752957412868983 45137835976129436119303475)
      ·
        refine ⟨67706753964194154178955213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45137835976129436119303475 67706753964194154178955213)
        ·
          refine ⟨25390032736572807817108205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67706753964194154178955213 25390032736572807817108205)
          ·
            refine ⟨9521262276214802931415577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25390032736572807817108205 9521262276214802931415577)
            ·
              refine ⟨7140946707161102198561683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9521262276214802931415577 7140946707161102198561683)
              ·
                refine ⟨10711420060741653297842525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140946707161102198561683 10711420060741653297842525)
                ·
                  refine ⟨4016782522778119986690947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10711420060741653297842525 4016782522778119986690947)
                  ·
                    refine ⟨6025173784167179980036421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016782522778119986690947 6025173784167179980036421)
                    ·
                      refine ⟨1129720084531346246256829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6025173784167179980036421 1129720084531346246256829)
                      ·
                        rfl

theorem cell23_2200122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_2200122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200122 prefixEnd_2200122 := by exact prefixLift 2200122
  have htrace : WordTrace (prefixWord ++ tailWord_2200122) baseStart_2200122 baseEnd_2200122 := by
    simpa [prefixWord, tailWord_2200122, baseEnd_2200122] using wordTrace_append hprefix tailTrace_2200122
  have hstable : (prefixWord ++ tailWord_2200122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200122).length < 2 ^ (prefixWord ++ tailWord_2200122).sum := by decide
  have hdescent : baseEnd_2200122 < baseStart_2200122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200139 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 1, 1, 4]
def baseStart_2200139 : Nat := 118140960795 + 2200139 * 2 ^ 59
def prefixEnd_2200139 : Nat := 4983230072969 + 3 ^ 40 * 2200139 * 2
def baseEnd_2200139 : Nat := 1129728813702472679744251

theorem tailTrace_2200139 : CollatzResearch.WordTrace tailWord_2200139 prefixEnd_2200139 1129728813702472679744251 := by
  unfold tailWord_2200139
  simp only [CollatzResearch.WordTrace]
  refine ⟨80245661776279631671019471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497107850853087780679647 80245661776279631671019471)
  ·
    refine ⟨120368492664419447506529207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80245661776279631671019471 120368492664419447506529207)
    ·
      refine ⟨180552738996629171259793811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120368492664419447506529207 180552738996629171259793811)
      ·
        refine ⟨270829108494943756889690717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180552738996629171259793811 270829108494943756889690717)
        ·
          refine ⟨101560915685603908833634019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270829108494943756889690717 101560915685603908833634019)
          ·
            refine ⟨152341373528405863250451029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101560915685603908833634019 152341373528405863250451029)
            ·
              refine ⟨1785250471036006209966223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 152341373528405863250451029 1785250471036006209966223)
              ·
                refine ⟨2677875706554009314949335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785250471036006209966223 2677875706554009314949335)
                ·
                  refine ⟨4016813559831013972424003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677875706554009314949335 4016813559831013972424003)
                  ·
                    refine ⟨6025220339746520958636005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016813559831013972424003 6025220339746520958636005)
                    ·
                      refine ⟨1129728813702472679744251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6025220339746520958636005 1129728813702472679744251)
                      ·
                        rfl

theorem cell23_2200139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 1, 4].length) (baseStart_2200139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200139 prefixEnd_2200139 := by exact prefixLift 2200139
  have htrace : WordTrace (prefixWord ++ tailWord_2200139) baseStart_2200139 baseEnd_2200139 := by
    simpa [prefixWord, tailWord_2200139, baseEnd_2200139] using wordTrace_append hprefix tailTrace_2200139
  have hstable : (prefixWord ++ tailWord_2200139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200139).length < 2 ^ (prefixWord ++ tailWord_2200139).sum := by decide
  have hdescent : baseEnd_2200139 < baseStart_2200139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200145 : List Nat := [1, 2, 2, 1, 3, 4, 10]
def baseStart_2200145 : Nat := 118140960795 + 2200145 * 2 ^ 59
def prefixEnd_2200145 : Nat := 4983230072969 + 3 ^ 40 * 2200145 * 2
def baseEnd_2200145 : Nat := 13947307340572835262583

theorem tailTrace_2200145 : CollatzResearch.WordTrace tailWord_2200145 prefixEnd_2200145 13947307340572835262583 := by
  unfold tailWord_2200145
  simp only [CollatzResearch.WordTrace]
  refine ⟨80245880614257894695737889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497253742838596463825259 80245880614257894695737889)
  ·
    refine ⟨60184410460693421021803417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80245880614257894695737889 60184410460693421021803417)
    ·
      refine ⟨45138307845520065766352563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60184410460693421021803417 45138307845520065766352563)
      ·
        refine ⟨67707461768280098649528845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45138307845520065766352563 67707461768280098649528845)
        ·
          refine ⟨25390298163105036993573317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67707461768280098649528845 25390298163105036993573317)
          ·
            refine ⟨4760680905582194436294997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25390298163105036993573317 4760680905582194436294997)
            ·
              refine ⟨13947307340572835262583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4760680905582194436294997 13947307340572835262583)
              ·
                rfl

theorem cell23_2200145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 10].length) (baseStart_2200145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200145 prefixEnd_2200145 := by exact prefixLift 2200145
  have htrace : WordTrace (prefixWord ++ tailWord_2200145) baseStart_2200145 baseEnd_2200145 := by
    simpa [prefixWord, tailWord_2200145, baseEnd_2200145] using wordTrace_append hprefix tailTrace_2200145
  have hstable : (prefixWord ++ tailWord_2200145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200145).length < 2 ^ (prefixWord ++ tailWord_2200145).sum := by decide
  have hdescent : baseEnd_2200145 < baseStart_2200145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200149 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2200149 : Nat := 118140960795 + 2200149 * 2 ^ 59
def prefixEnd_2200149 : Nat := 4983230072969 + 3 ^ 40 * 2200149 * 2
def baseEnd_2200149 : Nat := 376577982836339213539735

theorem tailTrace_2200149 : CollatzResearch.WordTrace tailWord_2200149 prefixEnd_2200149 376577982836339213539735 := by
  unfold tailWord_2200149
  simp only [CollatzResearch.WordTrace]
  refine ⟨80246026506243403378883501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497351004162268919255667 80246026506243403378883501)
  ·
    refine ⟨30092259939841276267081313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80246026506243403378883501 30092259939841276267081313)
    ·
      refine ⟨22569194954880957200310985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30092259939841276267081313 22569194954880957200310985)
      ·
        refine ⟨16926896216160717900233239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22569194954880957200310985 16926896216160717900233239)
        ·
          refine ⟨25390344324241076850349859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16926896216160717900233239 25390344324241076850349859)
          ·
            refine ⟨38085516486361615275524789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25390344324241076850349859 38085516486361615275524789)
            ·
              refine ⟨3570517170596401432080449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38085516486361615275524789 3570517170596401432080449)
              ·
                refine ⟨2677887877947301074060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570517170596401432080449 2677887877947301074060337)
                ·
                  refine ⟨2008415908460475805545253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677887877947301074060337 2008415908460475805545253)
                  ·
                    refine ⟨376577982836339213539735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008415908460475805545253 376577982836339213539735)
                    ·
                      rfl

theorem cell23_2200149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2200149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200149 prefixEnd_2200149 := by exact prefixLift 2200149
  have htrace : WordTrace (prefixWord ++ tailWord_2200149) baseStart_2200149 baseEnd_2200149 := by
    simpa [prefixWord, tailWord_2200149, baseEnd_2200149] using wordTrace_append hprefix tailTrace_2200149
  have hstable : (prefixWord ++ tailWord_2200149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200149).length < 2 ^ (prefixWord ++ tailWord_2200149).sum := by decide
  have hdescent : baseEnd_2200149 < baseStart_2200149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200175 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 7]
def baseStart_2200175 : Nat := 118140960795 + 2200175 * 2 ^ 59
def prefixEnd_2200175 : Nat := 4983230072969 + 3 ^ 40 * 2200175 * 2
def baseEnd_2200175 : Nat := 376582433002011512964695

theorem tailTrace_2200175 : CollatzResearch.WordTrace tailWord_2200175 prefixEnd_2200175 376582433002011512964695 := by
  unfold tailWord_2200175
  simp only [CollatzResearch.WordTrace]
  refine ⟨80246974804149209819329979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53497983202766139879553319 80246974804149209819329979)
  ·
    refine ⟨120370462206223814728994969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80246974804149209819329979 120370462206223814728994969)
    ·
      refine ⟨90277846654667861046746227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120370462206223814728994969 90277846654667861046746227)
      ·
        refine ⟨135416769982001791570119341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90277846654667861046746227 135416769982001791570119341)
        ·
          refine ⟨50781288743250671838794753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135416769982001791570119341 50781288743250671838794753)
          ·
            refine ⟨38085966557438003879096065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50781288743250671838794753 38085966557438003879096065)
            ·
              refine ⟨28564474918078502909322049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38085966557438003879096065 28564474918078502909322049)
              ·
                refine ⟨21423356188558877181991537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28564474918078502909322049 21423356188558877181991537)
                ·
                  refine ⟨16067517141419157886493653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21423356188558877181991537 16067517141419157886493653)
                  ·
                    refine ⟨376582433002011512964695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16067517141419157886493653 376582433002011512964695)
                    ·
                      rfl

theorem cell23_2200175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_2200175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200175 prefixEnd_2200175 := by exact prefixLift 2200175
  have htrace : WordTrace (prefixWord ++ tailWord_2200175) baseStart_2200175 baseEnd_2200175 := by
    simpa [prefixWord, tailWord_2200175, baseEnd_2200175] using wordTrace_append hprefix tailTrace_2200175
  have hstable : (prefixWord ++ tailWord_2200175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200175).length < 2 ^ (prefixWord ++ tailWord_2200175).sum := by decide
  have hdescent : baseEnd_2200175 < baseStart_2200175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200176 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_2200176 : Nat := 118140960795 + 2200176 * 2 ^ 59
def prefixEnd_2200176 : Nat := 4983230072969 + 3 ^ 40 * 2200176 * 2
def baseEnd_2200176 : Nat := 1129747812486689034981581

theorem tailTrace_2200176 : CollatzResearch.WordTrace tailWord_2200176 prefixEnd_2200176 1129747812486689034981581 := by
  unfold tailWord_2200176
  simp only [CollatzResearch.WordTrace]
  refine ⟨40123505638572793495058191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53498007518097057993410921 40123505638572793495058191)
  ·
    refine ⟨60185258457859190242587287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40123505638572793495058191 60185258457859190242587287)
    ·
      refine ⟨90277887686788785363880931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60185258457859190242587287 90277887686788785363880931)
      ·
        refine ⟨135416831530183178045821397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90277887686788785363880931 135416831530183178045821397)
        ·
          refine ⟨3173831988988668235448939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 135416831530183178045821397 3173831988988668235448939)
          ·
            refine ⟨4760747983483002353173409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173831988988668235448939 4760747983483002353173409)
            ·
              refine ⟨3570560987612251764880057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760747983483002353173409 3570560987612251764880057)
              ·
                refine ⟨2677920740709188823660043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570560987612251764880057 2677920740709188823660043)
                ·
                  refine ⟨4016881111063783235490065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677920740709188823660043 4016881111063783235490065)
                  ·
                    refine ⟨3012660833297837426617549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016881111063783235490065 3012660833297837426617549)
                    ·
                      refine ⟨1129747812486689034981581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3012660833297837426617549 1129747812486689034981581)
                      ·
                        rfl

theorem cell23_2200176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_2200176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200176 prefixEnd_2200176 := by exact prefixLift 2200176
  have htrace : WordTrace (prefixWord ++ tailWord_2200176) baseStart_2200176 baseEnd_2200176 := by
    simpa [prefixWord, tailWord_2200176, baseEnd_2200176] using wordTrace_append hprefix tailTrace_2200176
  have hstable : (prefixWord ++ tailWord_2200176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200176).length < 2 ^ (prefixWord ++ tailWord_2200176).sum := by decide
  have hdescent : baseEnd_2200176 < baseStart_2200176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200206 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2200206 : Nat := 118140960795 + 2200206 * 2 ^ 59
def prefixEnd_2200206 : Nat := 4983230072969 + 3 ^ 40 * 2200206 * 2
def baseEnd_2200206 : Nat := 1129763216906323917606443

theorem tailTrace_2200206 : CollatzResearch.WordTrace tailWord_2200206 prefixEnd_2200206 1129763216906323917606443 := by
  unfold tailWord_2200206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031013183379612764213559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53498736978024601409138981 10031013183379612764213559)
  ·
    refine ⟨15046519775069419146320339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10031013183379612764213559 15046519775069419146320339)
    ·
      refine ⟨22569779662604128719480509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046519775069419146320339 22569779662604128719480509)
      ·
        refine ⟨8463667373476548269805191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22569779662604128719480509 8463667373476548269805191)
        ·
          refine ⟨12695501060214822404707787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463667373476548269805191 12695501060214822404707787)
          ·
            refine ⟨19043251590322233607061681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695501060214822404707787 19043251590322233607061681)
            ·
              refine ⟨14282438692741675205296261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19043251590322233607061681 14282438692741675205296261)
              ·
                refine ⟨2677957254889064100993049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14282438692741675205296261 2677957254889064100993049)
                ·
                  refine ⟨2008467941166798075744787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677957254889064100993049 2008467941166798075744787)
                  ·
                    refine ⟨3012701911750197113617181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2008467941166798075744787 3012701911750197113617181)
                    ·
                      refine ⟨1129763216906323917606443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3012701911750197113617181 1129763216906323917606443)
                      ·
                        rfl

theorem cell23_2200206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2200206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200206 prefixEnd_2200206 := by exact prefixLift 2200206
  have htrace : WordTrace (prefixWord ++ tailWord_2200206) baseStart_2200206 baseEnd_2200206 := by
    simpa [prefixWord, tailWord_2200206, baseEnd_2200206] using wordTrace_append hprefix tailTrace_2200206
  have hstable : (prefixWord ++ tailWord_2200206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200206).length < 2 ^ (prefixWord ++ tailWord_2200206).sum := by decide
  have hdescent : baseEnd_2200206 < baseStart_2200206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200229 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_2200229 : Nat := 118140960795 + 2200229 * 2 ^ 59
def prefixEnd_2200229 : Nat := 4983230072969 + 3 ^ 40 * 2200229 * 2
def baseEnd_2200229 : Nat := 1129775026961377327618837

theorem tailTrace_2200229 : CollatzResearch.WordTrace tailWord_2200229 prefixEnd_2200229 1129775026961377327618837 := by
  unfold tailWord_2200229
  simp only [CollatzResearch.WordTrace]
  refine ⟨80248944345953577041795741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53499296230635718027863827 80248944345953577041795741)
  ·
    refine ⟨30093354129732591390673403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80248944345953577041795741 30093354129732591390673403)
    ·
      refine ⟨45140031194598887086010105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30093354129732591390673403 45140031194598887086010105)
      ·
        refine ⟨33855023395949165314507579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45140031194598887086010105 33855023395949165314507579)
        ·
          refine ⟨50782535093923747971761369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33855023395949165314507579 50782535093923747971761369)
          ·
            refine ⟨38086901320442810978821027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50782535093923747971761369 38086901320442810978821027)
            ·
              refine ⟨57130351980664216468231541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38086901320442810978821027 57130351980664216468231541)
              ·
                refine ⟨5355970498187270293896707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57130351980664216468231541 5355970498187270293896707)
                ·
                  refine ⟨8033955747280905440845061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5355970498187270293896707 8033955747280905440845061)
                  ·
                    refine ⟨1506366702615169770158449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8033955747280905440845061 1506366702615169770158449)
                    ·
                      refine ⟨1129775026961377327618837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506366702615169770158449 1129775026961377327618837)
                      ·
                        rfl

theorem cell23_2200229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_2200229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200229 prefixEnd_2200229 := by exact prefixLift 2200229
  have htrace : WordTrace (prefixWord ++ tailWord_2200229) baseStart_2200229 baseEnd_2200229 := by
    simpa [prefixWord, tailWord_2200229, baseEnd_2200229] using wordTrace_append hprefix tailTrace_2200229
  have hstable : (prefixWord ++ tailWord_2200229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200229).length < 2 ^ (prefixWord ++ tailWord_2200229).sum := by decide
  have hdescent : baseEnd_2200229 < baseStart_2200229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200242 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2200242 : Nat := 118140960795 + 2200242 * 2 ^ 59
def prefixEnd_2200242 : Nat := 4983230072969 + 3 ^ 40 * 2200242 * 2
def baseEnd_2200242 : Nat := 1129781702209885776756277

theorem tailTrace_2200242 : CollatzResearch.WordTrace tailWord_2200242 prefixEnd_2200242 1129781702209885776756277 := by
  unfold tailWord_2200242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062354623726620065504745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53499612329937653508012653 20062354623726620065504745)
  ·
    refine ⟨15046765967794965049128559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20062354623726620065504745 15046765967794965049128559)
    ·
      refine ⟨22570148951692447573692839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046765967794965049128559 22570148951692447573692839)
      ·
        refine ⟨33855223427538671360539259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22570148951692447573692839 33855223427538671360539259)
        ·
          refine ⟨50782835141308007040808889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33855223427538671360539259 50782835141308007040808889)
          ·
            refine ⟨38087126355981005280606667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50782835141308007040808889 38087126355981005280606667)
            ·
              refine ⟨57130689533971507920910001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38087126355981005280606667 57130689533971507920910001)
              ·
                refine ⟨42848017150478630940682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57130689533971507920910001 42848017150478630940682501)
                ·
                  refine ⟨8034003215714743301377969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42848017150478630940682501 8034003215714743301377969)
                  ·
                    refine ⟨6025502411786057476033477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8034003215714743301377969 6025502411786057476033477)
                    ·
                      refine ⟨1129781702209885776756277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6025502411786057476033477 1129781702209885776756277)
                      ·
                        rfl

theorem cell23_2200242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2200242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200242 prefixEnd_2200242 := by exact prefixLift 2200242
  have htrace : WordTrace (prefixWord ++ tailWord_2200242) baseStart_2200242 baseEnd_2200242 := by
    simpa [prefixWord, tailWord_2200242, baseEnd_2200242] using wordTrace_append hprefix tailTrace_2200242
  have hstable : (prefixWord ++ tailWord_2200242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200242).length < 2 ^ (prefixWord ++ tailWord_2200242).sum := by decide
  have hdescent : baseEnd_2200242 < baseStart_2200242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200276 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2200276 : Nat := 118140960795 + 2200276 * 2 ^ 59
def prefixEnd_2200276 : Nat := 4983230072969 + 3 ^ 40 * 2200276 * 2
def baseEnd_2200276 : Nat := 1129799160552138643731121

theorem tailTrace_2200276 : CollatzResearch.WordTrace tailWord_2200276 prefixEnd_2200276 1129799160552138643731121 := by
  unfold tailWord_2200276
  simp only [CollatzResearch.WordTrace]
  refine ⟨40125329288391652034378341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53500439051188869379171121 40125329288391652034378341)
  ·
    refine ⟨7523499241573434756445939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40125329288391652034378341 7523499241573434756445939)
    ·
      refine ⟨11285248862360152134668909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7523499241573434756445939 11285248862360152134668909)
      ·
        refine ⟨4231968323385057050500841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11285248862360152134668909 4231968323385057050500841)
        ·
          refine ⟨3173976242538792787875631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231968323385057050500841 3173976242538792787875631)
          ·
            refine ⟨4760964363808189181813447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173976242538792787875631 4760964363808189181813447)
            ·
              refine ⟨7141446545712283772720171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760964363808189181813447 7141446545712283772720171)
              ·
                refine ⟨10712169818568425659080257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141446545712283772720171 10712169818568425659080257)
                ·
                  refine ⟨8034127363926319244310193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10712169818568425659080257 8034127363926319244310193)
                  ·
                    refine ⟨6025595522944739433232645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8034127363926319244310193 6025595522944739433232645)
                    ·
                      refine ⟨1129799160552138643731121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6025595522944739433232645 1129799160552138643731121)
                      ·
                        rfl

theorem cell23_2200276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2200276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200276 prefixEnd_2200276 := by exact prefixLift 2200276
  have htrace : WordTrace (prefixWord ++ tailWord_2200276) baseStart_2200276 baseEnd_2200276 := by
    simpa [prefixWord, tailWord_2200276, baseEnd_2200276] using wordTrace_append hprefix tailTrace_2200276
  have hstable : (prefixWord ++ tailWord_2200276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200276).length < 2 ^ (prefixWord ++ tailWord_2200276).sum := by decide
  have hdescent : baseEnd_2200276 < baseStart_2200276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200279 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_2200279 : Nat := 118140960795 + 2200279 * 2 ^ 59
def prefixEnd_2200279 : Nat := 4983230072969 + 3 ^ 40 * 2200279 * 2
def baseEnd_2200279 : Nat := 1129800700994102131993607

theorem tailTrace_2200279 : CollatzResearch.WordTrace tailWord_2200279 prefixEnd_2200279 1129800700994102131993607 := by
  unfold tailWord_2200279
  simp only [CollatzResearch.WordTrace]
  refine ⟨80250767995772435581115891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53500511997181623720743927 80250767995772435581115891)
  ·
    refine ⟨120376151993658653371673837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80250767995772435581115891 120376151993658653371673837)
    ·
      refine ⟨45141056997621995014377689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120376151993658653371673837 45141056997621995014377689)
      ·
        refine ⟨33855792748216496260783267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45141056997621995014377689 33855792748216496260783267)
        ·
          refine ⟨50783689122324744391174901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33855792748216496260783267 50783689122324744391174901)
          ·
            refine ⟨4760970855217944786672647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50783689122324744391174901 4760970855217944786672647)
            ·
              refine ⟨7141456282826917180008971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760970855217944786672647 7141456282826917180008971)
              ·
                refine ⟨10712184424240375770013457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7141456282826917180008971 10712184424240375770013457)
                ·
                  refine ⟨8034138318180281827510093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10712184424240375770013457 8034138318180281827510093)
                  ·
                    refine ⟨3012801869317605685316285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8034138318180281827510093 3012801869317605685316285)
                    ·
                      refine ⟨1129800700994102131993607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3012801869317605685316285 1129800700994102131993607)
                      ·
                        rfl

theorem cell23_2200279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_2200279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200279 prefixEnd_2200279 := by exact prefixLift 2200279
  have htrace : WordTrace (prefixWord ++ tailWord_2200279) baseStart_2200279 baseEnd_2200279 := by
    simpa [prefixWord, tailWord_2200279, baseEnd_2200279] using wordTrace_append hprefix tailTrace_2200279
  have hstable : (prefixWord ++ tailWord_2200279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200279).length < 2 ^ (prefixWord ++ tailWord_2200279).sum := by decide
  have hdescent : baseEnd_2200279 < baseStart_2200279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200282 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_2200282 : Nat := 118140960795 + 2200282 * 2 ^ 59
def prefixEnd_2200282 : Nat := 4983230072969 + 3 ^ 40 * 2200282 * 2
def baseEnd_2200282 : Nat := 376600747145355206752031

theorem tailTrace_2200282 : CollatzResearch.WordTrace tailWord_2200282 prefixEnd_2200282 376600747145355206752031 := by
  unfold tailWord_2200282
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062719353690391773368775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53500584943174378062316733 20062719353690391773368775)
  ·
    refine ⟨30094079030535587660053163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20062719353690391773368775 30094079030535587660053163)
    ·
      refine ⟨45141118545803381490079745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30094079030535587660053163 45141118545803381490079745)
      ·
        refine ⟨33855838909352536117559809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45141118545803381490079745 33855838909352536117559809)
        ·
          refine ⟨25391879182014402088169857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33855838909352536117559809 25391879182014402088169857)
          ·
            refine ⟨19043909386510801566127393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25391879182014402088169857 19043909386510801566127393)
            ·
              refine ⟨14282932039883101174595545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19043909386510801566127393 14282932039883101174595545)
              ·
                refine ⟨10712199029912325880946659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14282932039883101174595545 10712199029912325880946659)
                ·
                  refine ⟨16068298544868488821419989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10712199029912325880946659 16068298544868488821419989)
                  ·
                    refine ⟨376600747145355206752031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16068298544868488821419989 376600747145355206752031)
                    ·
                      rfl

theorem cell23_2200282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_2200282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200282 prefixEnd_2200282 := by exact prefixLift 2200282
  have htrace : WordTrace (prefixWord ++ tailWord_2200282) baseStart_2200282 baseEnd_2200282 := by
    simpa [prefixWord, tailWord_2200282, baseEnd_2200282] using wordTrace_append hprefix tailTrace_2200282
  have hstable : (prefixWord ++ tailWord_2200282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200282).length < 2 ^ (prefixWord ++ tailWord_2200282).sum := by decide
  have hdescent : baseEnd_2200282 < baseStart_2200282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200329 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_2200329 : Nat := 118140960795 + 2200329 * 2 ^ 59
def prefixEnd_2200329 : Nat := 4983230072969 + 3 ^ 40 * 2200329 * 2
def baseEnd_2200329 : Nat := 376608791675608978789459

theorem tailTrace_2200329 : CollatzResearch.WordTrace tailWord_2200329 prefixEnd_2200329 376608791675608978789459 := by
  unfold tailWord_2200329
  simp only [CollatzResearch.WordTrace]
  refine ⟨80252591645591294120436041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53501727763727529413624027 80252591645591294120436041)
  ·
    refine ⟨60189443734193470590327031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80252591645591294120436041 60189443734193470590327031)
    ·
      refine ⟨90284165601290205885490547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60189443734193470590327031 90284165601290205885490547)
      ·
        refine ⟨135426248401935308828235821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90284165601290205885490547 135426248401935308828235821)
        ·
          refine ⟨50784843150725740810588433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135426248401935308828235821 50784843150725740810588433)
          ·
            refine ⟨38088632363044305607941325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50784843150725740810588433 38088632363044305607941325)
            ·
              refine ⟨14283237136141614602977997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38088632363044305607941325 14283237136141614602977997)
              ·
                refine ⟨5356213926053105476116749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14283237136141614602977997 5356213926053105476116749)
                ·
                  refine ⟨2008580222269914553543781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5356213926053105476116749 2008580222269914553543781)
                  ·
                    refine ⟨376608791675608978789459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008580222269914553543781 376608791675608978789459)
                    ·
                      rfl

theorem cell23_2200329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_2200329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200329 prefixEnd_2200329 := by exact prefixLift 2200329
  have htrace : WordTrace (prefixWord ++ tailWord_2200329) baseStart_2200329 baseEnd_2200329 := by
    simpa [prefixWord, tailWord_2200329, baseEnd_2200329] using wordTrace_append hprefix tailTrace_2200329
  have hstable : (prefixWord ++ tailWord_2200329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200329).length < 2 ^ (prefixWord ++ tailWord_2200329).sum := by decide
  have hdescent : baseEnd_2200329 < baseStart_2200329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200332 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2200332 : Nat := 118140960795 + 2200332 * 2 ^ 59
def prefixEnd_2200332 : Nat := 4983230072969 + 3 ^ 40 * 2200332 * 2
def baseEnd_2200332 : Nat := 1129827915468790424630863

theorem tailTrace_2200332 : CollatzResearch.WordTrace tailWord_2200332 prefixEnd_2200332 1129827915468790424630863 := by
  unfold tailWord_2200332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40126350532290212816397625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53501800709720283755196833 40126350532290212816397625)
  ·
    refine ⟨30094762899217659612298219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40126350532290212816397625 30094762899217659612298219)
    ·
      refine ⟨45142144348826489418447329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30094762899217659612298219 45142144348826489418447329)
      ·
        refine ⟨33856608261619867063835497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45142144348826489418447329 33856608261619867063835497)
        ·
          refine ⟨25392456196214900297876623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33856608261619867063835497 25392456196214900297876623)
          ·
            refine ⟨38088684294322350446814935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25392456196214900297876623 38088684294322350446814935)
            ·
              refine ⟨57133026441483525670222403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38088684294322350446814935 57133026441483525670222403)
              ·
                refine ⟨85699539662225288505333605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57133026441483525670222403 85699539662225288505333605)
                ·
                  refine ⟨16068663686667241594750051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85699539662225288505333605 16068663686667241594750051)
                  ·
                    refine ⟨24102995530000862392125077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16068663686667241594750051 24102995530000862392125077)
                    ·
                      refine ⟨1129827915468790424630863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24102995530000862392125077 1129827915468790424630863)
                      ·
                        rfl

theorem cell23_2200332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2200332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200332 prefixEnd_2200332 := by exact prefixLift 2200332
  have htrace : WordTrace (prefixWord ++ tailWord_2200332) baseStart_2200332 baseEnd_2200332 := by
    simpa [prefixWord, tailWord_2200332, baseEnd_2200332] using wordTrace_append hprefix tailTrace_2200332
  have hstable : (prefixWord ++ tailWord_2200332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200332).length < 2 ^ (prefixWord ++ tailWord_2200332).sum := by decide
  have hdescent : baseEnd_2200332 < baseStart_2200332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200379 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 11, 2]
def baseStart_2200379 : Nat := 118140960795 + 2200379 * 2 ^ 59
def prefixEnd_2200379 : Nat := 4983230072969 + 3 ^ 40 * 2200379 * 2
def baseEnd_2200379 : Nat := 1129852049059551740743147

theorem tailTrace_2200379 : CollatzResearch.WordTrace tailWord_2200379 prefixEnd_2200379 1129852049059551740743147 := by
  unfold tailWord_2200379
  simp only [CollatzResearch.WordTrace]
  refine ⟨80254415295410152659756191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53502943530273435106504127 80254415295410152659756191)
  ·
    refine ⟨120381622943115228989634287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80254415295410152659756191 120381622943115228989634287)
    ·
      refine ⟨180572434414672843484451431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120381622943115228989634287 180572434414672843484451431)
      ·
        refine ⟨270858651622009265226677147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180572434414672843484451431 270858651622009265226677147)
        ·
          refine ⟨406287977433013897840015721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270858651622009265226677147 406287977433013897840015721)
          ·
            refine ⟨304715983074760423380011791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406287977433013897840015721 304715983074760423380011791)
            ·
              refine ⟨457073974612140635070017687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304715983074760423380011791 457073974612140635070017687)
              ·
                refine ⟨685610961918210952605026531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457073974612140635070017687 685610961918210952605026531)
                ·
                  refine ⟨1028416442877316428907539797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685610961918210952605026531 1028416442877316428907539797)
                  ·
                    refine ⟨1506469398746068987657529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 1028416442877316428907539797 1506469398746068987657529)
                    ·
                      refine ⟨1129852049059551740743147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506469398746068987657529 1129852049059551740743147)
                      ·
                        rfl

theorem cell23_2200379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11, 2].length) (baseStart_2200379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200379 prefixEnd_2200379 := by exact prefixLift 2200379
  have htrace : WordTrace (prefixWord ++ tailWord_2200379) baseStart_2200379 baseEnd_2200379 := by
    simpa [prefixWord, tailWord_2200379, baseEnd_2200379] using wordTrace_append hprefix tailTrace_2200379
  have hstable : (prefixWord ++ tailWord_2200379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200379).length < 2 ^ (prefixWord ++ tailWord_2200379).sum := by decide
  have hdescent : baseEnd_2200379 < baseStart_2200379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200419 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 6]
def baseStart_2200419 : Nat := 118140960795 + 2200419 * 2 ^ 59
def prefixEnd_2200419 : Nat := 4983230072969 + 3 ^ 40 * 2200419 * 2
def baseEnd_2200419 : Nat := 376624196095243861414321

theorem tailTrace_2200419 : CollatzResearch.WordTrace tailWord_2200419 prefixEnd_2200419 376624196095243861414321 := by
  unfold tailWord_2200419
  simp only [CollatzResearch.WordTrace]
  refine ⟨80255874215265239491212311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53503916143510159660808207 80255874215265239491212311)
  ·
    refine ⟨120383811322897859236818467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80255874215265239491212311 120383811322897859236818467)
    ·
      refine ⟨180575716984346788855227701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120383811322897859236818467 180575716984346788855227701)
      ·
        refine ⟨16928973467282511455177597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180575716984346788855227701 16928973467282511455177597)
        ·
          refine ⟨6348365050230941795691599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16928973467282511455177597 6348365050230941795691599)
          ·
            refine ⟨9522547575346412693537399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348365050230941795691599 9522547575346412693537399)
            ·
              refine ⟨14283821363019619040306099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522547575346412693537399 14283821363019619040306099)
              ·
                refine ⟨21425732044529428560459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14283821363019619040306099 21425732044529428560459149)
                ·
                  refine ⟨8034649516698535710172181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21425732044529428560459149 8034649516698535710172181)
                  ·
                    refine ⟨376624196095243861414321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8034649516698535710172181 376624196095243861414321)
                    ·
                      rfl

theorem cell23_2200419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_2200419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200419 prefixEnd_2200419 := by exact prefixLift 2200419
  have htrace : WordTrace (prefixWord ++ tailWord_2200419) baseStart_2200419 baseEnd_2200419 := by
    simpa [prefixWord, tailWord_2200419, baseEnd_2200419] using wordTrace_append hprefix tailTrace_2200419
  have hstable : (prefixWord ++ tailWord_2200419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200419).length < 2 ^ (prefixWord ++ tailWord_2200419).sum := by decide
  have hdescent : baseEnd_2200419 < baseStart_2200419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200423 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2200423 : Nat := 118140960795 + 2200423 * 2 ^ 59
def prefixEnd_2200423 : Nat := 4983230072969 + 3 ^ 40 * 2200423 * 2
def baseEnd_2200423 : Nat := 376624880736116522864315

theorem tailTrace_2200423 : CollatzResearch.WordTrace tailWord_2200423 prefixEnd_2200423 376624880736116522864315 := by
  unfold tailWord_2200423
  simp only [CollatzResearch.WordTrace]
  refine ⟨80256020107250748174357923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53504013404833832116238615 80256020107250748174357923)
  ·
    refine ⟨120384030160876122261536885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80256020107250748174357923 120384030160876122261536885)
    ·
      refine ⟨11286002827582136462019083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120384030160876122261536885 11286002827582136462019083)
      ·
        refine ⟨16929004241373204693028625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286002827582136462019083 16929004241373204693028625)
        ·
          refine ⟨12696753181029903519771469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16929004241373204693028625 12696753181029903519771469)
          ·
            refine ⟨4761282442886213819914301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12696753181029903519771469 4761282442886213819914301)
            ·
              refine ⟨1785480916082330182467863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4761282442886213819914301 1785480916082330182467863)
              ·
                refine ⟨2678221374123495273701795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785480916082330182467863 2678221374123495273701795)
                ·
                  refine ⟨4017332061185242910552693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678221374123495273701795 4017332061185242910552693)
                  ·
                    refine ⟨376624880736116522864315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4017332061185242910552693 376624880736116522864315)
                    ·
                      rfl

theorem cell23_2200423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2200423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200423 prefixEnd_2200423 := by exact prefixLift 2200423
  have htrace : WordTrace (prefixWord ++ tailWord_2200423) baseStart_2200423 baseEnd_2200423 := by
    simpa [prefixWord, tailWord_2200423, baseEnd_2200423] using wordTrace_append hprefix tailTrace_2200423
  have hstable : (prefixWord ++ tailWord_2200423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200423).length < 2 ^ (prefixWord ++ tailWord_2200423).sum := by decide
  have hdescent : baseEnd_2200423 < baseStart_2200423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200437 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2200437 : Nat := 118140960795 + 2200437 * 2 ^ 59
def prefixEnd_2200437 : Nat := 4983230072969 + 3 ^ 40 * 2200437 * 2
def baseEnd_2200437 : Nat := 1129881830937512513817881

theorem tailTrace_2200437 : CollatzResearch.WordTrace tailWord_2200437 prefixEnd_2200437 1129881830937512513817881 := by
  unfold tailWord_2200437
  simp only [CollatzResearch.WordTrace]
  refine ⟨80256530729200028565367565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53504353819466685710245043 80256530729200028565367565)
  ·
    refine ⟨30096199023450010712012837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80256530729200028565367565 30096199023450010712012837)
    ·
      refine ⟨5643037316896877008502407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30096199023450010712012837 5643037316896877008502407)
      ·
        refine ⟨8464555975345315512753611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643037316896877008502407 8464555975345315512753611)
        ·
          refine ⟨12696833963017973269130417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464555975345315512753611 12696833963017973269130417)
          ·
            refine ⟨9522625472263479951847813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12696833963017973269130417 9522625472263479951847813)
            ·
              refine ⟨1785492276049402490971465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9522625472263479951847813 1785492276049402490971465)
              ·
                refine ⟨1339119207037051868228599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785492276049402490971465 1339119207037051868228599)
                ·
                  refine ⟨2008678810555577802342899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339119207037051868228599 2008678810555577802342899)
                  ·
                    refine ⟨3013018215833366703514349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2008678810555577802342899 3013018215833366703514349)
                    ·
                      refine ⟨1129881830937512513817881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3013018215833366703514349 1129881830937512513817881)
                      ·
                        rfl

theorem cell23_2200437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2200437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200437 prefixEnd_2200437 := by exact prefixLift 2200437
  have htrace : WordTrace (prefixWord ++ tailWord_2200437) baseStart_2200437 baseEnd_2200437 := by
    simpa [prefixWord, tailWord_2200437, baseEnd_2200437] using wordTrace_append hprefix tailTrace_2200437
  have hstable : (prefixWord ++ tailWord_2200437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200437).length < 2 ^ (prefixWord ++ tailWord_2200437).sum := by decide
  have hdescent : baseEnd_2200437 < baseStart_2200437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200456 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2200456 : Nat := 118140960795 + 2200456 * 2 ^ 59
def prefixEnd_2200456 : Nat := 4983230072969 + 3 ^ 40 * 2200456 * 2
def baseEnd_2200456 : Nat := 1129891587069947939480293

theorem tailTrace_2200456 : CollatzResearch.WordTrace tailWord_2200456 prefixEnd_2200456 1129891587069947939480293 := by
  unfold tailWord_2200456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40128611858065597405154611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53504815810754129873539481 40128611858065597405154611)
  ·
    refine ⟨60192917787098396107731917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40128611858065597405154611 60192917787098396107731917)
    ·
      refine ⟨22572344170161898540399469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60192917787098396107731917 22572344170161898540399469)
      ·
        refine ⟨8464629063810711952649801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22572344170161898540399469 8464629063810711952649801)
        ·
          refine ⟨6348471797858033964487351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8464629063810711952649801 6348471797858033964487351)
          ·
            refine ⟨9522707696787050946731027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348471797858033964487351 9522707696787050946731027)
            ·
              refine ⟨14284061545180576420096541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9522707696787050946731027 14284061545180576420096541)
              ·
                refine ⟨5356523079442716157536203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14284061545180576420096541 5356523079442716157536203)
                ·
                  refine ⟨8034784619164074236304305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356523079442716157536203 8034784619164074236304305)
                  ·
                    refine ⟨6026088464373055677228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8034784619164074236304305 6026088464373055677228229)
                    ·
                      refine ⟨1129891587069947939480293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6026088464373055677228229 1129891587069947939480293)
                      ·
                        rfl

theorem cell23_2200456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2200456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200456 prefixEnd_2200456 := by exact prefixLift 2200456
  have htrace : WordTrace (prefixWord ++ tailWord_2200456) baseStart_2200456 baseEnd_2200456 := by
    simpa [prefixWord, tailWord_2200456, baseEnd_2200456] using wordTrace_append hprefix tailTrace_2200456
  have hstable : (prefixWord ++ tailWord_2200456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200456).length < 2 ^ (prefixWord ++ tailWord_2200456).sum := by decide
  have hdescent : baseEnd_2200456 < baseStart_2200456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200470 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2200470 : Nat := 118140960795 + 2200470 * 2 ^ 59
def prefixEnd_2200470 : Nat := 4983230072969 + 3 ^ 40 * 2200470 * 2
def baseEnd_2200470 : Nat := 376632925266370294901743

theorem tailTrace_2200470 : CollatzResearch.WordTrace tailWord_2200470 prefixEnd_2200470 376632925266370294901743 := by
  unfold tailWord_2200470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016108396130029700082429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53505156225386983467545909 5016108396130029700082429)
  ·
    refine ⟨1881040648548761137530911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5016108396130029700082429 1881040648548761137530911)
    ·
      refine ⟨2821560972823141706296367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881040648548761137530911 2821560972823141706296367)
      ·
        refine ⟨4232341459234712559444551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821560972823141706296367 4232341459234712559444551)
        ·
          refine ⟨6348512188852068839166827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232341459234712559444551 6348512188852068839166827)
          ·
            refine ⟨9522768283278103258750241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348512188852068839166827 9522768283278103258750241)
            ·
              refine ⟨7142076212458577444062681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9522768283278103258750241 7142076212458577444062681)
              ·
                refine ⟨5356557159343933083047011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7142076212458577444062681 5356557159343933083047011)
                ·
                  refine ⟨8034835739015899624570517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356557159343933083047011 8034835739015899624570517)
                  ·
                    refine ⟨376632925266370294901743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8034835739015899624570517 376632925266370294901743)
                    ·
                      rfl

theorem cell23_2200470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2200470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200470 prefixEnd_2200470 := by exact prefixLift 2200470
  have htrace : WordTrace (prefixWord ++ tailWord_2200470) baseStart_2200470 baseEnd_2200470 := by
    simpa [prefixWord, tailWord_2200470, baseEnd_2200470] using wordTrace_append hprefix tailTrace_2200470
  have hstable : (prefixWord ++ tailWord_2200470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200470).length < 2 ^ (prefixWord ++ tailWord_2200470).sum := by decide
  have hdescent : baseEnd_2200470 < baseStart_2200470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200477 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_2200477 : Nat := 118140960795 + 2200477 * 2 ^ 59
def prefixEnd_2200477 : Nat := 4983230072969 + 3 ^ 40 * 2200477 * 2
def baseEnd_2200477 : Nat := 1129902370163692357317697

theorem tailTrace_2200477 : CollatzResearch.WordTrace tailWord_2200477 prefixEnd_2200477 1129902370163692357317697 := by
  unfold tailWord_2200477
  simp only [CollatzResearch.WordTrace]
  refine ⟨80257989649055115396823685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53505326432703410264549123 80257989649055115396823685)
  ·
    refine ⟨15048373059197834136904441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80257989649055115396823685 15048373059197834136904441)
    ·
      refine ⟨11286279794398375602678331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15048373059197834136904441 11286279794398375602678331)
      ·
        refine ⟨16929419691597563404017497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286279794398375602678331 16929419691597563404017497)
        ·
          refine ⟨12697064768698172553013123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16929419691597563404017497 12697064768698172553013123)
          ·
            refine ⟨19045597153047258829519685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12697064768698172553013123 19045597153047258829519685)
            ·
              refine ⟨3571049466196361030534941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19045597153047258829519685 3571049466196361030534941)
              ·
                refine ⟨1339143549823635386450603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3571049466196361030534941 1339143549823635386450603)
                ·
                  refine ⟨2008715324735453079675905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339143549823635386450603 2008715324735453079675905)
                  ·
                    refine ⟨1506536493551589809756929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2008715324735453079675905 1506536493551589809756929)
                    ·
                      refine ⟨1129902370163692357317697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506536493551589809756929 1129902370163692357317697)
                      ·
                        rfl

theorem cell23_2200477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_2200477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200477 prefixEnd_2200477 := by exact prefixLift 2200477
  have htrace : WordTrace (prefixWord ++ tailWord_2200477) baseStart_2200477 baseEnd_2200477 := by
    simpa [prefixWord, tailWord_2200477, baseEnd_2200477] using wordTrace_append hprefix tailTrace_2200477
  have hstable : (prefixWord ++ tailWord_2200477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200477).length < 2 ^ (prefixWord ++ tailWord_2200477).sum := by decide
  have hdescent : baseEnd_2200477 < baseStart_2200477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200487 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2200487 : Nat := 118140960795 + 2200487 * 2 ^ 59
def prefixEnd_2200487 : Nat := 4983230072969 + 3 ^ 40 * 2200487 * 2
def baseEnd_2200487 : Nat := 376635834990079106064217

theorem tailTrace_2200487 : CollatzResearch.WordTrace tailWord_2200487 prefixEnd_2200487 376635834990079106064217 := by
  unfold tailWord_2200487
  simp only [CollatzResearch.WordTrace]
  refine ⟨80258354379018887104687715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53505569586012591403125143 80258354379018887104687715)
  ·
    refine ⟨120387531568528330657031573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80258354379018887104687715 120387531568528330657031573)
    ·
      refine ⟨5643165542274765499548355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120387531568528330657031573 5643165542274765499548355)
      ·
        refine ⟨8464748313412148249322533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643165542274765499548355 8464748313412148249322533)
        ·
          refine ⟨1587140308764777796747975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8464748313412148249322533 1587140308764777796747975)
          ·
            refine ⟨2380710463147166695121963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587140308764777796747975 2380710463147166695121963)
            ·
              refine ⟨3571065694720750042682945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380710463147166695121963 3571065694720750042682945)
              ·
                refine ⟨2678299271040562532012209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571065694720750042682945 2678299271040562532012209)
                ·
                  refine ⟨2008724453280421899009157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678299271040562532012209 2008724453280421899009157)
                  ·
                    refine ⟨376635834990079106064217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008724453280421899009157 376635834990079106064217)
                    ·
                      rfl

theorem cell23_2200487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2200487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200487 prefixEnd_2200487 := by exact prefixLift 2200487
  have htrace : WordTrace (prefixWord ++ tailWord_2200487) baseStart_2200487 baseEnd_2200487 := by
    simpa [prefixWord, tailWord_2200487, baseEnd_2200487] using wordTrace_append hprefix tailTrace_2200487
  have hstable : (prefixWord ++ tailWord_2200487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200487).length < 2 ^ (prefixWord ++ tailWord_2200487).sum := by decide
  have hdescent : baseEnd_2200487 < baseStart_2200487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200499 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_2200499 : Nat := 118140960795 + 2200499 * 2 ^ 59
def prefixEnd_2200499 : Nat := 4983230072969 + 3 ^ 40 * 2200499 * 2
def baseEnd_2200499 : Nat := 1129913666738091271242595

theorem tailTrace_2200499 : CollatzResearch.WordTrace tailWord_2200499 prefixEnd_2200499 1129913666738091271242595 := by
  unfold tailWord_2200499
  simp only [CollatzResearch.WordTrace]
  refine ⟨80258792054975413154124551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53505861369983608769416367 80258792054975413154124551)
  ·
    refine ⟨120388188082463119731186827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80258792054975413154124551 120388188082463119731186827)
    ·
      refine ⟨180582282123694679596780241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120388188082463119731186827 180582282123694679596780241)
      ·
        refine ⟨135436711592771009697585181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180582282123694679596780241 135436711592771009697585181)
        ·
          refine ⟨50788766847289128636594443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135436711592771009697585181 50788766847289128636594443)
          ·
            refine ⟨76183150270933692954891665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50788766847289128636594443 76183150270933692954891665)
            ·
              refine ⟨57137362703200269716168749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76183150270933692954891665 57137362703200269716168749)
              ·
                refine ⟨21426511013700101143563281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57137362703200269716168749 21426511013700101143563281)
                ·
                  refine ⟨16069883260275075857672461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21426511013700101143563281 16069883260275075857672461)
                  ·
                    refine ⟨6026206222603153446627173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16069883260275075857672461 6026206222603153446627173)
                    ·
                      refine ⟨1129913666738091271242595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6026206222603153446627173 1129913666738091271242595)
                      ·
                        rfl

theorem cell23_2200499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_2200499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200499 prefixEnd_2200499 := by exact prefixLift 2200499
  have htrace : WordTrace (prefixWord ++ tailWord_2200499) baseStart_2200499 baseEnd_2200499 := by
    simpa [prefixWord, tailWord_2200499, baseEnd_2200499] using wordTrace_append hprefix tailTrace_2200499
  have hstable : (prefixWord ++ tailWord_2200499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200499).length < 2 ^ (prefixWord ++ tailWord_2200499).sum := by decide
  have hdescent : baseEnd_2200499 < baseStart_2200499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200536 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2200536 : Nat := 118140960795 + 2200536 * 2 ^ 59
def prefixEnd_2200536 : Nat := 4983230072969 + 3 ^ 40 * 2200536 * 2
def baseEnd_2200536 : Nat := 1129932665522307626479925

theorem tailTrace_2200536 : CollatzResearch.WordTrace tailWord_2200536 prefixEnd_2200536 1129932665522307626479925 := by
  unfold tailWord_2200536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40130070777920684236610731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53506761037227578982147641 40130070777920684236610731)
  ·
    refine ⟨60195106166881026354916097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40130070777920684236610731 60195106166881026354916097)
    ·
      refine ⟨45146329625160769766187073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60195106166881026354916097 45146329625160769766187073)
      ·
        refine ⟨33859747218870577324640305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45146329625160769766187073 33859747218870577324640305)
        ·
          refine ⟨25394810414152932993480229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33859747218870577324640305 25394810414152932993480229)
          ·
            refine ⟨4761526952653674936277543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25394810414152932993480229 4761526952653674936277543)
            ·
              refine ⟨7142290428980512404416315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761526952653674936277543 7142290428980512404416315)
              ·
                refine ⟨10713435643470768606624473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7142290428980512404416315 10713435643470768606624473)
                ·
                  refine ⟨8035076732603076454968355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10713435643470768606624473 8035076732603076454968355)
                  ·
                    refine ⟨12052615098904614682452533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8035076732603076454968355 12052615098904614682452533)
                    ·
                      refine ⟨1129932665522307626479925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12052615098904614682452533 1129932665522307626479925)
                      ·
                        rfl

theorem cell23_2200536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2200536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200536 prefixEnd_2200536 := by exact prefixLift 2200536
  have htrace : WordTrace (prefixWord ++ tailWord_2200536) baseStart_2200536 baseEnd_2200536 := by
    simpa [prefixWord, tailWord_2200536, baseEnd_2200536] using wordTrace_append hprefix tailTrace_2200536
  have hstable : (prefixWord ++ tailWord_2200536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200536).length < 2 ^ (prefixWord ++ tailWord_2200536).sum := by decide
  have hdescent : baseEnd_2200536 < baseStart_2200536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200633 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_2200633 : Nat := 118140960795 + 2200633 * 2 ^ 59
def prefixEnd_2200633 : Nat := 4983230072969 + 3 ^ 40 * 2200633 * 2
def baseEnd_2200633 : Nat := 376660824381931248988993

theorem tailTrace_2200633 : CollatzResearch.WordTrace tailWord_2200633 prefixEnd_2200633 376660824381931248988993 := by
  unfold tailWord_2200633
  simp only [CollatzResearch.WordTrace]
  refine ⟨80263679436489954039502553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53509119624326636026335035 80263679436489954039502553)
  ·
    refine ⟨60197759577367465529626915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80263679436489954039502553 60197759577367465529626915)
    ·
      refine ⟨90296639366051198294440373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60197759577367465529626915 90296639366051198294440373)
      ·
        refine ⟨8465309940567299840103785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90296639366051198294440373 8465309940567299840103785)
        ·
          refine ⟨6348982455425474880077839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8465309940567299840103785 6348982455425474880077839)
          ·
            refine ⟨9523473683138212320116759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348982455425474880077839 9523473683138212320116759)
            ·
              refine ⟨14285210524707318480175139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523473683138212320116759 14285210524707318480175139)
              ·
                refine ⟨21427815787060977720262709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285210524707318480175139 21427815787060977720262709)
                ·
                  refine ⟨2008857730036966661274629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21427815787060977720262709 2008857730036966661274629)
                  ·
                    refine ⟨376660824381931248988993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008857730036966661274629 376660824381931248988993)
                    ·
                      rfl

theorem cell23_2200633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_2200633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200633 prefixEnd_2200633 := by exact prefixLift 2200633
  have htrace : WordTrace (prefixWord ++ tailWord_2200633) baseStart_2200633 baseEnd_2200633 := by
    simpa [prefixWord, tailWord_2200633, baseEnd_2200633] using wordTrace_append hprefix tailTrace_2200633
  have hstable : (prefixWord ++ tailWord_2200633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200633).length < 2 ^ (prefixWord ++ tailWord_2200633).sum := by decide
  have hdescent : baseEnd_2200633 < baseStart_2200633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200650 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_2200650 : Nat := 118140960795 + 2200650 * 2 ^ 59
def prefixEnd_2200650 : Nat := 4983230072969 + 3 ^ 40 * 2200650 * 2
def baseEnd_2200650 : Nat := 376663734105640060151467

theorem tailTrace_2200650 : CollatzResearch.WordTrace tailWord_2200650 prefixEnd_2200650 376663734105640060151467 := by
  unfold tailWord_2200650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066074869357091485717851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53509532984952243961914269 20066074869357091485717851)
  ·
    refine ⟨30099112304035637228576777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066074869357091485717851 30099112304035637228576777)
    ·
      refine ⟨22574334228026727921432583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30099112304035637228576777 22574334228026727921432583)
      ·
        refine ⟨33861501342040091882148875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22574334228026727921432583 33861501342040091882148875)
        ·
          refine ⟨50792252013060137823223313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33861501342040091882148875 50792252013060137823223313)
          ·
            refine ⟨38094189009795103367417485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50792252013060137823223313 38094189009795103367417485)
            ·
              refine ⟨14285320878673163762781557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38094189009795103367417485 14285320878673163762781557)
              ·
                refine ⟨1339248832375609102760771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14285320878673163762781557 1339248832375609102760771)
                ·
                  refine ⟨2008873248563413654141157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339248832375609102760771 2008873248563413654141157)
                  ·
                    refine ⟨376663734105640060151467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008873248563413654141157 376663734105640060151467)
                    ·
                      rfl

theorem cell23_2200650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_2200650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200650 prefixEnd_2200650 := by exact prefixLift 2200650
  have htrace : WordTrace (prefixWord ++ tailWord_2200650) baseStart_2200650 baseEnd_2200650 := by
    simpa [prefixWord, tailWord_2200650, baseEnd_2200650] using wordTrace_append hprefix tailTrace_2200650
  have hstable : (prefixWord ++ tailWord_2200650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200650).length < 2 ^ (prefixWord ++ tailWord_2200650).sum := by decide
  have hdescent : baseEnd_2200650 < baseStart_2200650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200653 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2200653 : Nat := 118140960795 + 2200653 * 2 ^ 59
def prefixEnd_2200653 : Nat := 4983230072969 + 3 ^ 40 * 2200653 * 2
def baseEnd_2200653 : Nat := 1129992742758883668716887

theorem tailTrace_2200653 : CollatzResearch.WordTrace tailWord_2200653 prefixEnd_2200653 1129992742758883668716887 := by
  unfold tailWord_2200653
  simp only [CollatzResearch.WordTrace]
  refine ⟨80264408896417497455230613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53509605930944998303487075 80264408896417497455230613)
  ·
    refine ⟨3762394167019570193213935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80264408896417497455230613 3762394167019570193213935)
    ·
      refine ⟨5643591250529355289820903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3762394167019570193213935 5643591250529355289820903)
      ·
        refine ⟨8465386875794032934731355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643591250529355289820903 8465386875794032934731355)
        ·
          refine ⟨12698080313691049402097033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8465386875794032934731355 12698080313691049402097033)
          ·
            refine ⟨9523560235268287051572775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698080313691049402097033 9523560235268287051572775)
            ·
              refine ⟨14285340352902430577359163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9523560235268287051572775 14285340352902430577359163)
              ·
                refine ⟨21428010529353645866038745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14285340352902430577359163 21428010529353645866038745)
                ·
                  refine ⟨16071007897015234399529059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21428010529353645866038745 16071007897015234399529059)
                  ·
                    refine ⟨24106511845522851599293589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16071007897015234399529059 24106511845522851599293589)
                    ·
                      refine ⟨1129992742758883668716887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24106511845522851599293589 1129992742758883668716887)
                      ·
                        rfl

theorem cell23_2200653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2200653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200653 prefixEnd_2200653 := by exact prefixLift 2200653
  have htrace : WordTrace (prefixWord ++ tailWord_2200653) baseStart_2200653 baseEnd_2200653 := by
    simpa [prefixWord, tailWord_2200653, baseEnd_2200653] using wordTrace_append hprefix tailTrace_2200653
  have hstable : (prefixWord ++ tailWord_2200653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200653).length < 2 ^ (prefixWord ++ tailWord_2200653).sum := by decide
  have hdescent : baseEnd_2200653 < baseStart_2200653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200656 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_2200656 : Nat := 118140960795 + 2200656 * 2 ^ 59
def prefixEnd_2200656 : Nat := 4983230072969 + 3 ^ 40 * 2200656 * 2
def baseEnd_2200656 : Nat := 1129994283200847156979373

theorem tailTrace_2200656 : CollatzResearch.WordTrace tailWord_2200656 prefixEnd_2200656 1129994283200847156979373 := by
  unfold tailWord_2200656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40132259157703314483794911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53509678876937752645059881 40132259157703314483794911)
  ·
    refine ⟨60198388736554971725692367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40132259157703314483794911 60198388736554971725692367)
    ·
      refine ⟨90297583104832457588538551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60198388736554971725692367 90297583104832457588538551)
      ·
        refine ⟨135446374657248686382807827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90297583104832457588538551 135446374657248686382807827)
        ·
          refine ⟨203169561985873029574211741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135446374657248686382807827 203169561985873029574211741)
          ·
            refine ⟨76188585744702386090329403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203169561985873029574211741 76188585744702386090329403)
            ·
              refine ⟨114282878617053579135494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76188585744702386090329403 114282878617053579135494105)
              ·
                refine ⟨85712158962790184351620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114282878617053579135494105 85712158962790184351620579)
                ·
                  refine ⟨128568238444185276527430869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85712158962790184351620579 128568238444185276527430869)
                  ·
                    refine ⟨3013318088535592418611661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128568238444185276527430869 3013318088535592418611661)
                    ·
                      refine ⟨1129994283200847156979373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3013318088535592418611661 1129994283200847156979373)
                      ·
                        rfl

theorem cell23_2200656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_2200656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200656 prefixEnd_2200656 := by exact prefixLift 2200656
  have htrace : WordTrace (prefixWord ++ tailWord_2200656) baseStart_2200656 baseEnd_2200656 := by
    simpa [prefixWord, tailWord_2200656, baseEnd_2200656] using wordTrace_append hprefix tailTrace_2200656
  have hstable : (prefixWord ++ tailWord_2200656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200656).length < 2 ^ (prefixWord ++ tailWord_2200656).sum := by decide
  have hdescent : baseEnd_2200656 < baseStart_2200656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200690 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2200690 : Nat := 118140960795 + 2200690 * 2 ^ 59
def prefixEnd_2200690 : Nat := 4983230072969 + 3 ^ 40 * 2200690 * 2
def baseEnd_2200690 : Nat := 1130011741543100023954217

theorem tailTrace_2200690 : CollatzResearch.WordTrace tailWord_2200690 prefixEnd_2200690 1130011741543100023954217 := by
  unfold tailWord_2200690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066439599320863193581881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53510505598188968516218349 20066439599320863193581881)
  ·
    refine ⟨15049829699490647395186411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20066439599320863193581881 15049829699490647395186411)
    ·
      refine ⟨22574744549235971092779617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15049829699490647395186411 22574744549235971092779617)
      ·
        refine ⟨16931058411926978319584713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22574744549235971092779617 16931058411926978319584713)
        ·
          refine ⟨12698293808945233739688535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16931058411926978319584713 12698293808945233739688535)
          ·
            refine ⟨19047440713417850609532803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12698293808945233739688535 19047440713417850609532803)
            ·
              refine ⟨28571161070126775914299205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19047440713417850609532803 28571161070126775914299205)
              ·
                refine ⟨5357092700648770483931101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28571161070126775914299205 5357092700648770483931101)
                ·
                  refine ⟨2008909762743288931474163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5357092700648770483931101 2008909762743288931474163)
                  ·
                    refine ⟨3013364644114933397211245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2008909762743288931474163 3013364644114933397211245)
                    ·
                      refine ⟨1130011741543100023954217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3013364644114933397211245 1130011741543100023954217)
                      ·
                        rfl

theorem cell23_2200690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2200690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200690 prefixEnd_2200690 := by exact prefixLift 2200690
  have htrace : WordTrace (prefixWord ++ tailWord_2200690) baseStart_2200690 baseEnd_2200690 := by
    simpa [prefixWord, tailWord_2200690, baseEnd_2200690] using wordTrace_append hprefix tailTrace_2200690
  have hstable : (prefixWord ++ tailWord_2200690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200690).length < 2 ^ (prefixWord ++ tailWord_2200690).sum := by decide
  have hdescent : baseEnd_2200690 < baseStart_2200690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200700 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_2200700 : Nat := 118140960795 + 2200700 * 2 ^ 59
def prefixEnd_2200700 : Nat := 4983230072969 + 3 ^ 40 * 2200700 * 2
def baseEnd_2200700 : Nat := 1130016876349644984829171

theorem tailTrace_2200700 : CollatzResearch.WordTrace tailWord_2200700 prefixEnd_2200700 1130016876349644984829171 := by
  unfold tailWord_2200700
  simp only [CollatzResearch.WordTrace]
  refine ⟨40133061563623612241095777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53510748751498149654794369 40133061563623612241095777)
  ·
    refine ⟨30099796172717709180821833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40133061563623612241095777 30099796172717709180821833)
    ·
      refine ⟨22574847129538281885616375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30099796172717709180821833 22574847129538281885616375)
      ·
        refine ⟨33862270694307422828424563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22574847129538281885616375 33862270694307422828424563)
        ·
          refine ⟨50793406041461134242636845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33862270694307422828424563 50793406041461134242636845)
          ·
            refine ⟨19047527265547925340988817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50793406041461134242636845 19047527265547925340988817)
            ·
              refine ⟨14285645449160944005741613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19047527265547925340988817 14285645449160944005741613)
              ·
                refine ⟨5357117043435354002153105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14285645449160944005741613 5357117043435354002153105)
                ·
                  refine ⟨4017837782576515501614829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357117043435354002153105 4017837782576515501614829)
                  ·
                    refine ⟨1506689168466193313105561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4017837782576515501614829 1506689168466193313105561)
                    ·
                      refine ⟨1130016876349644984829171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506689168466193313105561 1130016876349644984829171)
                      ·
                        rfl

theorem cell23_2200700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_2200700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200700 prefixEnd_2200700 := by exact prefixLift 2200700
  have htrace : WordTrace (prefixWord ++ tailWord_2200700) baseStart_2200700 baseEnd_2200700 := by
    simpa [prefixWord, tailWord_2200700, baseEnd_2200700] using wordTrace_append hprefix tailTrace_2200700
  have hstable : (prefixWord ++ tailWord_2200700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200700).length < 2 ^ (prefixWord ++ tailWord_2200700).sum := by decide
  have hdescent : baseEnd_2200700 < baseStart_2200700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200723 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 4, 4]
def baseStart_2200723 : Nat := 118140960795 + 2200723 * 2 ^ 59
def prefixEnd_2200723 : Nat := 4983230072969 + 3 ^ 40 * 2200723 * 2
def baseEnd_2200723 : Nat := 376676228801566131613855

theorem tailTrace_2200723 : CollatzResearch.WordTrace tailWord_2200723 prefixEnd_2200723 376676228801566131613855 := by
  unfold tailWord_2200723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80266962006163899410278823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53511308004109266273519215 80266962006163899410278823)
  ·
    refine ⟨120400443009245849115418235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80266962006163899410278823 120400443009245849115418235)
    ·
      refine ⟨180600664513868773673127353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120400443009245849115418235 180600664513868773673127353)
      ·
        refine ⟨135450498385401580254845515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180600664513868773673127353 135450498385401580254845515)
        ·
          refine ⟨203175747578102370382268273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135450498385401580254845515 203175747578102370382268273)
          ·
            refine ⟨152381810683576777786701205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203175747578102370382268273 152381810683576777786701205)
            ·
              refine ⟨7142897375792661458751619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152381810683576777786701205 7142897375792661458751619)
              ·
                refine ⟨10714346063688992188127429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7142897375792661458751619 10714346063688992188127429)
                ·
                  refine ⟨2008939886941686035273893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10714346063688992188127429 2008939886941686035273893)
                  ·
                    refine ⟨376676228801566131613855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008939886941686035273893 376676228801566131613855)
                    ·
                      rfl

theorem cell23_2200723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 4].length) (baseStart_2200723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200723 prefixEnd_2200723 := by exact prefixLift 2200723
  have htrace : WordTrace (prefixWord ++ tailWord_2200723) baseStart_2200723 baseEnd_2200723 := by
    simpa [prefixWord, tailWord_2200723, baseEnd_2200723] using wordTrace_append hprefix tailTrace_2200723
  have hstable : (prefixWord ++ tailWord_2200723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200723).length < 2 ^ (prefixWord ++ tailWord_2200723).sum := by decide
  have hdescent : baseEnd_2200723 < baseStart_2200723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200733 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2200733 : Nat := 118140960795 + 2200733 * 2 ^ 59
def prefixEnd_2200733 : Nat := 4983230072969 + 3 ^ 40 * 2200733 * 2
def baseEnd_2200733 : Nat := 1130033821211243355716519

theorem tailTrace_2200733 : CollatzResearch.WordTrace tailWord_2200733 prefixEnd_2200733 1130033821211243355716519 := by
  unfold tailWord_2200733
  simp only [CollatzResearch.WordTrace]
  refine ⟨80267326736127671118142853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53511551157418447412095235 80267326736127671118142853)
  ·
    refine ⟨15050123763023938334651785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80267326736127671118142853 15050123763023938334651785)
    ·
      refine ⟨11287592822267953750988839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15050123763023938334651785 11287592822267953750988839)
      ·
        refine ⟨16931389233401930626483259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287592822267953750988839 16931389233401930626483259)
        ·
          refine ⟨25397083850102895939724889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16931389233401930626483259 25397083850102895939724889)
          ·
            refine ⟨19047812887577171954793667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25397083850102895939724889 19047812887577171954793667)
            ·
              refine ⟨28571719331365757932190501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19047812887577171954793667 28571719331365757932190501)
              ·
                refine ⟨5357197374631079612285719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28571719331365757932190501 5357197374631079612285719)
                ·
                  refine ⟨8035796061946619418428579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357197374631079612285719 8035796061946619418428579)
                  ·
                    refine ⟨12053694092919929127642869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8035796061946619418428579 12053694092919929127642869)
                    ·
                      refine ⟨1130033821211243355716519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12053694092919929127642869 1130033821211243355716519)
                      ·
                        rfl

theorem cell23_2200733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2200733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200733 prefixEnd_2200733 := by exact prefixLift 2200733
  have htrace : WordTrace (prefixWord ++ tailWord_2200733) baseStart_2200733 baseEnd_2200733 := by
    simpa [prefixWord, tailWord_2200733, baseEnd_2200733] using wordTrace_append hprefix tailTrace_2200733
  have hstable : (prefixWord ++ tailWord_2200733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200733).length < 2 ^ (prefixWord ++ tailWord_2200733).sum := by decide
  have hdescent : baseEnd_2200733 < baseStart_2200733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200753 : List Nat := [1, 2, 2, 5, 1, 1, 2, 9]
def baseStart_2200753 : Nat := 118140960795 + 2200753 * 2 ^ 59
def prefixEnd_2200753 : Nat := 4983230072969 + 3 ^ 40 * 2200753 * 2
def baseEnd_2200753 : Nat := 41853484845345676943201

theorem tailTrace_2200753 : CollatzResearch.WordTrace tailWord_2200753 prefixEnd_2200753 41853484845345676943201 := by
  unfold tailWord_2200753
  simp only [CollatzResearch.WordTrace]
  refine ⟨80268056196055214533870913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53512037464036809689247275 80268056196055214533870913)
  ·
    refine ⟨60201042147041410900403185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80268056196055214533870913 60201042147041410900403185)
    ·
      refine ⟨45150781610281058175302389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60201042147041410900403185 45150781610281058175302389)
      ·
        refine ⟨4232885775963849203934599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45150781610281058175302389 4232885775963849203934599)
        ·
          refine ⟨6349328663945773805901899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232885775963849203934599 6349328663945773805901899)
          ·
            refine ⟨9523992995918660708852849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349328663945773805901899 9523992995918660708852849)
            ·
              refine ⟨7142994746938995531639637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9523992995918660708852849 7142994746938995531639637)
              ·
                refine ⟨41853484845345676943201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7142994746938995531639637 41853484845345676943201)
                ·
                  rfl

theorem cell23_2200753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 9].length) (baseStart_2200753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200753 prefixEnd_2200753 := by exact prefixLift 2200753
  have htrace : WordTrace (prefixWord ++ tailWord_2200753) baseStart_2200753 baseEnd_2200753 := by
    simpa [prefixWord, tailWord_2200753, baseEnd_2200753] using wordTrace_append hprefix tailTrace_2200753
  have hstable : (prefixWord ++ tailWord_2200753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200753).length < 2 ^ (prefixWord ++ tailWord_2200753).sum := by decide
  have hdescent : baseEnd_2200753 < baseStart_2200753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200770 : List Nat := [3, 5, 1, 1, 13]
def baseStart_2200770 : Nat := 118140960795 + 2200770 * 2 ^ 59
def prefixEnd_2200770 : Nat := 4983230072969 + 3 ^ 40 * 2200770 * 2
def baseEnd_2200770 : Nat := 1550141042517777381281

theorem tailTrace_2200770 : CollatzResearch.WordTrace tailWord_2200770 prefixEnd_2200770 1550141042517777381281 := by
  unfold tailWord_2200770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067169059248406609309941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53512450824662417624826509 20067169059248406609309941)
  ·
    refine ⟨1881297099304538119622807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20067169059248406609309941 1881297099304538119622807)
    ·
      refine ⟨2821945648956807179434211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881297099304538119622807 2821945648956807179434211)
      ·
        refine ⟨4232918473435210769151317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821945648956807179434211 4232918473435210769151317)
        ·
          refine ⟨1550141042517777381281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4232918473435210769151317 1550141042517777381281)
          ·
            rfl

theorem cell23_2200770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 13].length) (baseStart_2200770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200770 prefixEnd_2200770 := by exact prefixLift 2200770
  have htrace : WordTrace (prefixWord ++ tailWord_2200770) baseStart_2200770 baseEnd_2200770 := by
    simpa [prefixWord, tailWord_2200770, baseEnd_2200770] using wordTrace_append hprefix tailTrace_2200770
  have hstable : (prefixWord ++ tailWord_2200770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200770).length < 2 ^ (prefixWord ++ tailWord_2200770).sum := by decide
  have hdescent : baseEnd_2200770 < baseStart_2200770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_2200823 : Nat := 118140960795 + 2200823 * 2 ^ 59
def prefixEnd_2200823 : Nat := 4983230072969 + 3 ^ 40 * 2200823 * 2
def baseEnd_2200823 : Nat := 1130080034470148003591105

theorem tailTrace_2200823 : CollatzResearch.WordTrace tailWord_2200823 prefixEnd_2200823 1130080034470148003591105 := by
  unfold tailWord_2200823
  simp only [CollatzResearch.WordTrace]
  refine ⟨80270609305801616488919123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53513739537201077659279415 80270609305801616488919123)
  ·
    refine ⟨120405913958702424733378685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80270609305801616488919123 120405913958702424733378685)
    ·
      refine ⟨45152217734513409275017007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120405913958702424733378685 45152217734513409275017007)
      ·
        refine ⟨67728326601770113912525511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45152217734513409275017007 67728326601770113912525511)
        ·
          refine ⟨101592489902655170868788267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67728326601770113912525511 101592489902655170868788267)
          ·
            refine ⟨152388734853982756303182401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101592489902655170868788267 152388734853982756303182401)
            ·
              refine ⟨114291551140487067227386801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152388734853982756303182401 114291551140487067227386801)
              ·
                refine ⟨85718663355365300420540101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114291551140487067227386801 85718663355365300420540101)
                ·
                  refine ⟨16072249379130993828851269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85718663355365300420540101 16072249379130993828851269)
                  ·
                    refine ⟨3013546758587061342909613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16072249379130993828851269 3013546758587061342909613)
                    ·
                      refine ⟨1130080034470148003591105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3013546758587061342909613 1130080034470148003591105)
                      ·
                        rfl

theorem cell23_2200823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_2200823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200823 prefixEnd_2200823 := by exact prefixLift 2200823
  have htrace : WordTrace (prefixWord ++ tailWord_2200823) baseStart_2200823 baseEnd_2200823 := by
    simpa [prefixWord, tailWord_2200823, baseEnd_2200823] using wordTrace_append hprefix tailTrace_2200823
  have hstable : (prefixWord ++ tailWord_2200823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200823).length < 2 ^ (prefixWord ++ tailWord_2200823).sum := by decide
  have hdescent : baseEnd_2200823 < baseStart_2200823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200830 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2200830 : Nat := 118140960795 + 2200830 * 2 ^ 59
def prefixEnd_2200830 : Nat := 4983230072969 + 3 ^ 40 * 2200830 * 2
def baseEnd_2200830 : Nat := 376694542944909825401191

theorem tailTrace_2200830 : CollatzResearch.WordTrace tailWord_2200830 prefixEnd_2200830 376694542944909825401191 := by
  unfold tailWord_2200830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033858077097032085552993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53513909744517504456282629 10033858077097032085552993)
  ·
    refine ⟨7525393557822774064164745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10033858077097032085552993 7525393557822774064164745)
    ·
      refine ⟨5644045168367080548123559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7525393557822774064164745 5644045168367080548123559)
      ·
        refine ⟨8466067752550620822185339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644045168367080548123559 8466067752550620822185339)
        ·
          refine ⟨12699101628825931233278009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466067752550620822185339 12699101628825931233278009)
          ·
            refine ⟨9524326221619448424958507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12699101628825931233278009 9524326221619448424958507)
            ·
              refine ⟨14286489332429172637437761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9524326221619448424958507 14286489332429172637437761)
              ·
                refine ⟨10714866999321879478078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14286489332429172637437761 10714866999321879478078321)
                ·
                  refine ⟨8036150249491409608558741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10714866999321879478078321 8036150249491409608558741)
                  ·
                    refine ⟨376694542944909825401191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8036150249491409608558741 376694542944909825401191)
                    ·
                      rfl

theorem cell23_2200830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2200830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200830 prefixEnd_2200830 := by exact prefixLift 2200830
  have htrace : WordTrace (prefixWord ++ tailWord_2200830) baseStart_2200830 baseEnd_2200830 := by
    simpa [prefixWord, tailWord_2200830, baseEnd_2200830] using wordTrace_append hprefix tailTrace_2200830
  have hstable : (prefixWord ++ tailWord_2200830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200830).length < 2 ^ (prefixWord ++ tailWord_2200830).sum := by decide
  have hdescent : baseEnd_2200830 < baseStart_2200830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200837 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_2200837 : Nat := 118140960795 + 2200837 * 2 ^ 59
def prefixEnd_2200837 : Nat := 4983230072969 + 3 ^ 40 * 2200837 * 2
def baseEnd_2200837 : Nat := 1130087223199310948816041

theorem tailTrace_2200837 : CollatzResearch.WordTrace tailWord_2200837 prefixEnd_2200837 1130087223199310948816041 := by
  unfold tailWord_2200837
  simp only [CollatzResearch.WordTrace]
  refine ⟨80271119927750896879928765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53514079951833931253285843 80271119927750896879928765)
  ·
    refine ⟨30101669972906586329973287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80271119927750896879928765 30101669972906586329973287)
    ·
      refine ⟨45152504959359879494959931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30101669972906586329973287 45152504959359879494959931)
      ·
        refine ⟨67728757439039819242439897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45152504959359879494959931 67728757439039819242439897)
        ·
          refine ⟨50796568079279864431829923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67728757439039819242439897 50796568079279864431829923)
          ·
            refine ⟨76194852118919796647744885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50796568079279864431829923 76194852118919796647744885)
            ·
              refine ⟨7143267386148730935726083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76194852118919796647744885 7143267386148730935726083)
              ·
                refine ⟨10714901079223096403589125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7143267386148730935726083 10714901079223096403589125)
                ·
                  refine ⟨2009043952354330575672961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10714901079223096403589125 2009043952354330575672961)
                  ·
                    refine ⟨1506782964265747931754721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2009043952354330575672961 1506782964265747931754721)
                    ·
                      refine ⟨1130087223199310948816041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506782964265747931754721 1130087223199310948816041)
                      ·
                        rfl

theorem cell23_2200837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_2200837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200837 prefixEnd_2200837 := by exact prefixLift 2200837
  have htrace : WordTrace (prefixWord ++ tailWord_2200837) baseStart_2200837 baseEnd_2200837 := by
    simpa [prefixWord, tailWord_2200837, baseEnd_2200837] using wordTrace_append hprefix tailTrace_2200837
  have hstable : (prefixWord ++ tailWord_2200837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200837).length < 2 ^ (prefixWord ++ tailWord_2200837).sum := by decide
  have hdescent : baseEnd_2200837 < baseStart_2200837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200843 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 7]
def baseStart_2200843 : Nat := 118140960795 + 2200843 * 2 ^ 59
def prefixEnd_2200843 : Nat := 4983230072969 + 3 ^ 40 * 2200843 * 2
def baseEnd_2200843 : Nat := 125565589342581991704557

theorem tailTrace_2200843 : CollatzResearch.WordTrace tailWord_2200843 prefixEnd_2200843 125565589342581991704557 := by
  unfold tailWord_2200843
  simp only [CollatzResearch.WordTrace]
  refine ⟨80271338765729159904647183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53514225843819439936431455 80271338765729159904647183)
  ·
    refine ⟨120407008148593739856970775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80271338765729159904647183 120407008148593739856970775)
    ·
      refine ⟨180610512222890609785456163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120407008148593739856970775 180610512222890609785456163)
      ·
        refine ⟨270915768334335914678184245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180610512222890609785456163 270915768334335914678184245)
        ·
          refine ⟨25398353281343992001079773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270915768334335914678184245 25398353281343992001079773)
          ·
            refine ⟨9524382480503997000404915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25398353281343992001079773 9524382480503997000404915)
            ·
              refine ⟨14286573720755995500607373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9524382480503997000404915 14286573720755995500607373)
              ·
                refine ⟨5357465145283498312727765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14286573720755995500607373 5357465145283498312727765)
                ·
                  refine ⟨125565589342581991704557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5357465145283498312727765 125565589342581991704557)
                  ·
                    rfl

theorem cell23_2200843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 7].length) (baseStart_2200843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200843 prefixEnd_2200843 := by exact prefixLift 2200843
  have htrace : WordTrace (prefixWord ++ tailWord_2200843) baseStart_2200843 baseEnd_2200843 := by
    simpa [prefixWord, tailWord_2200843, baseEnd_2200843] using wordTrace_append hprefix tailTrace_2200843
  have hstable : (prefixWord ++ tailWord_2200843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200843).length < 2 ^ (prefixWord ++ tailWord_2200843).sum := by decide
  have hdescent : baseEnd_2200843 < baseStart_2200843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200890 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_2200890 : Nat := 118140960795 + 2200890 * 2 ^ 59
def prefixEnd_2200890 : Nat := 4983230072969 + 3 ^ 40 * 2200890 * 2
def baseEnd_2200890 : Nat := 376704812557999747151099

theorem tailTrace_2200890 : CollatzResearch.WordTrace tailWord_2200890 prefixEnd_2200890 376704812557999747151099 := by
  unfold tailWord_2200890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20068263249139721732902031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53515368664372591287738749 20068263249139721732902031)
  ·
    refine ⟨30102394873709582599353047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20068263249139721732902031 30102394873709582599353047)
    ·
      refine ⟨45153592310564373899029571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30102394873709582599353047 45153592310564373899029571)
      ·
        refine ⟨67730388465846560848544357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45153592310564373899029571 67730388465846560848544357)
        ·
          refine ⟨12699447837346230159102067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67730388465846560848544357 12699447837346230159102067)
          ·
            refine ⟨19049171756019345238653101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12699447837346230159102067 19049171756019345238653101)
            ·
              refine ⟨7143439408507254464494913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19049171756019345238653101 7143439408507254464494913)
              ·
                refine ⟨5357579556380440848371185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143439408507254464494913 5357579556380440848371185)
                ·
                  refine ⟨4018184667285330636278389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357579556380440848371185 4018184667285330636278389)
                  ·
                    refine ⟨376704812557999747151099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4018184667285330636278389 376704812557999747151099)
                    ·
                      rfl

theorem cell23_2200890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_2200890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200890 prefixEnd_2200890 := by exact prefixLift 2200890
  have htrace : WordTrace (prefixWord ++ tailWord_2200890) baseStart_2200890 baseEnd_2200890 := by
    simpa [prefixWord, tailWord_2200890, baseEnd_2200890] using wordTrace_append hprefix tailTrace_2200890
  have hstable : (prefixWord ++ tailWord_2200890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200890).length < 2 ^ (prefixWord ++ tailWord_2200890).sum := by decide
  have hdescent : baseEnd_2200890 < baseStart_2200890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200894 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2200894 : Nat := 118140960795 + 2200894 * 2 ^ 59
def prefixEnd_2200894 : Nat := 4983230072969 + 3 ^ 40 * 2200894 * 2
def baseEnd_2200894 : Nat := 125568499066290802867031

theorem tailTrace_2200894 : CollatzResearch.WordTrace tailWord_2200894 prefixEnd_2200894 125568499066290802867031 := by
  unfold tailWord_2200894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034149861068049451844217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53515465925696263743169157 10034149861068049451844217)
  ·
    refine ⟨7525612395801037088883163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10034149861068049451844217 7525612395801037088883163)
    ·
      refine ⟨11288418593701555633324745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525612395801037088883163 11288418593701555633324745)
      ·
        refine ⟨8466313945276166724993559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11288418593701555633324745 8466313945276166724993559)
        ·
          refine ⟨12699470917914250087490339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466313945276166724993559 12699470917914250087490339)
          ·
            refine ⟨19049206376871375131235509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12699470917914250087490339 19049206376871375131235509)
            ·
              refine ⟨1785863097831691418553329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19049206376871375131235509 1785863097831691418553329)
              ·
                refine ⟨1339397323373768563914997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785863097831691418553329 1339397323373768563914997)
                ·
                  refine ⟨125568499066290802867031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1339397323373768563914997 125568499066290802867031)
                  ·
                    rfl

theorem cell23_2200894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2200894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200894 prefixEnd_2200894 := by exact prefixLift 2200894
  have htrace : WordTrace (prefixWord ++ tailWord_2200894) baseStart_2200894 baseEnd_2200894 := by
    simpa [prefixWord, tailWord_2200894, baseEnd_2200894] using wordTrace_append hprefix tailTrace_2200894
  have hstable : (prefixWord ++ tailWord_2200894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200894).length < 2 ^ (prefixWord ++ tailWord_2200894).sum := by decide
  have hdescent : baseEnd_2200894 < baseStart_2200894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200910 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2200910 : Nat := 118140960795 + 2200910 * 2 ^ 59
def prefixEnd_2200910 : Nat := 4983230072969 + 3 ^ 40 * 2200910 * 2
def baseEnd_2200910 : Nat := 1130124707287089163203205

theorem tailTrace_2200910 : CollatzResearch.WordTrace tailWord_2200910 prefixEnd_2200910 1130124707287089163203205 := by
  unfold tailWord_2200910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034222807060803793417023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53515854970990953564890789 10034222807060803793417023)
  ·
    refine ⟨15051334210591205690125535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10034222807060803793417023 15051334210591205690125535)
    ·
      refine ⟨22577001315886808535188303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15051334210591205690125535 22577001315886808535188303)
      ·
        refine ⟨33865501973830212802782455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22577001315886808535188303 33865501973830212802782455)
        ·
          refine ⟨50798252960745319204173683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33865501973830212802782455 50798252960745319204173683)
          ·
            refine ⟨76197379441117978806260525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50798252960745319204173683 76197379441117978806260525)
            ·
              refine ⟨28574017290419242052347697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76197379441117978806260525 28574017290419242052347697)
              ·
                refine ⟨21430512967814431539260773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28574017290419242052347697 21430512967814431539260773)
                ·
                  refine ⟨4018221181465205913611395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21430512967814431539260773 4018221181465205913611395)
                  ·
                    refine ⟨6027331772197808870417093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018221181465205913611395 6027331772197808870417093)
                    ·
                      refine ⟨1130124707287089163203205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6027331772197808870417093 1130124707287089163203205)
                      ·
                        rfl

theorem cell23_2200910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2200910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200910 prefixEnd_2200910 := by exact prefixLift 2200910
  have htrace : WordTrace (prefixWord ++ tailWord_2200910) baseStart_2200910 baseEnd_2200910 := by
    simpa [prefixWord, tailWord_2200910, baseEnd_2200910] using wordTrace_append hprefix tailTrace_2200910
  have hstable : (prefixWord ++ tailWord_2200910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200910).length < 2 ^ (prefixWord ++ tailWord_2200910).sum := by decide
  have hdescent : baseEnd_2200910 < baseStart_2200910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200920 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_2200920 : Nat := 118140960795 + 2200920 * 2 ^ 59
def prefixEnd_2200920 : Nat := 4983230072969 + 3 ^ 40 * 2200920 * 2
def baseEnd_2200920 : Nat := 376709947364544708026053

theorem tailTrace_2200920 : CollatzResearch.WordTrace tailWord_2200920 prefixEnd_2200920 376709947364544708026053 := by
  unfold tailWord_2200920
  simp only [CollatzResearch.WordTrace]
  refine ⟨40137073593225101027600107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53516098124300134703466809 40137073593225101027600107)
  ·
    refine ⟨60205610389837651541400161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40137073593225101027600107 60205610389837651541400161)
    ·
      refine ⟨45154207792378238656050121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60205610389837651541400161 45154207792378238656050121)
      ·
        refine ⟨33865655844283678992037591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45154207792378238656050121 33865655844283678992037591)
        ·
          refine ⟨50798483766425518488056387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33865655844283678992037591 50798483766425518488056387)
          ·
            refine ⟨76197725649638277732084581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50798483766425518488056387 76197725649638277732084581)
            ·
              refine ⟨14287073559307177074765859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76197725649638277732084581 14287073559307177074765859)
              ·
                refine ⟨21430610338960765612148789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14287073559307177074765859 21430610338960765612148789)
                ·
                  refine ⟨2009119719277571776138949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21430610338960765612148789 2009119719277571776138949)
                  ·
                    refine ⟨376709947364544708026053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009119719277571776138949 376709947364544708026053)
                    ·
                      rfl

theorem cell23_2200920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_2200920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200920 prefixEnd_2200920 := by exact prefixLift 2200920
  have htrace : WordTrace (prefixWord ++ tailWord_2200920) baseStart_2200920 baseEnd_2200920 := by
    simpa [prefixWord, tailWord_2200920, baseEnd_2200920] using wordTrace_append hprefix tailTrace_2200920
  have hstable : (prefixWord ++ tailWord_2200920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200920).length < 2 ^ (prefixWord ++ tailWord_2200920).sum := by decide
  have hdescent : baseEnd_2200920 < baseStart_2200920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200977 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_2200977 : Nat := 118140960795 + 2200977 * 2 ^ 59
def prefixEnd_2200977 : Nat := 4983230072969 + 3 ^ 40 * 2200977 * 2
def baseEnd_2200977 : Nat := 1130159110490940401065397

theorem tailTrace_2200977 : CollatzResearch.WordTrace tailWord_2200977 prefixEnd_2200977 1130159110490940401065397 := by
  unfold tailWord_2200977
  simp only [CollatzResearch.WordTrace]
  refine ⟨80276226147243700790025185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53517484098162467193350123 80276226147243700790025185)
  ·
    refine ⟨60207169610432775592518889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80276226147243700790025185 60207169610432775592518889)
    ·
      refine ⟨45155377207824581694389167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60207169610432775592518889 45155377207824581694389167)
      ·
        refine ⟨67733065811736872541583751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45155377207824581694389167 67733065811736872541583751)
        ·
          refine ⟨101599598717605308812375627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67733065811736872541583751 101599598717605308812375627)
          ·
            refine ⟨152399398076407963218563441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101599598717605308812375627 152399398076407963218563441)
            ·
              refine ⟨114299548557305972413922581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152399398076407963218563441 114299548557305972413922581)
              ·
                refine ⟨5357791338623717456902621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114299548557305972413922581 5357791338623717456902621)
                ·
                  refine ⟨2009171751983894046338483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5357791338623717456902621 2009171751983894046338483)
                  ·
                    refine ⟨3013757627975841069507725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009171751983894046338483 3013757627975841069507725)
                    ·
                      refine ⟨1130159110490940401065397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3013757627975841069507725 1130159110490940401065397)
                      ·
                        rfl

theorem cell23_2200977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_2200977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200977 prefixEnd_2200977 := by exact prefixLift 2200977
  have htrace : WordTrace (prefixWord ++ tailWord_2200977) baseStart_2200977 baseEnd_2200977 := by
    simpa [prefixWord, tailWord_2200977, baseEnd_2200977] using wordTrace_append hprefix tailTrace_2200977
  have hstable : (prefixWord ++ tailWord_2200977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200977).length < 2 ^ (prefixWord ++ tailWord_2200977).sum := by decide
  have hdescent : baseEnd_2200977 < baseStart_2200977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200978 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2200978 : Nat := 118140960795 + 2200978 * 2 ^ 59
def prefixEnd_2200978 : Nat := 4983230072969 + 3 ^ 40 * 2200978 * 2
def baseEnd_2200978 : Nat := 1130159623971594897152893

theorem tailTrace_2200978 : CollatzResearch.WordTrace tailWord_2200978 prefixEnd_2200978 1130159623971594897152893 := by
  unfold tailWord_2200978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20069065655060019490202897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53517508413493385307207725 20069065655060019490202897)
  ·
    refine ⟨15051799241295014617652173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20069065655060019490202897 15051799241295014617652173)
    ·
      refine ⟨5644424715485630481619565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15051799241295014617652173 5644424715485630481619565)
      ·
        refine ⟨2116659268307111430607337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5644424715485630481619565 2116659268307111430607337)
        ·
          refine ⟨1587494451230333572955503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2116659268307111430607337 1587494451230333572955503)
          ·
            refine ⟨2381241676845500359433255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587494451230333572955503 2381241676845500359433255)
            ·
              refine ⟨3571862515268250539149883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381241676845500359433255 3571862515268250539149883)
              ·
                refine ⟨5357793772902375808724825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571862515268250539149883 5357793772902375808724825)
                ·
                  refine ⟨4018345329676781856543619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357793772902375808724825 4018345329676781856543619)
                  ·
                    refine ⟨6027517994515172784815429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018345329676781856543619 6027517994515172784815429)
                    ·
                      refine ⟨1130159623971594897152893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6027517994515172784815429 1130159623971594897152893)
                      ·
                        rfl

theorem cell23_2200978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2200978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200978 prefixEnd_2200978 := by exact prefixLift 2200978
  have htrace : WordTrace (prefixWord ++ tailWord_2200978) baseStart_2200978 baseEnd_2200978 := by
    simpa [prefixWord, tailWord_2200978, baseEnd_2200978] using wordTrace_append hprefix tailTrace_2200978
  have hstable : (prefixWord ++ tailWord_2200978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200978).length < 2 ^ (prefixWord ++ tailWord_2200978).sum := by decide
  have hdescent : baseEnd_2200978 < baseStart_2200978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200988 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_2200988 : Nat := 118140960795 + 2200988 * 2 ^ 59
def prefixEnd_2200988 : Nat := 4983230072969 + 3 ^ 40 * 2200988 * 2
def baseEnd_2200988 : Nat := 376721586259379952675949

theorem tailTrace_2200988 : CollatzResearch.WordTrace tailWord_2200988 prefixEnd_2200988 376721586259379952675949 := by
  unfold tailWord_2200988
  simp only [CollatzResearch.WordTrace]
  refine ⟨40138313675101924834337809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53517751566802566445783745 40138313675101924834337809)
  ·
    refine ⟨30103735256326443625753357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40138313675101924834337809 30103735256326443625753357)
    ·
      refine ⟨11288900721122416359657509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30103735256326443625753357 11288900721122416359657509)
      ·
        refine ⟨2116668885210453067435783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11288900721122416359657509 2116668885210453067435783)
        ·
          refine ⟨3175003327815679601153675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116668885210453067435783 3175003327815679601153675)
          ·
            refine ⟨4762504991723519401730513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175003327815679601153675 4762504991723519401730513)
            ·
              refine ⟨3571878743792639551297885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762504991723519401730513 3571878743792639551297885)
              ·
                refine ⟨1339454528922239831736707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3571878743792639551297885 1339454528922239831736707)
                ·
                  refine ⟨2009181793383359747605061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339454528922239831736707 2009181793383359747605061)
                  ·
                    refine ⟨376721586259379952675949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009181793383359747605061 376721586259379952675949)
                    ·
                      rfl

theorem cell23_2200988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_2200988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200988 prefixEnd_2200988 := by exact prefixLift 2200988
  have htrace : WordTrace (prefixWord ++ tailWord_2200988) baseStart_2200988 baseEnd_2200988 := by
    simpa [prefixWord, tailWord_2200988, baseEnd_2200988] using wordTrace_append hprefix tailTrace_2200988
  have hstable : (prefixWord ++ tailWord_2200988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200988).length < 2 ^ (prefixWord ++ tailWord_2200988).sum := by decide
  have hdescent : baseEnd_2200988 < baseStart_2200988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201027 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 2, 4]
def baseStart_2201027 : Nat := 118140960795 + 2201027 * 2 ^ 59
def prefixEnd_2201027 : Nat := 4983230072969 + 3 ^ 40 * 2201027 * 2
def baseEnd_2201027 : Nat := 376728261507888401813389

theorem tailTrace_2201027 : CollatzResearch.WordTrace tailWord_2201027 prefixEnd_2201027 376728261507888401813389 := by
  unfold tailWord_2201027
  simp only [CollatzResearch.WordTrace]
  refine ⟨80278049797062559329345335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53518699864708372886230223 80278049797062559329345335)
  ·
    refine ⟨120417074695593838994018003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80278049797062559329345335 120417074695593838994018003)
    ·
      refine ⟨180625612043390758491027005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120417074695593838994018003 180625612043390758491027005)
      ·
        refine ⟨67734604516271534434135127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180625612043390758491027005 67734604516271534434135127)
        ·
          refine ⟨101601906774407301651202691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67734604516271534434135127 101601906774407301651202691)
          ·
            refine ⟨152402860161610952476804037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101601906774407301651202691 152402860161610952476804037)
            ·
              refine ⟨28575536280302053589400757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152402860161610952476804037 28575536280302053589400757)
              ·
                refine ⟨2678956526278317524006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28575536280302053589400757 2678956526278317524006321)
                ·
                  refine ⟨2009217394708738143004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678956526278317524006321 2009217394708738143004741)
                  ·
                    refine ⟨376728261507888401813389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009217394708738143004741 376728261507888401813389)
                    ·
                      rfl

theorem cell23_2201027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 4].length) (baseStart_2201027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201027 prefixEnd_2201027 := by exact prefixLift 2201027
  have htrace : WordTrace (prefixWord ++ tailWord_2201027) baseStart_2201027 baseEnd_2201027 := by
    simpa [prefixWord, tailWord_2201027, baseEnd_2201027] using wordTrace_append hprefix tailTrace_2201027
  have hstable : (prefixWord ++ tailWord_2201027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201027).length < 2 ^ (prefixWord ++ tailWord_2201027).sum := by decide
  have hdescent : baseEnd_2201027 < baseStart_2201027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201034 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_2201034 : Nat := 118140960795 + 2201034 * 2 ^ 59
def prefixEnd_2201034 : Nat := 4983230072969 + 3 ^ 40 * 2201034 * 2
def baseEnd_2201034 : Nat := 1130188378888246678052635

theorem tailTrace_2201034 : CollatzResearch.WordTrace tailWord_2201034 prefixEnd_2201034 1130188378888246678052635 := by
  unfold tailWord_2201034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20069576277009299881212539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53518870072024799683233437 20069576277009299881212539)
  ·
    refine ⟨30104364415513949821818809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20069576277009299881212539 30104364415513949821818809)
    ·
      refine ⟨22578273311635462366364107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30104364415513949821818809 22578273311635462366364107)
      ·
        refine ⟨33867409967453193549546161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22578273311635462366364107 33867409967453193549546161)
        ·
          refine ⟨25400557475589895162159621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33867409967453193549546161 25400557475589895162159621)
          ·
            refine ⟨4762604526673105342904929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25400557475589895162159621 4762604526673105342904929)
            ·
              refine ⟨3571953395004829007178697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762604526673105342904929 3571953395004829007178697)
              ·
                refine ⟨2678965046253621755384023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571953395004829007178697 2678965046253621755384023)
                ·
                  refine ⟨4018447569380432633076035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678965046253621755384023 4018447569380432633076035)
                  ·
                    refine ⟨6027671354070648949614053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018447569380432633076035 6027671354070648949614053)
                    ·
                      refine ⟨1130188378888246678052635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6027671354070648949614053 1130188378888246678052635)
                      ·
                        rfl

theorem cell23_2201034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_2201034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201034 prefixEnd_2201034 := by exact prefixLift 2201034
  have htrace : WordTrace (prefixWord ++ tailWord_2201034) baseStart_2201034 baseEnd_2201034 := by
    simpa [prefixWord, tailWord_2201034, baseEnd_2201034] using wordTrace_append hprefix tailTrace_2201034
  have hstable : (prefixWord ++ tailWord_2201034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201034).length < 2 ^ (prefixWord ++ tailWord_2201034).sum := by decide
  have hdescent : baseEnd_2201034 < baseStart_2201034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201078 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2201078 : Nat := 118140960795 + 2201078 * 2 ^ 59
def prefixEnd_2201078 : Nat := 4983230072969 + 3 ^ 40 * 2201078 * 2
def baseEnd_2201078 : Nat := 376736990679014835300811

theorem tailTrace_2201078 : CollatzResearch.WordTrace tailWord_2201078 prefixEnd_2201078 376736990679014835300811 := by
  unfold tailWord_2201078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017494369992362189965743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53519939946585196692967925 5017494369992362189965743)
  ·
    refine ⟨7526241554988543284948615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017494369992362189965743 7526241554988543284948615)
    ·
      refine ⟨11289362332482814927422923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7526241554988543284948615 11289362332482814927422923)
      ·
        refine ⟨16934043498724222391134385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11289362332482814927422923 16934043498724222391134385)
        ·
          refine ⟨12700532624043166793350789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16934043498724222391134385 12700532624043166793350789)
          ·
            refine ⟨2381349867008093773753273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12700532624043166793350789 2381349867008093773753273)
            ·
              refine ⟨1786012400256070330314955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381349867008093773753273 1786012400256070330314955)
              ·
                refine ⟨2679018600384105495472433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786012400256070330314955 2679018600384105495472433)
                ·
                  refine ⟨2009263950288079121604325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679018600384105495472433 2009263950288079121604325)
                  ·
                    refine ⟨376736990679014835300811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009263950288079121604325 376736990679014835300811)
                    ·
                      rfl

theorem cell23_2201078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2201078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201078 prefixEnd_2201078 := by exact prefixLift 2201078
  have htrace : WordTrace (prefixWord ++ tailWord_2201078) baseStart_2201078 baseEnd_2201078 := by
    simpa [prefixWord, tailWord_2201078, baseEnd_2201078] using wordTrace_append hprefix tailTrace_2201078
  have hstable : (prefixWord ++ tailWord_2201078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201078).length < 2 ^ (prefixWord ++ tailWord_2201078).sum := by decide
  have hdescent : baseEnd_2201078 < baseStart_2201078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201117 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2201117 : Nat := 118140960795 + 2201117 * 2 ^ 59
def prefixEnd_2201117 : Nat := 4983230072969 + 3 ^ 40 * 2201117 * 2
def baseEnd_2201117 : Nat := 376743665927523284438251

theorem tailTrace_2201117 : CollatzResearch.WordTrace tailWord_2201117 prefixEnd_2201117 376743665927523284438251 := by
  unfold tailWord_2201117
  simp only [CollatzResearch.WordTrace]
  refine ⟨80281332366736504700121605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53520888244491003133414403 80281332366736504700121605)
  ·
    refine ⟨15052749818763094631272801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80281332366736504700121605 15052749818763094631272801)
    ·
      refine ⟨11289562364072320973454601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15052749818763094631272801 11289562364072320973454601)
      ·
        refine ⟨8467171773054240730090951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11289562364072320973454601 8467171773054240730090951)
        ·
          refine ⟨12700757659581361095136427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467171773054240730090951 12700757659581361095136427)
          ·
            refine ⟨19051136489372041642704641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700757659581361095136427 19051136489372041642704641)
            ·
              refine ⟨14288352367029031232028481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19051136489372041642704641 14288352367029031232028481)
              ·
                refine ⟨10716264275271773424021361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14288352367029031232028481 10716264275271773424021361)
                ·
                  refine ⟨8037198206453830068016021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10716264275271773424021361 8037198206453830068016021)
                  ·
                    refine ⟨376743665927523284438251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8037198206453830068016021 376743665927523284438251)
                    ·
                      rfl

theorem cell23_2201117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2201117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201117 prefixEnd_2201117 := by exact prefixLift 2201117
  have htrace : WordTrace (prefixWord ++ tailWord_2201117) baseStart_2201117 baseEnd_2201117 := by
    simpa [prefixWord, tailWord_2201117, baseEnd_2201117] using wordTrace_append hprefix tailTrace_2201117
  have hstable : (prefixWord ++ tailWord_2201117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201117).length < 2 ^ (prefixWord ++ tailWord_2201117).sum := by decide
  have hdescent : baseEnd_2201117 < baseStart_2201117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201134 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2201134 : Nat := 118140960795 + 2201134 * 2 ^ 59
def prefixEnd_2201134 : Nat := 4983230072969 + 3 ^ 40 * 2201134 * 2
def baseEnd_2201134 : Nat := 376746575651232095600725

theorem tailTrace_2201134 : CollatzResearch.WordTrace tailWord_2201134 prefixEnd_2201134 376746575651232095600725 := by
  unfold tailWord_2201134
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035244050959364575436307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53521301605116611068993637 10035244050959364575436307)
  ·
    refine ⟨15052866076439046863154461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10035244050959364575436307 15052866076439046863154461)
    ·
      refine ⟨5644824778664642573682923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15052866076439046863154461 5644824778664642573682923)
      ·
        refine ⟨8467237167996963860524385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644824778664642573682923 8467237167996963860524385)
        ·
          refine ⟨6350427875997722895393289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8467237167996963860524385 6350427875997722895393289)
          ·
            refine ⟨4762820906998292171544967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6350427875997722895393289 4762820906998292171544967)
            ·
              refine ⟨7144231360497438257317451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762820906998292171544967 7144231360497438257317451)
              ·
                refine ⟨10716347040746157385976177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144231360497438257317451 10716347040746157385976177)
                ·
                  refine ⟨8037260280559618039482133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10716347040746157385976177 8037260280559618039482133)
                  ·
                    refine ⟨376746575651232095600725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8037260280559618039482133 376746575651232095600725)
                    ·
                      rfl

theorem cell23_2201134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2201134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201134 prefixEnd_2201134 := by exact prefixLift 2201134
  have htrace : WordTrace (prefixWord ++ tailWord_2201134) baseStart_2201134 baseEnd_2201134 := by
    simpa [prefixWord, tailWord_2201134, baseEnd_2201134] using wordTrace_append hprefix tailTrace_2201134
  have hstable : (prefixWord ++ tailWord_2201134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201134).length < 2 ^ (prefixWord ++ tailWord_2201134).sum := by decide
  have hdescent : baseEnd_2201134 < baseStart_2201134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201141 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_2201141 : Nat := 118140960795 + 2201141 * 2 ^ 59
def prefixEnd_2201141 : Nat := 4983230072969 + 3 ^ 40 * 2201141 * 2
def baseEnd_2201141 : Nat := 1130243321318277759414643

theorem tailTrace_2201141 : CollatzResearch.WordTrace tailWord_2201141 prefixEnd_2201141 1130243321318277759414643 := by
  unfold tailWord_2201141
  simp only [CollatzResearch.WordTrace]
  refine ⟨80282207718649556798995277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53521471812433037865996851 80282207718649556798995277)
  ·
    refine ⟨30105827894493583799623229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80282207718649556798995277 30105827894493583799623229)
    ·
      refine ⟨11289685460435093924858711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30105827894493583799623229 11289685460435093924858711)
      ·
        refine ⟨16934528190652640887288067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11289685460435093924858711 16934528190652640887288067)
        ·
          refine ⟨25401792285978961330932101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16934528190652640887288067 25401792285978961330932101)
          ·
            refine ⟨4762836053621055249549769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25401792285978961330932101 4762836053621055249549769)
            ·
              refine ⟨3572127040215791437162327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762836053621055249549769 3572127040215791437162327)
              ·
                refine ⟨5358190560323687155743491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572127040215791437162327 5358190560323687155743491)
                ·
                  refine ⟨8037285840485530733615237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358190560323687155743491 8037285840485530733615237)
                  ·
                    refine ⟨1506991095091037012552857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8037285840485530733615237 1506991095091037012552857)
                    ·
                      refine ⟨1130243321318277759414643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506991095091037012552857 1130243321318277759414643)
                      ·
                        rfl

theorem cell23_2201141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_2201141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201141 prefixEnd_2201141 := by exact prefixLift 2201141
  have htrace : WordTrace (prefixWord ++ tailWord_2201141) baseStart_2201141 baseEnd_2201141 := by
    simpa [prefixWord, tailWord_2201141, baseEnd_2201141] using wordTrace_append hprefix tailTrace_2201141
  have hstable : (prefixWord ++ tailWord_2201141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201141).length < 2 ^ (prefixWord ++ tailWord_2201141).sum := by decide
  have hdescent : baseEnd_2201141 < baseStart_2201141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201157 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_2201157 : Nat := 118140960795 + 2201157 * 2 ^ 59
def prefixEnd_2201157 : Nat := 4983230072969 + 3 ^ 40 * 2201157 * 2
def baseEnd_2201157 : Nat := 1130251537008749696814569

theorem tailTrace_2201157 : CollatzResearch.WordTrace tailWord_2201157 prefixEnd_2201157 1130251537008749696814569 := by
  unfold tailWord_2201157
  simp only [CollatzResearch.WordTrace]
  refine ⟨80282791286591591531577725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53521860857727727687718483 80282791286591591531577725)
  ·
    refine ⟨30106046732471846824341647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80282791286591591531577725 30106046732471846824341647)
    ·
      refine ⟨45159070098707770236512471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30106046732471846824341647 45159070098707770236512471)
      ·
        refine ⟨67738605148061655354768707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45159070098707770236512471 67738605148061655354768707)
        ·
          refine ⟨101607907722092483032153061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67738605148061655354768707 101607907722092483032153061)
          ·
            refine ⟨19051482697892340568528699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101607907722092483032153061 19051482697892340568528699)
            ·
              refine ⟨28577224046838510852793049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19051482697892340568528699 28577224046838510852793049)
              ·
                refine ⟨21432918035128883139594787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28577224046838510852793049 21432918035128883139594787)
                ·
                  refine ⟨32149377052693324709392181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21432918035128883139594787 32149377052693324709392181)
                  ·
                    refine ⟨3014004098689999191505517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32149377052693324709392181 3014004098689999191505517)
                    ·
                      refine ⟨1130251537008749696814569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014004098689999191505517 1130251537008749696814569)
                      ·
                        rfl

theorem cell23_2201157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_2201157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201157 prefixEnd_2201157 := by exact prefixLift 2201157
  have htrace : WordTrace (prefixWord ++ tailWord_2201157) baseStart_2201157 baseEnd_2201157 := by
    simpa [prefixWord, tailWord_2201157, baseEnd_2201157] using wordTrace_append hprefix tailTrace_2201157
  have hstable : (prefixWord ++ tailWord_2201157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201157).length < 2 ^ (prefixWord ++ tailWord_2201157).sum := by decide
  have hdescent : baseEnd_2201157 < baseStart_2201157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201164 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 5]
def baseStart_2201164 : Nat := 118140960795 + 2201164 * 2 ^ 59
def prefixEnd_2201164 : Nat := 4983230072969 + 3 ^ 40 * 2201164 * 2
def baseEnd_2201164 : Nat := 125583903485925685491893

theorem tailTrace_2201164 : CollatzResearch.WordTrace tailWord_2201164 prefixEnd_2201164 125583903485925685491893 := by
  unfold tailWord_2201164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40141523298783115863541273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53522031065044154484721697 40141523298783115863541273)
  ·
    refine ⟨30106142474087336897655955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40141523298783115863541273 30106142474087336897655955)
    ·
      refine ⟨45159213711131005346483933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30106142474087336897655955 45159213711131005346483933)
      ·
        refine ⟨16934705141674127004931475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45159213711131005346483933 16934705141674127004931475)
        ·
          refine ⟨25402057712511190507397213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16934705141674127004931475 25402057712511190507397213)
          ·
            refine ⟨9525771642191696440273955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25402057712511190507397213 9525771642191696440273955)
            ·
              refine ⟨14288657463287544660410933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525771642191696440273955 14288657463287544660410933)
              ·
                refine ⟨1339561637183207311913525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14288657463287544660410933 1339561637183207311913525)
                ·
                  refine ⟨125583903485925685491893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1339561637183207311913525 125583903485925685491893)
                  ·
                    rfl

theorem cell23_2201164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_2201164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201164 prefixEnd_2201164 := by exact prefixLift 2201164
  have htrace : WordTrace (prefixWord ++ tailWord_2201164) baseStart_2201164 baseEnd_2201164 := by
    simpa [prefixWord, tailWord_2201164, baseEnd_2201164] using wordTrace_append hprefix tailTrace_2201164
  have hstable : (prefixWord ++ tailWord_2201164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201164).length < 2 ^ (prefixWord ++ tailWord_2201164).sum := by decide
  have hdescent : baseEnd_2201164 < baseStart_2201164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201177 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_2201177 : Nat := 118140960795 + 2201177 * 2 ^ 59
def prefixEnd_2201177 : Nat := 4983230072969 + 3 ^ 40 * 2201177 * 2
def baseEnd_2201177 : Nat := 376753935540613206188159

theorem tailTrace_2201177 : CollatzResearch.WordTrace tailWord_2201177 prefixEnd_2201177 376753935540613206188159 := by
  unfold tailWord_2201177
  simp only [CollatzResearch.WordTrace]
  refine ⟨80283520746519134947305785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53522347164346089964870523 80283520746519134947305785)
  ·
    refine ⟨60212640559889351210479339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80283520746519134947305785 60212640559889351210479339)
    ·
      refine ⟨90318960839834026815719009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60212640559889351210479339 90318960839834026815719009)
      ·
        refine ⟨67739220629875520111789257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90318960839834026815719009 67739220629875520111789257)
        ·
          refine ⟨50804415472406640083841943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67739220629875520111789257 50804415472406640083841943)
          ·
            refine ⟨76206623208609960125762915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50804415472406640083841943 76206623208609960125762915)
            ·
              refine ⟨114309934812914940188644373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76206623208609960125762915 114309934812914940188644373)
              ·
                refine ⟨5358278194355387821342705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114309934812914940188644373 5358278194355387821342705)
                ·
                  refine ⟨4018708645766540866007029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5358278194355387821342705 4018708645766540866007029)
                  ·
                    refine ⟨376753935540613206188159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4018708645766540866007029 376753935540613206188159)
                    ·
                      rfl

theorem cell23_2201177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_2201177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201177 prefixEnd_2201177 := by exact prefixLift 2201177
  have htrace : WordTrace (prefixWord ++ tailWord_2201177) baseStart_2201177 baseEnd_2201177 := by
    simpa [prefixWord, tailWord_2201177, baseEnd_2201177] using wordTrace_append hprefix tailTrace_2201177
  have hstable : (prefixWord ++ tailWord_2201177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201177).length < 2 ^ (prefixWord ++ tailWord_2201177).sum := by decide
  have hdescent : baseEnd_2201177 < baseStart_2201177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201292 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_2201292 : Nat := 118140960795 + 2201292 * 2 ^ 59
def prefixEnd_2201292 : Nat := 4983230072969 + 3 ^ 40 * 2201292 * 2
def baseEnd_2201292 : Nat := 376773618965702222875483

theorem tailTrace_2201292 : CollatzResearch.WordTrace tailWord_2201292 prefixEnd_2201292 376773618965702222875483 := by
  unfold tailWord_2201292
  simp only [CollatzResearch.WordTrace]
  refine ⟨40143857570551254793871065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53525143427401673058494753 40143857570551254793871065)
  ·
    refine ⟨30107893177913441095403299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40143857570551254793871065 30107893177913441095403299)
    ·
      refine ⟨45161839766870161643104949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30107893177913441095403299 45161839766870161643104949)
      ·
        refine ⟨4233922478144077654041089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45161839766870161643104949 4233922478144077654041089)
        ·
          refine ⟨3175441858608058240530817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4233922478144077654041089 3175441858608058240530817)
          ·
            refine ⟨2381581393956043680398113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3175441858608058240530817 2381581393956043680398113)
            ·
              refine ⟨1786186045467032760298585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381581393956043680398113 1786186045467032760298585)
              ·
                refine ⟨1339639534100274570223939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786186045467032760298585 1339639534100274570223939)
                ·
                  refine ⟨2009459301150411855335909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339639534100274570223939 2009459301150411855335909)
                  ·
                    refine ⟨376773618965702222875483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009459301150411855335909 376773618965702222875483)
                    ·
                      rfl

theorem cell23_2201292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_2201292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201292 prefixEnd_2201292 := by exact prefixLift 2201292
  have htrace : WordTrace (prefixWord ++ tailWord_2201292) baseStart_2201292 baseEnd_2201292 := by
    simpa [prefixWord, tailWord_2201292, baseEnd_2201292] using wordTrace_append hprefix tailTrace_2201292
  have hstable : (prefixWord ++ tailWord_2201292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201292).length < 2 ^ (prefixWord ++ tailWord_2201292).sum := by decide
  have hdescent : baseEnd_2201292 < baseStart_2201292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201304 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2201304 : Nat := 118140960795 + 2201304 * 2 ^ 59
def prefixEnd_2201304 : Nat := 4983230072969 + 3 ^ 40 * 2201304 * 2
def baseEnd_2201304 : Nat := 1130327018664960621676393

theorem tailTrace_2201304 : CollatzResearch.WordTrace tailWord_2201304 prefixEnd_2201304 1130327018664960621676393 := by
  unfold tailWord_2201304
  simp only [CollatzResearch.WordTrace]
  refine ⟨40144076408529517818589483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53525435211372690424785977 40144076408529517818589483)
  ·
    refine ⟨60216114612794276727884225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40144076408529517818589483 60216114612794276727884225)
    ·
      refine ⟨45162085959595707545913169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60216114612794276727884225 45162085959595707545913169)
      ·
        refine ⟨33871564469696780659434877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45162085959595707545913169 33871564469696780659434877)
        ·
          refine ⟨12701836676136292747288079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33871564469696780659434877 12701836676136292747288079)
          ·
            refine ⟨19052755014204439120932119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12701836676136292747288079 19052755014204439120932119)
            ·
              refine ⟨28579132521306658681398179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19052755014204439120932119 28579132521306658681398179)
              ·
                refine ⟨42868698781959988022097269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28579132521306658681398179 42868698781959988022097269)
                ·
                  refine ⟨4018940510808748877071619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42868698781959988022097269 4018940510808748877071619)
                  ·
                    refine ⟨6028410766213123315607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018940510808748877071619 6028410766213123315607429)
                    ·
                      refine ⟨1130327018664960621676393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6028410766213123315607429 1130327018664960621676393)
                      ·
                        rfl

theorem cell23_2201304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2201304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201304 prefixEnd_2201304 := by exact prefixLift 2201304
  have htrace : WordTrace (prefixWord ++ tailWord_2201304) baseStart_2201304 baseEnd_2201304 := by
    simpa [prefixWord, tailWord_2201304, baseEnd_2201304] using wordTrace_append hprefix tailTrace_2201304
  have hstable : (prefixWord ++ tailWord_2201304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201304).length < 2 ^ (prefixWord ++ tailWord_2201304).sum := by decide
  have hdescent : baseEnd_2201304 < baseStart_2201304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201325 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2201325 : Nat := 118140960795 + 2201325 * 2 ^ 59
def prefixEnd_2201325 : Nat := 4983230072969 + 3 ^ 40 * 2201325 * 2
def baseEnd_2201325 : Nat := 1130337801758705039513797

theorem tailTrace_2201325 : CollatzResearch.WordTrace tailWord_2201325 prefixEnd_2201325 1130337801758705039513797 := by
  unfold tailWord_2201325
  simp only [CollatzResearch.WordTrace]
  refine ⟨80288918749982956223693429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53525945833321970815795619 80288918749982956223693429)
  ·
    refine ⟨7527086132810902145971259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80288918749982956223693429 7527086132810902145971259)
    ·
      refine ⟨11290629199216353218956889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7527086132810902145971259 11290629199216353218956889)
      ·
        refine ⟨8467971899412264914217667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11290629199216353218956889 8467971899412264914217667)
        ·
          refine ⟨12701957849118397371326501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467971899412264914217667 12701957849118397371326501)
          ·
            refine ⟨2381617096709699507123719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12701957849118397371326501 2381617096709699507123719)
            ·
              refine ⟨3572425645064549260685579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381617096709699507123719 3572425645064549260685579)
              ·
                refine ⟨5358638467596823891028369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572425645064549260685579 5358638467596823891028369)
                ·
                  refine ⟨4018978850697617918271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5358638467596823891028369 4018978850697617918271277)
                  ·
                    refine ⟨1507117069011606719351729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4018978850697617918271277 1507117069011606719351729)
                    ·
                      refine ⟨1130337801758705039513797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507117069011606719351729 1130337801758705039513797)
                      ·
                        rfl

theorem cell23_2201325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2201325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201325 prefixEnd_2201325 := by exact prefixLift 2201325
  have htrace : WordTrace (prefixWord ++ tailWord_2201325) baseStart_2201325 baseEnd_2201325 := by
    simpa [prefixWord, tailWord_2201325, baseEnd_2201325] using wordTrace_append hprefix tailTrace_2201325
  have hstable : (prefixWord ++ tailWord_2201325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201325).length < 2 ^ (prefixWord ++ tailWord_2201325).sum := by decide
  have hdescent : baseEnd_2201325 < baseStart_2201325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201348 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_2201348 : Nat := 118140960795 + 2201348 * 2 ^ 59
def prefixEnd_2201348 : Nat := 4983230072969 + 3 ^ 40 * 2201348 * 2
def baseEnd_2201348 : Nat := 376783203937919483175397

theorem tailTrace_2201348 : CollatzResearch.WordTrace tailWord_2201348 prefixEnd_2201348 376783203937919483175397 := by
  unfold tailWord_2201348
  simp only [CollatzResearch.WordTrace]
  refine ⟨40144878814449815575890349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53526505085933087434520465 40144878814449815575890349)
  ·
    refine ⟨15054329555418680840958881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40144878814449815575890349 15054329555418680840958881)
    ·
      refine ⟨11290747166564010630719161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15054329555418680840958881 11290747166564010630719161)
      ·
        refine ⟨8468060374923007973039371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11290747166564010630719161 8468060374923007973039371)
        ·
          refine ⟨12702090562384511959559057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8468060374923007973039371 12702090562384511959559057)
          ·
            refine ⟨9526567921788383969669293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12702090562384511959559057 9526567921788383969669293)
            ·
              refine ⟨3572462970670643988625985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9526567921788383969669293 3572462970670643988625985)
              ·
                refine ⟨2679347228002982991469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572462970670643988625985 2679347228002982991469489)
                ·
                  refine ⟨2009510421002237243602117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679347228002982991469489 2009510421002237243602117)
                  ·
                    refine ⟨376783203937919483175397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009510421002237243602117 376783203937919483175397)
                    ·
                      rfl

theorem cell23_2201348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_2201348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201348 prefixEnd_2201348 := by exact prefixLift 2201348
  have htrace : WordTrace (prefixWord ++ tailWord_2201348) baseStart_2201348 baseEnd_2201348 := by
    simpa [prefixWord, tailWord_2201348, baseEnd_2201348] using wordTrace_append hprefix tailTrace_2201348
  have hstable : (prefixWord ++ tailWord_2201348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201348).length < 2 ^ (prefixWord ++ tailWord_2201348).sum := by decide
  have hdescent : baseEnd_2201348 < baseStart_2201348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201355 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 1, 2, 2]
def baseStart_2201355 : Nat := 118140960795 + 2201355 * 2 ^ 59
def prefixEnd_2201355 : Nat := 4983230072969 + 3 ^ 40 * 2201355 * 2
def baseEnd_2201355 : Nat := 1130353206178339922138659

theorem tailTrace_2201355 : CollatzResearch.WordTrace tailWord_2201355 prefixEnd_2201355 1130353206178339922138659 := by
  unfold tailWord_2201355
  simp only [CollatzResearch.WordTrace]
  refine ⟨80290012939874271347285519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53526675293249514231523679 80290012939874271347285519)
  ·
    refine ⟨120435019409811407020928279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80290012939874271347285519 120435019409811407020928279)
    ·
      refine ⟨180652529114717110531392419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120435019409811407020928279 180652529114717110531392419)
      ·
        refine ⟨270978793672075665797088629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180652529114717110531392419 270978793672075665797088629)
        ·
          refine ⟨25404261906757093668477059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270978793672075665797088629 25404261906757093668477059)
          ·
            refine ⟨38106392860135640502715589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25404261906757093668477059 38106392860135640502715589)
            ·
              refine ⟨7144948661275432594259173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38106392860135640502715589 7144948661275432594259173)
              ·
                refine ⟨1339677873989143611423595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7144948661275432594259173 1339677873989143611423595)
                ·
                  refine ⟨2009516810983715417135393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339677873989143611423595 2009516810983715417135393)
                  ·
                    refine ⟨1507137608237786562851545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2009516810983715417135393 1507137608237786562851545)
                    ·
                      refine ⟨1130353206178339922138659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507137608237786562851545 1130353206178339922138659)
                      ·
                        rfl

theorem cell23_2201355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 2, 2].length) (baseStart_2201355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201355 prefixEnd_2201355 := by exact prefixLift 2201355
  have htrace : WordTrace (prefixWord ++ tailWord_2201355) baseStart_2201355 baseEnd_2201355 := by
    simpa [prefixWord, tailWord_2201355, baseEnd_2201355] using wordTrace_append hprefix tailTrace_2201355
  have hstable : (prefixWord ++ tailWord_2201355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201355).length < 2 ^ (prefixWord ++ tailWord_2201355).sum := by decide
  have hdescent : baseEnd_2201355 < baseStart_2201355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201404 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_2201404 : Nat := 118140960795 + 2201404 * 2 ^ 59
def prefixEnd_2201404 : Nat := 4983230072969 + 3 ^ 40 * 2201404 * 2
def baseEnd_2201404 : Nat := 376792788910136743475311

theorem tailTrace_2201404 : CollatzResearch.WordTrace tailWord_2201404 prefixEnd_2201404 376792788910136743475311 := by
  unfold tailWord_2201404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145900058348376357909633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53527866744464501810546177 40145900058348376357909633)
  ·
    refine ⟨30109425043761282268432225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40145900058348376357909633 30109425043761282268432225)
    ·
      refine ⟨22582068782820961701324169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30109425043761282268432225 22582068782820961701324169)
      ·
        refine ⟨16936551587115721275993127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22582068782820961701324169 16936551587115721275993127)
        ·
          refine ⟨25404827380673581913989691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16936551587115721275993127 25404827380673581913989691)
          ·
            refine ⟨38107241071010372870984537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25404827380673581913989691 38107241071010372870984537)
            ·
              refine ⟨28580430803257779653238403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38107241071010372870984537 28580430803257779653238403)
              ·
                refine ⟨42870646204886669479857605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28580430803257779653238403 42870646204886669479857605)
                ·
                  refine ⟨8038246163416250527473301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42870646204886669479857605 8038246163416250527473301)
                  ·
                    refine ⟨376792788910136743475311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8038246163416250527473301 376792788910136743475311)
                    ·
                      rfl

theorem cell23_2201404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_2201404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201404 prefixEnd_2201404 := by exact prefixLift 2201404
  have htrace : WordTrace (prefixWord ++ tailWord_2201404) baseStart_2201404 baseEnd_2201404 := by
    simpa [prefixWord, tailWord_2201404, baseEnd_2201404] using wordTrace_append hprefix tailTrace_2201404
  have hstable : (prefixWord ++ tailWord_2201404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201404).length < 2 ^ (prefixWord ++ tailWord_2201404).sum := by decide
  have hdescent : baseEnd_2201404 < baseStart_2201404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201424 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2201424 : Nat := 118140960795 + 2201424 * 2 ^ 59
def prefixEnd_2201424 : Nat := 4983230072969 + 3 ^ 40 * 2201424 * 2
def baseEnd_2201424 : Nat := 1130388636343500152175841

theorem tailTrace_2201424 : CollatzResearch.WordTrace tailWord_2201424 prefixEnd_2201424 1130388636343500152175841 := by
  unfold tailWord_2201424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40146264788312148065773663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53528353051082864087698217 40146264788312148065773663)
  ·
    refine ⟨60219397182468222098660495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40146264788312148065773663 60219397182468222098660495)
    ·
      refine ⟨90329095773702333147990743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60219397182468222098660495 90329095773702333147990743)
      ·
        refine ⟨135493643660553499721986115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90329095773702333147990743 135493643660553499721986115)
        ·
          refine ⟨203240465490830249582979173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135493643660553499721986115 203240465490830249582979173)
          ·
            refine ⟨38107587279530671796808595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203240465490830249582979173 38107587279530671796808595)
            ·
              refine ⟨57161380919296007695212893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38107587279530671796808595 57161380919296007695212893)
              ·
                refine ⟨21435517844736002885704835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57161380919296007695212893 21435517844736002885704835)
                ·
                  refine ⟨32153276767104004328557253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21435517844736002885704835 32153276767104004328557253)
                  ·
                    refine ⟨6028739393832000811604485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32153276767104004328557253 6028739393832000811604485)
                    ·
                      refine ⟨1130388636343500152175841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6028739393832000811604485 1130388636343500152175841)
                      ·
                        rfl

theorem cell23_2201424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2201424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201424 prefixEnd_2201424 := by exact prefixLift 2201424
  have htrace : WordTrace (prefixWord ++ tailWord_2201424) baseStart_2201424 baseEnd_2201424 := by
    simpa [prefixWord, tailWord_2201424, baseEnd_2201424] using wordTrace_append hprefix tailTrace_2201424
  have hstable : (prefixWord ++ tailWord_2201424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201424).length < 2 ^ (prefixWord ++ tailWord_2201424).sum := by decide
  have hdescent : baseEnd_2201424 < baseStart_2201424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201434 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_2201434 : Nat := 118140960795 + 2201434 * 2 ^ 59
def prefixEnd_2201434 : Nat := 4983230072969 + 3 ^ 40 * 2201434 * 2
def baseEnd_2201434 : Nat := 125599307905560568116755

theorem tailTrace_2201434 : CollatzResearch.WordTrace tailWord_2201434 prefixEnd_2201434 125599307905560568116755 := by
  unfold tailWord_2201434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20073223576647016959852839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53528596204392045226274237 20073223576647016959852839)
  ·
    refine ⟨30109835364970525439779259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20073223576647016959852839 30109835364970525439779259)
    ·
      refine ⟨45164753047455788159668889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30109835364970525439779259 45164753047455788159668889)
      ·
        refine ⟨33873564785591841119751667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45164753047455788159668889 33873564785591841119751667)
        ·
          refine ⟨50810347178387761679627501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33873564785591841119751667 50810347178387761679627501)
          ·
            refine ⟨19053880191895410629860313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50810347178387761679627501 19053880191895410629860313)
            ·
              refine ⟨14290410143921557972395235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19053880191895410629860313 14290410143921557972395235)
              ·
                refine ⟨21435615215882336958592853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14290410143921557972395235 21435615215882336958592853)
                ·
                  refine ⟨125599307905560568116755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21435615215882336958592853 125599307905560568116755)
                  ·
                    rfl

theorem cell23_2201434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_2201434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201434 prefixEnd_2201434 := by exact prefixLift 2201434
  have htrace : WordTrace (prefixWord ++ tailWord_2201434) baseStart_2201434 baseEnd_2201434 := by
    simpa [prefixWord, tailWord_2201434, baseEnd_2201434] using wordTrace_append hprefix tailTrace_2201434
  have hstable : (prefixWord ++ tailWord_2201434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201434).length < 2 ^ (prefixWord ++ tailWord_2201434).sum := by decide
  have hdescent : baseEnd_2201434 < baseStart_2201434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201451 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 5]
def baseStart_2201451 : Nat := 118140960795 + 2201451 * 2 ^ 59
def prefixEnd_2201451 : Nat := 4983230072969 + 3 ^ 40 * 2201451 * 2
def baseEnd_2201451 : Nat := 125600277813463505170913

theorem tailTrace_2201451 : CollatzResearch.WordTrace tailWord_2201451 prefixEnd_2201451 125600277813463505170913 := by
  unfold tailWord_2201451
  simp only [CollatzResearch.WordTrace]
  refine ⟨80293514347526479742780207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53529009565017653161853471 80293514347526479742780207)
  ·
    refine ⟨120440271521289719614170311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80293514347526479742780207 120440271521289719614170311)
    ·
      refine ⟨180660407281934579421255467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120440271521289719614170311 180660407281934579421255467)
      ·
        refine ⟨270990610922901869131883201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180660407281934579421255467 270990610922901869131883201)
        ·
          refine ⟨203242958192176401848912401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270990610922901869131883201 203242958192176401848912401)
          ·
            refine ⟨152432218644132301386684301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203242958192176401848912401 152432218644132301386684301)
            ·
              refine ⟨57162081991549613020006613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152432218644132301386684301 57162081991549613020006613)
              ·
                refine ⟨1339736296676944055156405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57162081991549613020006613 1339736296676944055156405)
                ·
                  refine ⟨125600277813463505170913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1339736296676944055156405 125600277813463505170913)
                  ·
                    rfl

theorem cell23_2201451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 5].length) (baseStart_2201451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201451 prefixEnd_2201451 := by exact prefixLift 2201451
  have htrace : WordTrace (prefixWord ++ tailWord_2201451) baseStart_2201451 baseEnd_2201451 := by
    simpa [prefixWord, tailWord_2201451, baseEnd_2201451] using wordTrace_append hprefix tailTrace_2201451
  have hstable : (prefixWord ++ tailWord_2201451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201451).length < 2 ^ (prefixWord ++ tailWord_2201451).sum := by decide
  have hdescent : baseEnd_2201451 < baseStart_2201451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201498 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_2201498 : Nat := 118140960795 + 2201498 * 2 ^ 59
def prefixEnd_2201498 : Nat := 4983230072969 + 3 ^ 40 * 2201498 * 2
def baseEnd_2201498 : Nat := 376808877970644287550167

theorem tailTrace_2201498 : CollatzResearch.WordTrace tailWord_2201498 prefixEnd_2201498 376808877970644287550167 := by
  unfold tailWord_2201498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20073807144589051692435287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53530152385570804513160765 20073807144589051692435287)
  ·
    refine ⟨30110710716883577538652931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20073807144589051692435287 30110710716883577538652931)
    ·
      refine ⟨45166066075325366307979397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30110710716883577538652931 45166066075325366307979397)
      ·
        refine ⟨8468637389123506182746137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45166066075325366307979397 8468637389123506182746137)
        ·
          refine ⟨6351478041842629637059603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8468637389123506182746137 6351478041842629637059603)
          ·
            refine ⟨9527217062763944455589405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6351478041842629637059603 9527217062763944455589405)
            ·
              refine ⟨3572706398536479170846027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9527217062763944455589405 3572706398536479170846027)
              ·
                refine ⟨5359059597804718756269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572706398536479170846027 5359059597804718756269041)
                ·
                  refine ⟨4019294698353539067201781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359059597804718756269041 4019294698353539067201781)
                  ·
                    refine ⟨376808877970644287550167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019294698353539067201781 376808877970644287550167)
                    ·
                      rfl

theorem cell23_2201498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_2201498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201498 prefixEnd_2201498 := by exact prefixLift 2201498
  have htrace : WordTrace (prefixWord ++ tailWord_2201498) baseStart_2201498 baseEnd_2201498 := by
    simpa [prefixWord, tailWord_2201498, baseEnd_2201498] using wordTrace_append hprefix tailTrace_2201498
  have hstable : (prefixWord ++ tailWord_2201498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201498).length < 2 ^ (prefixWord ++ tailWord_2201498).sum := by decide
  have hdescent : baseEnd_2201498 < baseStart_2201498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201528 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_2201528 : Nat := 118140960795 + 2201528 * 2 ^ 59
def prefixEnd_2201528 : Nat := 4983230072969 + 3 ^ 40 * 2201528 * 2
def baseEnd_2201528 : Nat := 376814012777189248425121

theorem tailTrace_2201528 : CollatzResearch.WordTrace tailWord_2201528 prefixEnd_2201528 376814012777189248425121 := by
  unfold tailWord_2201528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40148161384123760946666619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53530881845498347928888825 40148161384123760946666619)
  ·
    refine ⟨60222242076185641419999929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40148161384123760946666619 60222242076185641419999929)
    ·
      refine ⟨45166681557139231064999947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60222242076185641419999929 45166681557139231064999947)
      ·
        refine ⟨67750022335708846597499921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45166681557139231064999947 67750022335708846597499921)
        ·
          refine ⟨50812516751781634948124941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67750022335708846597499921 50812516751781634948124941)
          ·
            refine ⟨19054693781918113105546853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50812516751781634948124941 19054693781918113105546853)
            ·
              refine ⟨3572755084109646207290035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19054693781918113105546853 3572755084109646207290035)
              ·
                refine ⟨5359132626164469310935053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572755084109646207290035 5359132626164469310935053)
                ·
                  refine ⟨2009674734811675991600645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5359132626164469310935053 2009674734811675991600645)
                  ·
                    refine ⟨376814012777189248425121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009674734811675991600645 376814012777189248425121)
                    ·
                      rfl

theorem cell23_2201528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_2201528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201528 prefixEnd_2201528 := by exact prefixLift 2201528
  have htrace : WordTrace (prefixWord ++ tailWord_2201528) baseStart_2201528 baseEnd_2201528 := by
    simpa [prefixWord, tailWord_2201528, baseEnd_2201528] using wordTrace_append hprefix tailTrace_2201528
  have hstable : (prefixWord ++ tailWord_2201528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201528).length < 2 ^ (prefixWord ++ tailWord_2201528).sum := by decide
  have hdescent : baseEnd_2201528 < baseStart_2201528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201551 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_2201551 : Nat := 118140960795 + 2201551 * 2 ^ 59
def prefixEnd_2201551 : Nat := 4983230072969 + 3 ^ 40 * 2201551 * 2
def baseEnd_2201551 : Nat := 1130453848386621155287757

theorem tailTrace_2201551 : CollatzResearch.WordTrace tailWord_2201551 prefixEnd_2201551 1130453848386621155287757 := by
  unfold tailWord_2201551
  simp only [CollatzResearch.WordTrace]
  refine ⟨80297161647164196821420507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53531441098109464547613671 80297161647164196821420507)
  ·
    refine ⟨120445742470746295232130761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80297161647164196821420507 120445742470746295232130761)
    ·
      refine ⟨90334306853059721424098071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120445742470746295232130761 90334306853059721424098071)
      ·
        refine ⟨135501460279589582136147107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90334306853059721424098071 135501460279589582136147107)
        ·
          refine ⟨203252190419384373204220661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135501460279589582136147107 203252190419384373204220661)
          ·
            refine ⟨19054892851817284987895687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203252190419384373204220661 19054892851817284987895687)
            ·
              refine ⟨28582339277725927481843531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19054892851817284987895687 28582339277725927481843531)
              ·
                refine ⟨42873508916588891222765297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28582339277725927481843531 42873508916588891222765297)
                ·
                  refine ⟨32155131687441668417073973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42873508916588891222765297 32155131687441668417073973)
                  ·
                    refine ⟨3014543595697656414100685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32155131687441668417073973 3014543595697656414100685)
                    ·
                      refine ⟨1130453848386621155287757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014543595697656414100685 1130453848386621155287757)
                      ·
                        rfl

theorem cell23_2201551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_2201551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201551 prefixEnd_2201551 := by exact prefixLift 2201551
  have htrace : WordTrace (prefixWord ++ tailWord_2201551) baseStart_2201551 baseEnd_2201551 := by
    simpa [prefixWord, tailWord_2201551, baseEnd_2201551] using wordTrace_append hprefix tailTrace_2201551
  have hstable : (prefixWord ++ tailWord_2201551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201551).length < 2 ^ (prefixWord ++ tailWord_2201551).sum := by decide
  have hdescent : baseEnd_2201551 < baseStart_2201551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201568 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2201568 : Nat := 118140960795 + 2201568 * 2 ^ 59
def prefixEnd_2201568 : Nat := 4983230072969 + 3 ^ 40 * 2201568 * 2
def baseEnd_2201568 : Nat := 1130462577557747588775179

theorem tailTrace_2201568 : CollatzResearch.WordTrace tailWord_2201568 prefixEnd_2201568 1130462577557747588775179 := by
  unfold tailWord_2201568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40148890844051304362394679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53531854458735072483192905 40148890844051304362394679)
  ·
    refine ⟨60223336266076956543592019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40148890844051304362394679 60223336266076956543592019)
    ·
      refine ⟨90335004399115434815388029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60223336266076956543592019 90335004399115434815388029)
      ·
        refine ⟨33875626649668288055770511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90335004399115434815388029 33875626649668288055770511)
        ·
          refine ⟨50813439974502432083655767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33875626649668288055770511 50813439974502432083655767)
          ·
            refine ⟨76220159961753648125483651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50813439974502432083655767 76220159961753648125483651)
            ·
              refine ⟨114330239942630472188225477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76220159961753648125483651 114330239942630472188225477)
              ·
                refine ⟨21436919989243213535292277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114330239942630472188225477 21436919989243213535292277)
                ·
                  refine ⟨2009711248991551268933651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21436919989243213535292277 2009711248991551268933651)
                  ·
                    refine ⟨3014566873487326903400477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009711248991551268933651 3014566873487326903400477)
                    ·
                      refine ⟨1130462577557747588775179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014566873487326903400477 1130462577557747588775179)
                      ·
                        rfl

theorem cell23_2201568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2201568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201568 prefixEnd_2201568 := by exact prefixLift 2201568
  have htrace : WordTrace (prefixWord ++ tailWord_2201568) baseStart_2201568 baseEnd_2201568 := by
    simpa [prefixWord, tailWord_2201568, baseEnd_2201568] using wordTrace_append hprefix tailTrace_2201568
  have hstable : (prefixWord ++ tailWord_2201568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201568).length < 2 ^ (prefixWord ++ tailWord_2201568).sum := by decide
  have hdescent : baseEnd_2201568 < baseStart_2201568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201605 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_2201605 : Nat := 118140960795 + 2201605 * 2 ^ 59
def prefixEnd_2201605 : Nat := 4983230072969 + 3 ^ 40 * 2201605 * 2
def baseEnd_2201605 : Nat := 376827192113987981337503

theorem tailTrace_2201605 : CollatzResearch.WordTrace tailWord_2201605 prefixEnd_2201605 376827192113987981337503 := by
  unfold tailWord_2201605
  simp only [CollatzResearch.WordTrace]
  refine ⟨80299131188968564043886269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53532754125979042695924179 80299131188968564043886269)
  ·
    refine ⟨30112174195863211516457351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80299131188968564043886269 30112174195863211516457351)
    ·
      refine ⟨45168261293794817274686027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30112174195863211516457351 45168261293794817274686027)
      ·
        refine ⟨67752391940692225912029041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45168261293794817274686027 67752391940692225912029041)
        ·
          refine ⟨50814293955519169434021781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67752391940692225912029041 50814293955519169434021781)
          ·
            refine ⟨2381920029164961067219771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50814293955519169434021781 2381920029164961067219771)
            ·
              refine ⟨3572880043747441600829657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381920029164961067219771 3572880043747441600829657)
              ·
                refine ⟨2679660032810581200622243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572880043747441600829657 2679660032810581200622243)
                ·
                  refine ⟨4019490049215871800933365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2679660032810581200622243 4019490049215871800933365)
                  ·
                    refine ⟨376827192113987981337503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019490049215871800933365 376827192113987981337503)
                    ·
                      rfl

theorem cell23_2201605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_2201605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201605 prefixEnd_2201605 := by exact prefixLift 2201605
  have htrace : WordTrace (prefixWord ++ tailWord_2201605) baseStart_2201605 baseEnd_2201605 := by
    simpa [prefixWord, tailWord_2201605, baseEnd_2201605] using wordTrace_append hprefix tailTrace_2201605
  have hstable : (prefixWord ++ tailWord_2201605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201605).length < 2 ^ (prefixWord ++ tailWord_2201605).sum := by decide
  have hdescent : baseEnd_2201605 < baseStart_2201605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201608 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2201608 : Nat := 118140960795 + 2201608 * 2 ^ 59
def prefixEnd_2201608 : Nat := 4983230072969 + 3 ^ 40 * 2201608 * 2
def baseEnd_2201608 : Nat := 1130483116783927432274995

theorem tailTrace_2201608 : CollatzResearch.WordTrace tailWord_2201608 prefixEnd_2201608 1130483116783927432274995 := by
  unfold tailWord_2201608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40149620303978847778122739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53532827071971797037496985 40149620303978847778122739)
  ·
    refine ⟨60224430455968271667184109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40149620303978847778122739 60224430455968271667184109)
    ·
      refine ⟨22584161420988101875194041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60224430455968271667184109 22584161420988101875194041)
      ·
        refine ⟨16938121065741076406395531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22584161420988101875194041 16938121065741076406395531)
        ·
          refine ⟨25407181598611614609593297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16938121065741076406395531 25407181598611614609593297)
          ·
            refine ⟨19055386198958710957194973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25407181598611614609593297 19055386198958710957194973)
            ·
              refine ⟨7145769824609516608948115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19055386198958710957194973 7145769824609516608948115)
              ·
                refine ⟨10718654736914274913422173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145769824609516608948115 10718654736914274913422173)
                ·
                  refine ⟨4019495526342853092533315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10718654736914274913422173 4019495526342853092533315)
                  ·
                    refine ⟨6029243289514279638799973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4019495526342853092533315 6029243289514279638799973)
                    ·
                      refine ⟨1130483116783927432274995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6029243289514279638799973 1130483116783927432274995)
                      ·
                        rfl

theorem cell23_2201608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2201608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201608 prefixEnd_2201608 := by exact prefixLift 2201608
  have htrace : WordTrace (prefixWord ++ tailWord_2201608) baseStart_2201608 baseEnd_2201608 := by
    simpa [prefixWord, tailWord_2201608, baseEnd_2201608] using wordTrace_append hprefix tailTrace_2201608
  have hstable : (prefixWord ++ tailWord_2201608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201608).length < 2 ^ (prefixWord ++ tailWord_2201608).sum := by decide
  have hdescent : baseEnd_2201608 < baseStart_2201608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201635 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 2, 4]
def baseStart_2201635 : Nat := 118140960795 + 2201635 * 2 ^ 59
def prefixEnd_2201635 : Nat := 4983230072969 + 3 ^ 40 * 2201635 * 2
def baseEnd_2201635 : Nat := 376832326920532942212457

theorem tailTrace_2201635 : CollatzResearch.WordTrace tailWord_2201635 prefixEnd_2201635 376832326920532942212457 := by
  unfold tailWord_2201635
  simp only [CollatzResearch.WordTrace]
  refine ⟨80300225378859879167478359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53533483585906586111652239 80300225378859879167478359)
  ·
    refine ⟨120450338068289818751217539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80300225378859879167478359 120450338068289818751217539)
    ·
      refine ⟨180675507102434728126826309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120450338068289818751217539 180675507102434728126826309)
      ·
        refine ⟨33876657581706511523779933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180675507102434728126826309 33876657581706511523779933)
        ·
          refine ⟨12703746593139941821417475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33876657581706511523779933 12703746593139941821417475)
          ·
            refine ⟨19055619889709912732126213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12703746593139941821417475 19055619889709912732126213)
            ·
              refine ⟨3572928729320608637273665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19055619889709912732126213 3572928729320608637273665)
              ·
                refine ⟨2679696546990456477955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3572928729320608637273665 2679696546990456477955249)
                ·
                  refine ⟨2009772410242842358466437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679696546990456477955249 2009772410242842358466437)
                  ·
                    refine ⟨376832326920532942212457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009772410242842358466437 376832326920532942212457)
                    ·
                      rfl

theorem cell23_2201635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 4].length) (baseStart_2201635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201635 prefixEnd_2201635 := by exact prefixLift 2201635
  have htrace : WordTrace (prefixWord ++ tailWord_2201635) baseStart_2201635 baseEnd_2201635 := by
    simpa [prefixWord, tailWord_2201635, baseEnd_2201635] using wordTrace_append hprefix tailTrace_2201635
  have hstable : (prefixWord ++ tailWord_2201635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201635).length < 2 ^ (prefixWord ++ tailWord_2201635).sum := by decide
  have hdescent : baseEnd_2201635 < baseStart_2201635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201648 : List Nat := [2, 1, 1, 1, 2, 7, 1, 8]
def baseStart_2201648 : Nat := 118140960795 + 2201648 * 2 ^ 59
def prefixEnd_2201648 : Nat := 4983230072969 + 3 ^ 40 * 2201648 * 2
def baseEnd_2201648 : Nat := 41870505778152121324993

theorem tailTrace_2201648 : CollatzResearch.WordTrace tailWord_2201648 prefixEnd_2201648 41870505778152121324993 := by
  unfold tailWord_2201648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40150349763906391193850799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53533799685208521591801065 40150349763906391193850799)
  ·
    refine ⟨60225524645859586790776199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40150349763906391193850799 60225524645859586790776199)
    ·
      refine ⟨90338286968789380186164299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60225524645859586790776199 90338286968789380186164299)
      ·
        refine ⟨135507430453184070279246449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90338286968789380186164299 135507430453184070279246449)
        ·
          refine ⟨101630572839888052709434837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135507430453184070279246449 101630572839888052709434837)
          ·
            refine ⟨2381966550934876235377379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101630572839888052709434837 2381966550934876235377379)
            ·
              refine ⟨3572949826402314353066069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381966550934876235377379 3572949826402314353066069)
              ·
                refine ⟨41870505778152121324993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3572949826402314353066069 41870505778152121324993)
                ·
                  rfl

theorem cell23_2201648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_2201648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201648 prefixEnd_2201648 := by exact prefixLift 2201648
  have htrace : WordTrace (prefixWord ++ tailWord_2201648) baseStart_2201648 baseEnd_2201648 := by
    simpa [prefixWord, tailWord_2201648, baseEnd_2201648] using wordTrace_append hprefix tailTrace_2201648
  have hstable : (prefixWord ++ tailWord_2201648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201648).length < 2 ^ (prefixWord ++ tailWord_2201648).sum := by decide
  have hdescent : baseEnd_2201648 < baseStart_2201648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201651 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_2201651 : Nat := 118140960795 + 2201651 * 2 ^ 59
def prefixEnd_2201651 : Nat := 4983230072969 + 3 ^ 40 * 2201651 * 2
def baseEnd_2201651 : Nat := 1130505196452070764037297

theorem tailTrace_2201651 : CollatzResearch.WordTrace tailWord_2201651 prefixEnd_2201651 1130505196452070764037297 := by
  unfold tailWord_2201651
  simp only [CollatzResearch.WordTrace]
  refine ⟨80300808946801913900060807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53533872631201275933373871 80300808946801913900060807)
  ·
    refine ⟨120451213420202870850091211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80300808946801913900060807 120451213420202870850091211)
    ·
      refine ⟨180676820130304306275136817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120451213420202870850091211 180676820130304306275136817)
      ·
        refine ⟨135507615097728229706352613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180676820130304306275136817 135507615097728229706352613)
        ·
          refine ⟨25407677830824043069941115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135507615097728229706352613 25407677830824043069941115)
          ·
            refine ⟨38111516746236064604911673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25407677830824043069941115 38111516746236064604911673)
            ·
              refine ⟨28583637559677048453683755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38111516746236064604911673 28583637559677048453683755)
              ·
                refine ⟨42875456339515572680525633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28583637559677048453683755 42875456339515572680525633)
                ·
                  refine ⟨32156592254636679510394225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42875456339515572680525633 32156592254636679510394225)
                  ·
                    refine ⟨24117444190977509632795669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32156592254636679510394225 24117444190977509632795669)
                    ·
                      refine ⟨1130505196452070764037297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24117444190977509632795669 1130505196452070764037297)
                      ·
                        rfl

theorem cell23_2201651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_2201651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201651 prefixEnd_2201651 := by exact prefixLift 2201651
  have htrace : WordTrace (prefixWord ++ tailWord_2201651) baseStart_2201651 baseEnd_2201651 := by
    simpa [prefixWord, tailWord_2201651, baseEnd_2201651] using wordTrace_append hprefix tailTrace_2201651
  have hstable : (prefixWord ++ tailWord_2201651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201651).length < 2 ^ (prefixWord ++ tailWord_2201651).sum := by decide
  have hdescent : baseEnd_2201651 < baseStart_2201651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201652 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2201652 : Nat := 118140960795 + 2201652 * 2 ^ 59
def prefixEnd_2201652 : Nat := 4983230072969 + 3 ^ 40 * 2201652 * 2
def baseEnd_2201652 : Nat := 376835236644241753374931

theorem tailTrace_2201652 : CollatzResearch.WordTrace tailWord_2201652 prefixEnd_2201652 376835236644241753374931 := by
  unfold tailWord_2201652
  simp only [CollatzResearch.WordTrace]
  refine ⟨40150422709899145535423605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53533896946532194047231473 40150422709899145535423605)
  ·
    refine ⟨3764102129053044893945963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40150422709899145535423605 3764102129053044893945963)
    ·
      refine ⟨5646153193579567340918945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764102129053044893945963 5646153193579567340918945)
      ·
        refine ⟨4234614895184675505689209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646153193579567340918945 4234614895184675505689209)
        ·
          refine ⟨3175961171388506629266907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234614895184675505689209 3175961171388506629266907)
          ·
            refine ⟨4763941757082759943900361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175961171388506629266907 4763941757082759943900361)
            ·
              refine ⟨3572956317812069957925271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4763941757082759943900361 3572956317812069957925271)
              ·
                refine ⟨5359434476718104936887907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572956317812069957925271 5359434476718104936887907)
                ·
                  refine ⟨8039151715077157405331861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359434476718104936887907 8039151715077157405331861)
                  ·
                    refine ⟨376835236644241753374931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8039151715077157405331861 376835236644241753374931)
                    ·
                      rfl

theorem cell23_2201652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2201652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201652 prefixEnd_2201652 := by exact prefixLift 2201652
  have htrace : WordTrace (prefixWord ++ tailWord_2201652) baseStart_2201652 baseEnd_2201652 := by
    simpa [prefixWord, tailWord_2201652, baseEnd_2201652] using wordTrace_append hprefix tailTrace_2201652
  have hstable : (prefixWord ++ tailWord_2201652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201652).length < 2 ^ (prefixWord ++ tailWord_2201652).sum := by decide
  have hdescent : baseEnd_2201652 < baseStart_2201652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201665 : List Nat := [1, 2, 5, 1, 2, 2, 3, 7]
def baseStart_2201665 : Nat := 118140960795 + 2201665 * 2 ^ 59
def prefixEnd_2201665 : Nat := 4983230072969 + 3 ^ 40 * 2201665 * 2
def baseEnd_2201665 : Nat := 41870829080786433676379

theorem tailTrace_2201665 : CollatzResearch.WordTrace tailWord_2201665 prefixEnd_2201665 41870829080786433676379 := by
  unfold tailWord_2201665
  simp only [CollatzResearch.WordTrace]
  refine ⟨80301319568751194291070449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53534213045834129527380299 80301319568751194291070449)
  ·
    refine ⟨60225989676563395718302837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80301319568751194291070449 60225989676563395718302837)
    ·
      refine ⟨5646186532177818348590891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60225989676563395718302837 5646186532177818348590891)
      ·
        refine ⟨8469279798266727522886337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646186532177818348590891 8469279798266727522886337)
        ·
          refine ⟨6351959848700045642164753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8469279798266727522886337 6351959848700045642164753)
          ·
            refine ⟨4763969886525034231623565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6351959848700045642164753 4763969886525034231623565)
            ·
              refine ⟨1786488707446887836858837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4763969886525034231623565 1786488707446887836858837)
              ·
                refine ⟨41870829080786433676379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1786488707446887836858837 41870829080786433676379)
                ·
                  rfl

theorem cell23_2201665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 7].length) (baseStart_2201665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201665 prefixEnd_2201665 := by exact prefixLift 2201665
  have htrace : WordTrace (prefixWord ++ tailWord_2201665) baseStart_2201665 baseEnd_2201665 := by
    simpa [prefixWord, tailWord_2201665, baseEnd_2201665] using wordTrace_append hprefix tailTrace_2201665
  have hstable : (prefixWord ++ tailWord_2201665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201665).length < 2 ^ (prefixWord ++ tailWord_2201665).sum := by decide
  have hdescent : baseEnd_2201665 < baseStart_2201665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201686 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2201686 : Nat := 118140960795 + 2201686 * 2 ^ 59
def prefixEnd_2201686 : Nat := 4983230072969 + 3 ^ 40 * 2201686 * 2
def baseEnd_2201686 : Nat := 376841056091659375699879

theorem tailTrace_2201686 : CollatzResearch.WordTrace tailWord_2201686 prefixEnd_2201686 376841056091659375699879 := by
  unfold tailWord_2201686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018880343854694679849057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53534723667783409918389941 5018880343854694679849057)
  ·
    refine ⟨3764160257891021009886793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5018880343854694679849057 3764160257891021009886793)
    ·
      refine ⟨2823120193418265757415095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764160257891021009886793 2823120193418265757415095)
      ·
        refine ⟨4234680290127398636122643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823120193418265757415095 4234680290127398636122643)
        ·
          refine ⟨6352020435191097954183965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234680290127398636122643 6352020435191097954183965)
          ·
            refine ⟨2382007663196661732818987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6352020435191097954183965 2382007663196661732818987)
            ·
              refine ⟨3573011494794992599228481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382007663196661732818987 3573011494794992599228481)
              ·
                refine ⟨2679758621096244449421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3573011494794992599228481 2679758621096244449421361)
                ·
                  refine ⟨2009818965822183337066021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679758621096244449421361 2009818965822183337066021)
                  ·
                    refine ⟨376841056091659375699879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009818965822183337066021 376841056091659375699879)
                    ·
                      rfl

theorem cell23_2201686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2201686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201686 prefixEnd_2201686 := by exact prefixLift 2201686
  have htrace : WordTrace (prefixWord ++ tailWord_2201686) baseStart_2201686 baseEnd_2201686 := by
    simpa [prefixWord, tailWord_2201686, baseEnd_2201686] using wordTrace_append hprefix tailTrace_2201686
  have hstable : (prefixWord ++ tailWord_2201686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201686).length < 2 ^ (prefixWord ++ tailWord_2201686).sum := by decide
  have hdescent : baseEnd_2201686 < baseStart_2201686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201692 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2201692 : Nat := 118140960795 + 2201692 * 2 ^ 59
def prefixEnd_2201692 : Nat := 4983230072969 + 3 ^ 40 * 2201692 * 2
def baseEnd_2201692 : Nat := 1130526249158905103624609

theorem tailTrace_2201692 : CollatzResearch.WordTrace tailWord_2201692 prefixEnd_2201692 1130526249158905103624609 := by
  unfold tailWord_2201692
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151152169826688951151665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53534869559768918601535553 40151152169826688951151665)
  ·
    refine ⟨30113364127370016713363749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40151152169826688951151665 30113364127370016713363749)
    ·
      refine ⟨5646255773881878133755703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30113364127370016713363749 5646255773881878133755703)
      ·
        refine ⟨8469383660822817200633555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646255773881878133755703 8469383660822817200633555)
        ·
          refine ⟨12704075491234225800950333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8469383660822817200633555 12704075491234225800950333)
          ·
            refine ⟨4764028309212834675356375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12704075491234225800950333 4764028309212834675356375)
            ·
              refine ⟨7146042463819252013034563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764028309212834675356375 7146042463819252013034563)
              ·
                refine ⟨10719063695728878019551845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146042463819252013034563 10719063695728878019551845)
                ·
                  refine ⟨2009824442949164628665971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10719063695728878019551845 2009824442949164628665971)
                  ·
                    refine ⟨3014736664423746942998957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009824442949164628665971 3014736664423746942998957)
                    ·
                      refine ⟨1130526249158905103624609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014736664423746942998957 1130526249158905103624609)
                      ·
                        rfl

theorem cell23_2201692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2201692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201692 prefixEnd_2201692 := by exact prefixLift 2201692
  have htrace : WordTrace (prefixWord ++ tailWord_2201692) baseStart_2201692 baseEnd_2201692 := by
    simpa [prefixWord, tailWord_2201692, baseEnd_2201692] using wordTrace_append hprefix tailTrace_2201692
  have hstable : (prefixWord ++ tailWord_2201692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201692).length < 2 ^ (prefixWord ++ tailWord_2201692).sum := by decide
  have hdescent : baseEnd_2201692 < baseStart_2201692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201708 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_2201708 : Nat := 118140960795 + 2201708 * 2 ^ 59
def prefixEnd_2201708 : Nat := 4983230072969 + 3 ^ 40 * 2201708 * 2
def baseEnd_2201708 : Nat := 376844821616459013674845

theorem tailTrace_2201708 : CollatzResearch.WordTrace tailWord_2201708 prefixEnd_2201708 376844821616459013674845 := by
  unfold tailWord_2201708
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151443953797706317442889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53535258605063608423257185 40151443953797706317442889)
  ·
    refine ⟨30113582965348279738082167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40151443953797706317442889 30113582965348279738082167)
    ·
      refine ⟨45170374448022419607123251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30113582965348279738082167 45170374448022419607123251)
      ·
        refine ⟨67755561672033629410684877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45170374448022419607123251 67755561672033629410684877)
        ·
          refine ⟨25408335627012611029006829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67755561672033629410684877 25408335627012611029006829)
          ·
            refine ⟨9528125860129729135877561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25408335627012611029006829 9528125860129729135877561)
            ·
              refine ⟨7146094395097296851908171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9528125860129729135877561 7146094395097296851908171)
              ·
                refine ⟨10719141592645945277862257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146094395097296851908171 10719141592645945277862257)
                ·
                  refine ⟨8039356194484458958396693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10719141592645945277862257 8039356194484458958396693)
                  ·
                    refine ⟨376844821616459013674845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8039356194484458958396693 376844821616459013674845)
                    ·
                      rfl

theorem cell23_2201708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_2201708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201708 prefixEnd_2201708 := by exact prefixLift 2201708
  have htrace : WordTrace (prefixWord ++ tailWord_2201708) baseStart_2201708 baseEnd_2201708 := by
    simpa [prefixWord, tailWord_2201708, baseEnd_2201708] using wordTrace_append hprefix tailTrace_2201708
  have hstable : (prefixWord ++ tailWord_2201708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201708).length < 2 ^ (prefixWord ++ tailWord_2201708).sum := by decide
  have hdescent : baseEnd_2201708 < baseStart_2201708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201709 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2201709 : Nat := 118140960795 + 2201709 * 2 ^ 59
def prefixEnd_2201709 : Nat := 4983230072969 + 3 ^ 40 * 2201709 * 2
def baseEnd_2201709 : Nat := 1130534978330031537112031

theorem tailTrace_2201709 : CollatzResearch.WordTrace tailWord_2201709 prefixEnd_2201709 1130534978330031537112031 := by
  unfold tailWord_2201709
  simp only [CollatzResearch.WordTrace]
  refine ⟨80302924380591789805672181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53535282920394526537114787 80302924380591789805672181)
  ·
    refine ⟨7528399160680480294281767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80302924380591789805672181 7528399160680480294281767)
    ·
      refine ⟨11292598741020720441422651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7528399160680480294281767 11292598741020720441422651)
      ·
        refine ⟨16938898111531080662133977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11292598741020720441422651 16938898111531080662133977)
        ·
          refine ⟨12704173583648310496600483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16938898111531080662133977 12704173583648310496600483)
          ·
            refine ⟨19056260375472465744900725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704173583648310496600483 19056260375472465744900725)
            ·
              refine ⟨1786524410200543663584443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19056260375472465744900725 1786524410200543663584443)
              ·
                refine ⟨2679786615300815495376665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786524410200543663584443 2679786615300815495376665)
                ·
                  refine ⟨2009839961475611621532499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679786615300815495376665 2009839961475611621532499)
                  ·
                    refine ⟨3014759942213417432298749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009839961475611621532499 3014759942213417432298749)
                    ·
                      refine ⟨1130534978330031537112031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014759942213417432298749 1130534978330031537112031)
                      ·
                        rfl

theorem cell23_2201709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2201709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201709 prefixEnd_2201709 := by exact prefixLift 2201709
  have htrace : WordTrace (prefixWord ++ tailWord_2201709) baseStart_2201709 baseEnd_2201709 := by
    simpa [prefixWord, tailWord_2201709, baseEnd_2201709] using wordTrace_append hprefix tailTrace_2201709
  have hstable : (prefixWord ++ tailWord_2201709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201709).length < 2 ^ (prefixWord ++ tailWord_2201709).sum := by decide
  have hdescent : baseEnd_2201709 < baseStart_2201709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201732 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_2201732 : Nat := 118140960795 + 2201732 * 2 ^ 59
def prefixEnd_2201732 : Nat := 4983230072969 + 3 ^ 40 * 2201732 * 2
def baseEnd_2201732 : Nat := 1130546788385084947124425

theorem tailTrace_2201732 : CollatzResearch.WordTrace tailWord_2201732 prefixEnd_2201732 1130546788385084947124425 := by
  unfold tailWord_2201732
  simp only [CollatzResearch.WordTrace]
  refine ⟨40151881629754232366879725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53535842173005643155839633 40151881629754232366879725)
  ·
    refine ⟨15056955611157837137579897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40151881629754232366879725 15056955611157837137579897)
    ·
      refine ⟨11292716708368377853184923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15056955611157837137579897 11292716708368377853184923)
      ·
        refine ⟨16939075062552566779777385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11292716708368377853184923 16939075062552566779777385)
        ·
          refine ⟨12704306296914425084833039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16939075062552566779777385 12704306296914425084833039)
          ·
            refine ⟨19056459445371637627249559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704306296914425084833039 19056459445371637627249559)
            ·
              refine ⟨28584689168057456440874339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19056459445371637627249559 28584689168057456440874339)
              ·
                refine ⟨42877033752086184661311509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28584689168057456440874339 42877033752086184661311509)
                ·
                  refine ⟨2009860957129039905998977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42877033752086184661311509 2009860957129039905998977)
                  ·
                    refine ⟨1507395717846779929499233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2009860957129039905998977 1507395717846779929499233)
                    ·
                      refine ⟨1130546788385084947124425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507395717846779929499233 1130546788385084947124425)
                      ·
                        rfl

theorem cell23_2201732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_2201732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201732 prefixEnd_2201732 := by exact prefixLift 2201732
  have htrace : WordTrace (prefixWord ++ tailWord_2201732) baseStart_2201732 baseEnd_2201732 := by
    simpa [prefixWord, tailWord_2201732, baseEnd_2201732] using wordTrace_append hprefix tailTrace_2201732
  have hstable : (prefixWord ++ tailWord_2201732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201732).length < 2 ^ (prefixWord ++ tailWord_2201732).sum := by decide
  have hdescent : baseEnd_2201732 < baseStart_2201732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201778 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2201778 : Nat := 118140960795 + 2201778 * 2 ^ 59
def prefixEnd_2201778 : Nat := 4983230072969 + 3 ^ 40 * 2201778 * 2
def baseEnd_2201778 : Nat := 1130570408495191767149213

theorem tailTrace_2201778 : CollatzResearch.WordTrace tailWord_2201778 prefixEnd_2201778 1130570408495191767149213 := by
  unfold tailWord_2201778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20076360254335453647483497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53536960678227876393289325 20076360254335453647483497)
  ·
    refine ⟨15057270190751590235612623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20076360254335453647483497 15057270190751590235612623)
    ·
      refine ⟨22585905286127385353418935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057270190751590235612623 22585905286127385353418935)
      ·
        refine ⟨33878857929191078030128403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22585905286127385353418935 33878857929191078030128403)
        ·
          refine ⟨50818286893786617045192605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33878857929191078030128403 50818286893786617045192605)
          ·
            refine ⟨19056857585169981391947227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50818286893786617045192605 19056857585169981391947227)
            ·
              refine ⟨28585286377754972087920841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19056857585169981391947227 28585286377754972087920841)
              ·
                refine ⟨21438964783316229065940631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28585286377754972087920841 21438964783316229065940631)
                ·
                  refine ⟨32158447174974343598910947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21438964783316229065940631 32158447174974343598910947)
                  ·
                    refine ⟨48237670762461515398366421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32158447174974343598910947 48237670762461515398366421)
                    ·
                      refine ⟨1130570408495191767149213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48237670762461515398366421 1130570408495191767149213)
                      ·
                        rfl

theorem cell23_2201778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2201778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201778 prefixEnd_2201778 := by exact prefixLift 2201778
  have htrace : WordTrace (prefixWord ++ tailWord_2201778) baseStart_2201778 baseEnd_2201778 := by
    simpa [prefixWord, tailWord_2201778, baseEnd_2201778] using wordTrace_append hprefix tailTrace_2201778
  have hstable : (prefixWord ++ tailWord_2201778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201778).length < 2 ^ (prefixWord ++ tailWord_2201778).sum := by decide
  have hdescent : baseEnd_2201778 < baseStart_2201778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201785 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_2201785 : Nat := 118140960795 + 2201785 * 2 ^ 59
def prefixEnd_2201785 : Nat := 4983230072969 + 3 ^ 40 * 2201785 * 2
def baseEnd_2201785 : Nat := 376858000953257746587227

theorem tailTrace_2201785 : CollatzResearch.WordTrace tailWord_2201785 prefixEnd_2201785 376858000953257746587227 := by
  unfold tailWord_2201785
  simp only [CollatzResearch.WordTrace]
  refine ⟨80305696328316454785438809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53537130885544303190292539 80305696328316454785438809)
  ·
    refine ⟨60229272246237341089079107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80305696328316454785438809 60229272246237341089079107)
    ·
      refine ⟨90343908369356011633618661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60229272246237341089079107 90343908369356011633618661)
      ·
        refine ⟨16939482819254252181303499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90343908369356011633618661 16939482819254252181303499)
        ·
          refine ⟨25409224228881378271955249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16939482819254252181303499 25409224228881378271955249)
          ·
            refine ⟨19056918171661033703966437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25409224228881378271955249 19056918171661033703966437)
            ·
              refine ⟨3573172157186443819493707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19056918171661033703966437 3573172157186443819493707)
              ·
                refine ⟨5359758235779665729240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573172157186443819493707 5359758235779665729240561)
                ·
                  refine ⟨4019818676834749296930421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359758235779665729240561 4019818676834749296930421)
                  ·
                    refine ⟨376858000953257746587227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019818676834749296930421 376858000953257746587227)
                    ·
                      rfl

theorem cell23_2201785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_2201785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201785 prefixEnd_2201785 := by exact prefixLift 2201785
  have htrace : WordTrace (prefixWord ++ tailWord_2201785) baseStart_2201785 baseEnd_2201785 := by
    simpa [prefixWord, tailWord_2201785, baseEnd_2201785] using wordTrace_append hprefix tailTrace_2201785
  have hstable : (prefixWord ++ tailWord_2201785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201785).length < 2 ^ (prefixWord ++ tailWord_2201785).sum := by decide
  have hdescent : baseEnd_2201785 < baseStart_2201785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201815 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 3, 4]
def baseStart_2201815 : Nat := 118140960795 + 2201815 * 2 ^ 59
def prefixEnd_2201815 : Nat := 4983230072969 + 3 ^ 40 * 2201815 * 2
def baseEnd_2201815 : Nat := 376863135759802707462181

theorem tailTrace_2201815 : CollatzResearch.WordTrace tailWord_2201815 prefixEnd_2201815 376863135759802707462181 := by
  unfold tailWord_2201815
  simp only [CollatzResearch.WordTrace]
  refine ⟨80306790518207769909030899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53537860345471846606020599 80306790518207769909030899)
  ·
    refine ⟨120460185777311654863546349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80306790518207769909030899 120460185777311654863546349)
    ·
      refine ⟨45172569666491870573829881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120460185777311654863546349 45172569666491870573829881)
      ·
        refine ⟨33879427249868902930372411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45172569666491870573829881 33879427249868902930372411)
        ·
          refine ⟨50819140874803354395558617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33879427249868902930372411 50819140874803354395558617)
          ·
            refine ⟨38114355656102515796668963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50819140874803354395558617 38114355656102515796668963)
            ·
              refine ⟨57171533484153773695003445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38114355656102515796668963 57171533484153773695003445)
              ·
                refine ⟨5359831264139416283906573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57171533484153773695003445 5359831264139416283906573)
                ·
                  refine ⟨2009936724052281106464965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5359831264139416283906573 2009936724052281106464965)
                  ·
                    refine ⟨376863135759802707462181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009936724052281106464965 376863135759802707462181)
                    ·
                      rfl

theorem cell23_2201815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_2201815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201815 prefixEnd_2201815 := by exact prefixLift 2201815
  have htrace : WordTrace (prefixWord ++ tailWord_2201815) baseStart_2201815 baseEnd_2201815 := by
    simpa [prefixWord, tailWord_2201815, baseEnd_2201815] using wordTrace_append hprefix tailTrace_2201815
  have hstable : (prefixWord ++ tailWord_2201815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201815).length < 2 ^ (prefixWord ++ tailWord_2201815).sum := by decide
  have hdescent : baseEnd_2201815 < baseStart_2201815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201825 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_2201825 : Nat := 118140960795 + 2201825 * 2 ^ 59
def prefixEnd_2201825 : Nat := 4983230072969 + 3 ^ 40 * 2201825 * 2
def baseEnd_2201825 : Nat := 1130594542085953083261497

theorem tailTrace_2201825 : CollatzResearch.WordTrace tailWord_2201825 prefixEnd_2201825 1130594542085953083261497 := by
  unfold tailWord_2201825
  simp only [CollatzResearch.WordTrace]
  refine ⟨80307155248171541616894929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53538103498781027744596619 80307155248171541616894929)
  ·
    refine ⟨60230366436128656212671197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80307155248171541616894929 60230366436128656212671197)
    ·
      refine ⟨22586387413548246079751699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60230366436128656212671197 22586387413548246079751699)
      ·
        refine ⟨33879581120322369119627549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22586387413548246079751699 33879581120322369119627549)
        ·
          refine ⟨12704842920120888419860331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33879581120322369119627549 12704842920120888419860331)
          ·
            refine ⟨19057264380181332629790497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12704842920120888419860331 19057264380181332629790497)
            ·
              refine ⟨14292948285135999472342873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19057264380181332629790497 14292948285135999472342873)
              ·
                refine ⟨10719711213851999604257155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14292948285135999472342873 10719711213851999604257155)
                ·
                  refine ⟨16079566820777999406385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10719711213851999604257155 16079566820777999406385733)
                  ·
                    refine ⟨3014918778895874888697325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16079566820777999406385733 3014918778895874888697325)
                    ·
                      refine ⟨1130594542085953083261497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014918778895874888697325 1130594542085953083261497)
                      ·
                        rfl

theorem cell23_2201825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_2201825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201825 prefixEnd_2201825 := by exact prefixLift 2201825
  have htrace : WordTrace (prefixWord ++ tailWord_2201825) baseStart_2201825 baseEnd_2201825 := by
    simpa [prefixWord, tailWord_2201825, baseEnd_2201825] using wordTrace_append hprefix tailTrace_2201825
  have hstable : (prefixWord ++ tailWord_2201825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201825).length < 2 ^ (prefixWord ++ tailWord_2201825).sum := by decide
  have hdescent : baseEnd_2201825 < baseStart_2201825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201828 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 10]
def baseStart_2201828 : Nat := 118140960795 + 2201828 * 2 ^ 59
def prefixEnd_2201828 : Nat := 4983230072969 + 3 ^ 40 * 2201828 * 2
def baseEnd_2201828 : Nat := 125621786947546285724887

theorem tailTrace_2201828 : CollatzResearch.WordTrace tailWord_2201828 prefixEnd_2201828 125621786947546285724887 := by
  unfold tailWord_2201828
  simp only [CollatzResearch.WordTrace]
  refine ⟨40153632333580336564627069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53538176444773782086169425 40153632333580336564627069)
  ·
    refine ⟨15057612125092626211735151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40153632333580336564627069 15057612125092626211735151)
    ·
      refine ⟨22586418187638939317602727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057612125092626211735151 22586418187638939317602727)
      ·
        refine ⟨33879627281458408976404091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22586418187638939317602727 33879627281458408976404091)
        ·
          refine ⟨50819440922187613464606137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33879627281458408976404091 50819440922187613464606137)
          ·
            refine ⟨38114580691640710098454603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50819440922187613464606137 38114580691640710098454603)
            ·
              refine ⟨57171871037461065147681905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38114580691640710098454603 57171871037461065147681905)
              ·
                refine ⟨42878903278095798860761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57171871037461065147681905 42878903278095798860761429)
                ·
                  refine ⟨125621786947546285724887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42878903278095798860761429 125621786947546285724887)
                  ·
                    rfl

theorem cell23_2201828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_2201828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201828 prefixEnd_2201828 := by exact prefixLift 2201828
  have htrace : WordTrace (prefixWord ++ tailWord_2201828) baseStart_2201828 baseEnd_2201828 := by
    simpa [prefixWord, tailWord_2201828, baseEnd_2201828] using wordTrace_append hprefix tailTrace_2201828
  have hstable : (prefixWord ++ tailWord_2201828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201828).length < 2 ^ (prefixWord ++ tailWord_2201828).sum := by decide
  have hdescent : baseEnd_2201828 < baseStart_2201828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201832 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2201832 : Nat := 118140960795 + 2201832 * 2 ^ 59
def prefixEnd_2201832 : Nat := 4983230072969 + 3 ^ 40 * 2201832 * 2
def baseEnd_2201832 : Nat := 376866045483511518624655

theorem tailTrace_2201832 : CollatzResearch.WordTrace tailWord_2201832 prefixEnd_2201832 376866045483511518624655 := by
  unfold tailWord_2201832
  simp only [CollatzResearch.WordTrace]
  refine ⟨40153705279573090906199875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53538273706097454541599833 40153705279573090906199875)
  ·
    refine ⟨60230557919359636359299813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40153705279573090906199875 60230557919359636359299813)
    ·
      refine ⟨11293229609879931817368715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60230557919359636359299813 11293229609879931817368715)
      ·
        refine ⟨16939844414819897726053073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11293229609879931817368715 16939844414819897726053073)
        ·
          refine ⟨12704883311114923294539805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16939844414819897726053073 12704883311114923294539805)
          ·
            refine ⟨4764331241668096235452427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12704883311114923294539805 4764331241668096235452427)
            ·
              refine ⟨7146496862502144353178641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764331241668096235452427 7146496862502144353178641)
              ·
                refine ⟨5359872646876608264883981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146496862502144353178641 5359872646876608264883981)
                ·
                  refine ⟨2009952242578728099331493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5359872646876608264883981 2009952242578728099331493)
                  ·
                    refine ⟨376866045483511518624655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2009952242578728099331493 376866045483511518624655)
                    ·
                      rfl

theorem cell23_2201832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2201832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201832 prefixEnd_2201832 := by exact prefixLift 2201832
  have htrace : WordTrace (prefixWord ++ tailWord_2201832) baseStart_2201832 baseEnd_2201832 := by
    simpa [prefixWord, tailWord_2201832, baseEnd_2201832] using wordTrace_append hprefix tailTrace_2201832
  have hstable : (prefixWord ++ tailWord_2201832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201832).length < 2 ^ (prefixWord ++ tailWord_2201832).sum := by decide
  have hdescent : baseEnd_2201832 < baseStart_2201832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201842 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2201842 : Nat := 118140960795 + 2201842 * 2 ^ 59
def prefixEnd_2201842 : Nat := 4983230072969 + 3 ^ 40 * 2201842 * 2
def baseEnd_2201842 : Nat := 1130603271257079516748919

theorem tailTrace_2201842 : CollatzResearch.WordTrace tailWord_2201842 prefixEnd_2201842 1130603271257079516748919 := by
  unfold tailWord_2201842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20076943822277488380065945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53538516859406635680175853 20076943822277488380065945)
  ·
    refine ⟨15057707866708116285049459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20076943822277488380065945 15057707866708116285049459)
    ·
      refine ⟨22586561800062174427574189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15057707866708116285049459 22586561800062174427574189)
      ·
        refine ⟨8469960675023315410340321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22586561800062174427574189 8469960675023315410340321)
        ·
          refine ⟨6352470506267486557755241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8469960675023315410340321 6352470506267486557755241)
          ·
            refine ⟨4764352879700614918316431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6352470506267486557755241 4764352879700614918316431)
            ·
              refine ⟨7146529319550922377474647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764352879700614918316431 7146529319550922377474647)
              ·
                refine ⟨10719793979326383566211971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7146529319550922377474647 10719793979326383566211971)
                ·
                  refine ⟨16079690968989575349317957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10719793979326383566211971 16079690968989575349317957)
                  ·
                    refine ⟨3014942056685545377997117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16079690968989575349317957 3014942056685545377997117)
                    ·
                      refine ⟨1130603271257079516748919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3014942056685545377997117 1130603271257079516748919)
                      ·
                        rfl

theorem cell23_2201842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2201842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201842 prefixEnd_2201842 := by exact prefixLift 2201842
  have htrace : WordTrace (prefixWord ++ tailWord_2201842) baseStart_2201842 baseEnd_2201842 := by
    simpa [prefixWord, tailWord_2201842, baseEnd_2201842] using wordTrace_append hprefix tailTrace_2201842
  have hstable : (prefixWord ++ tailWord_2201842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201842).length < 2 ^ (prefixWord ++ tailWord_2201842).sum := by decide
  have hdescent : baseEnd_2201842 < baseStart_2201842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2201848 : Nat := 118140960795 + 2201848 * 2 ^ 59
def prefixEnd_2201848 : Nat := 4983230072969 + 3 ^ 40 * 2201848 * 2
def baseEnd_2201848 : Nat := 1130606352141006493273891

theorem tailTrace_2201848 : CollatzResearch.WordTrace tailWord_2201848 prefixEnd_2201848 1130606352141006493273891 := by
  unfold tailWord_2201848
  simp only [CollatzResearch.WordTrace]
  refine ⟨40153997063544108272491099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53538662751392144363321465 40153997063544108272491099)
  ·
    refine ⟨60230995595316162408736649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40153997063544108272491099 60230995595316162408736649)
    ·
      refine ⟨45173246696487121806552487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60230995595316162408736649 45173246696487121806552487)
      ·
        refine ⟨67759870044730682709828731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45173246696487121806552487 67759870044730682709828731)
        ·
          refine ⟨101639805067096024064743097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67759870044730682709828731 101639805067096024064743097)
          ·
            refine ⟨76229853800322018048557323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101639805067096024064743097 76229853800322018048557323)
            ·
              refine ⟨114344780700483027072835985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76229853800322018048557323 114344780700483027072835985)
              ·
                refine ⟨85758585525362270304626989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114344780700483027072835985 85758585525362270304626989)
                ·
                  refine ⟨32159469572010851364235121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85758585525362270304626989 32159469572010851364235121)
                  ·
                    refine ⟨24119602179008138523176341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32159469572010851364235121 24119602179008138523176341)
                    ·
                      refine ⟨1130606352141006493273891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24119602179008138523176341 1130606352141006493273891)
                      ·
                        rfl

theorem cell23_2201848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2201848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201848 prefixEnd_2201848 := by exact prefixLift 2201848
  have htrace : WordTrace (prefixWord ++ tailWord_2201848) baseStart_2201848 baseEnd_2201848 := by
    simpa [prefixWord, tailWord_2201848, baseEnd_2201848] using wordTrace_append hprefix tailTrace_2201848
  have hstable : (prefixWord ++ tailWord_2201848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201848).length < 2 ^ (prefixWord ++ tailWord_2201848).sum := by decide
  have hdescent : baseEnd_2201848 < baseStart_2201848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201892 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_2201892 : Nat := 118140960795 + 2201892 * 2 ^ 59
def prefixEnd_2201892 : Nat := 4983230072969 + 3 ^ 40 * 2201892 * 2
def baseEnd_2201892 : Nat := 376876315096601440374563

theorem tailTrace_2201892 : CollatzResearch.WordTrace tailWord_2201892 prefixEnd_2201892 376876315096601440374563 := by
  unfold tailWord_2201892
  simp only [CollatzResearch.WordTrace]
  refine ⟨40154799469464406029791965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53539732625952541373055953 40154799469464406029791965)
  ·
    refine ⟨15058049801049152261171987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40154799469464406029791965 15058049801049152261171987)
    ·
      refine ⟨22587074701573728391757981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15058049801049152261171987 22587074701573728391757981)
      ·
        refine ⟨8470153013090148146909243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22587074701573728391757981 8470153013090148146909243)
        ·
          refine ⟨12705229519635222220363865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8470153013090148146909243 12705229519635222220363865)
          ·
            refine ⟨9528922139726416665272899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12705229519635222220363865 9528922139726416665272899)
            ·
              refine ⟨14293383209589624997909349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9528922139726416665272899 14293383209589624997909349)
              ·
                refine ⟨2680009351798054687108003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14293383209589624997909349 2680009351798054687108003)
                ·
                  refine ⟨4020014027697082030662005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680009351798054687108003 4020014027697082030662005)
                  ·
                    refine ⟨376876315096601440374563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4020014027697082030662005 376876315096601440374563)
                    ·
                      rfl

theorem cell23_2201892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_2201892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201892 prefixEnd_2201892 := by exact prefixLift 2201892
  have htrace : WordTrace (prefixWord ++ tailWord_2201892) baseStart_2201892 baseEnd_2201892 := by
    simpa [prefixWord, tailWord_2201892, baseEnd_2201892] using wordTrace_append hprefix tailTrace_2201892
  have hstable : (prefixWord ++ tailWord_2201892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201892).length < 2 ^ (prefixWord ++ tailWord_2201892).sum := by decide
  have hdescent : baseEnd_2201892 < baseStart_2201892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201912 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2201912 : Nat := 118140960795 + 2201912 * 2 ^ 59
def prefixEnd_2201912 : Nat := 4983230072969 + 3 ^ 40 * 2201912 * 2
def baseEnd_2201912 : Nat := 1130639214902894242873597

theorem tailTrace_2201912 : CollatzResearch.WordTrace tailWord_2201912 prefixEnd_2201912 1130639214902894242873597 := by
  unfold tailWord_2201912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40155164199428177737655995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53540218932570903650207993 40155164199428177737655995)
  ·
    refine ⟨60232746299142266606483993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40155164199428177737655995 60232746299142266606483993)
    ·
      refine ⟨45174559724356699954862995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60232746299142266606483993 45174559724356699954862995)
      ·
        refine ⟨67761839586535049932294493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45174559724356699954862995 67761839586535049932294493)
        ·
          refine ⟨25410689844950643724610435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67761839586535049932294493 25410689844950643724610435)
          ·
            refine ⟨38116034767425965586915653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25410689844950643724610435 38116034767425965586915653)
            ·
              refine ⟨7146756518892368547546685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38116034767425965586915653 7146756518892368547546685)
              ·
                refine ⟨2680033694584638205330007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7146756518892368547546685 2680033694584638205330007)
                ·
                  refine ⟨4020050541876957307995011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680033694584638205330007 4020050541876957307995011)
                  ·
                    refine ⟨6030075812815435961992517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020050541876957307995011 6030075812815435961992517)
                    ·
                      refine ⟨1130639214902894242873597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6030075812815435961992517 1130639214902894242873597)
                      ·
                        rfl

theorem cell23_2201912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2201912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201912 prefixEnd_2201912 := by exact prefixLift 2201912
  have htrace : WordTrace (prefixWord ++ tailWord_2201912) baseStart_2201912 baseEnd_2201912 := by
    simpa [prefixWord, tailWord_2201912, baseEnd_2201912] using wordTrace_append hprefix tailTrace_2201912
  have hstable : (prefixWord ++ tailWord_2201912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201912).length < 2 ^ (prefixWord ++ tailWord_2201912).sum := by decide
  have hdescent : baseEnd_2201912 < baseStart_2201912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201932 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2201932 : Nat := 118140960795 + 2201932 * 2 ^ 59
def prefixEnd_2201932 : Nat := 4983230072969 + 3 ^ 40 * 2201932 * 2
def baseEnd_2201932 : Nat := 1130649484515984164623505

theorem tailTrace_2201932 : CollatzResearch.WordTrace tailWord_2201932 prefixEnd_2201932 1130649484515984164623505 := by
  unfold tailWord_2201932
  simp only [CollatzResearch.WordTrace]
  refine ⟨40155528929391949445520025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53540705239189265927360033 40155528929391949445520025)
  ·
    refine ⟨30116646697043962084140019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40155528929391949445520025 30116646697043962084140019)
    ·
      refine ⟨45174970045565943126210029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30116646697043962084140019 45174970045565943126210029)
      ·
        refine ⟨16940613767087228672328761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45174970045565943126210029 16940613767087228672328761)
        ·
          refine ⟨12705460325315421504246571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16940613767087228672328761 12705460325315421504246571)
          ·
            refine ⟨19058190487973132256369857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12705460325315421504246571 19058190487973132256369857)
            ·
              refine ⟨14293642865979849192277393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19058190487973132256369857 14293642865979849192277393)
              ·
                refine ⟨10720232149484886894208045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14293642865979849192277393 10720232149484886894208045)
                ·
                  refine ⟨4020087056056832585328017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10720232149484886894208045 4020087056056832585328017)
                  ·
                    refine ⟨3015065292042624438996013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020087056056832585328017 3015065292042624438996013)
                    ·
                      refine ⟨1130649484515984164623505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015065292042624438996013 1130649484515984164623505)
                      ·
                        rfl

theorem cell23_2201932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2201932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201932 prefixEnd_2201932 := by exact prefixLift 2201932
  have htrace : WordTrace (prefixWord ++ tailWord_2201932) baseStart_2201932 baseEnd_2201932 := by
    simpa [prefixWord, tailWord_2201932, baseEnd_2201932] using wordTrace_append hprefix tailTrace_2201932
  have hstable : (prefixWord ++ tailWord_2201932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201932).length < 2 ^ (prefixWord ++ tailWord_2201932).sum := by decide
  have hdescent : baseEnd_2201932 < baseStart_2201932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201974 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2201974 : Nat := 118140960795 + 2201974 * 2 ^ 59
def prefixEnd_2201974 : Nat := 4983230072969 + 3 ^ 40 * 2201974 * 2
def baseEnd_2201974 : Nat := 1130671050703473000298313

theorem tailTrace_2201974 : CollatzResearch.WordTrace tailWord_2201974 prefixEnd_2201974 1130671050703473000298313 := by
  unfold tailWord_2201974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019536857789483754004311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53541726483087826709379317 5019536857789483754004311)
  ·
    refine ⟨7529305286684225631006467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019536857789483754004311 7529305286684225631006467)
    ·
      refine ⟨11293957930026338446509701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529305286684225631006467 11293957930026338446509701)
      ·
        refine ⟨2117617111879938458720569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11293957930026338446509701 2117617111879938458720569)
        ·
          refine ⟨1588212833909953844040427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117617111879938458720569 1588212833909953844040427)
          ·
            refine ⟨2382319250864930766060641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588212833909953844040427 2382319250864930766060641)
            ·
              refine ⟨1786739438148698074545481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382319250864930766060641 1786739438148698074545481)
              ·
                refine ⟨1340054578611523555909111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786739438148698074545481 1340054578611523555909111)
                ·
                  refine ⟨2010081867917285333863667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340054578611523555909111 2010081867917285333863667)
                  ·
                    refine ⟨3015122801875928000795501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010081867917285333863667 3015122801875928000795501)
                    ·
                      refine ⟨1130671050703473000298313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015122801875928000795501 1130671050703473000298313)
                      ·
                        rfl

theorem cell23_2201974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2201974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201974 prefixEnd_2201974 := by exact prefixLift 2201974
  have htrace : WordTrace (prefixWord ++ tailWord_2201974) baseStart_2201974 baseEnd_2201974 := by
    simpa [prefixWord, tailWord_2201974, baseEnd_2201974] using wordTrace_append hprefix tailTrace_2201974
  have hstable : (prefixWord ++ tailWord_2201974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201974).length < 2 ^ (prefixWord ++ tailWord_2201974).sum := by decide
  have hdescent : baseEnd_2201974 < baseStart_2201974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201979 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 3]
def baseStart_2201979 : Nat := 118140960795 + 2201979 * 2 ^ 59
def prefixEnd_2201979 : Nat := 4983230072969 + 3 ^ 40 * 2201979 * 2
def baseEnd_2201979 : Nat := 1130673618106745480735789

theorem tailTrace_2201979 : CollatzResearch.WordTrace tailWord_2201979 prefixEnd_2201979 1130673618106745480735789 := by
  unfold tailWord_2201979
  simp only [CollatzResearch.WordTrace]
  refine ⟨80312772089613625918000991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53541848059742417278667327 80312772089613625918000991)
  ·
    refine ⟨120469158134420438877001487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80312772089613625918000991 120469158134420438877001487)
    ·
      refine ⟨180703737201630658315502231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120469158134420438877001487 180703737201630658315502231)
      ·
        refine ⟨271055605802445987473253347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180703737201630658315502231 271055605802445987473253347)
        ·
          refine ⟨406583408703668981209880021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271055605802445987473253347 406583408703668981209880021)
          ·
            refine ⟨9529298641492241747106563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 406583408703668981209880021 9529298641492241747106563)
            ·
              refine ⟨14293947962238362620659845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529298641492241747106563 14293947962238362620659845)
              ·
                refine ⟨2680115242919692991373721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14293947962238362620659845 2680115242919692991373721)
                ·
                  refine ⟨2010086432189769743530291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2680115242919692991373721 2010086432189769743530291)
                  ·
                    refine ⟨3015129648284654615295437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010086432189769743530291 3015129648284654615295437)
                    ·
                      refine ⟨1130673618106745480735789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015129648284654615295437 1130673618106745480735789)
                      ·
                        rfl

theorem cell23_2201979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 3].length) (baseStart_2201979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201979 prefixEnd_2201979 := by exact prefixLift 2201979
  have htrace : WordTrace (prefixWord ++ tailWord_2201979) baseStart_2201979 baseEnd_2201979 := by
    simpa [prefixWord, tailWord_2201979, baseEnd_2201979] using wordTrace_append hprefix tailTrace_2201979
  have hstable : (prefixWord ++ tailWord_2201979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201979).length < 2 ^ (prefixWord ++ tailWord_2201979).sum := by decide
  have hdescent : baseEnd_2201979 < baseStart_2201979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201986 : List Nat := [3, 4, 2, 1, 2, 2, 1, 8]
def baseStart_2201986 : Nat := 118140960795 + 2201986 * 2 ^ 59
def prefixEnd_2201986 : Nat := 4983230072969 + 3 ^ 40 * 2201986 * 2
def baseEnd_2201986 : Nat := 41876933795234331605491

theorem tailTrace_2201986 : CollatzResearch.WordTrace tailWord_2201986 prefixEnd_2201986 41876933795234331605491 := by
  unfold tailWord_2201986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078256850147066528376453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53542018267058844075670541 20078256850147066528376453)
  ·
    refine ⟨3764673159402574974070585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20078256850147066528376453 3764673159402574974070585)
    ·
      refine ⟨2823504869551931230552939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764673159402574974070585 2823504869551931230552939)
      ·
        refine ⟨4235257304327896845829409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823504869551931230552939 4235257304327896845829409)
        ·
          refine ⟨3176442978245922634372057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4235257304327896845829409 3176442978245922634372057)
          ·
            refine ⟨2382332233684441975779043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176442978245922634372057 2382332233684441975779043)
            ·
              refine ⟨3573498350526662963668565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382332233684441975779043 3573498350526662963668565)
              ·
                refine ⟨41876933795234331605491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3573498350526662963668565 41876933795234331605491)
                ·
                  rfl

theorem cell23_2201986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_2201986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201986 prefixEnd_2201986 := by exact prefixLift 2201986
  have htrace : WordTrace (prefixWord ++ tailWord_2201986) baseStart_2201986 baseEnd_2201986 := by
    simpa [prefixWord, tailWord_2201986, baseEnd_2201986] using wordTrace_append hprefix tailTrace_2201986
  have hstable : (prefixWord ++ tailWord_2201986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201986).length < 2 ^ (prefixWord ++ tailWord_2201986).sum := by decide
  have hdescent : baseEnd_2201986 < baseStart_2201986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2201995 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 8]
def baseStart_2201995 : Nat := 118140960795 + 2201995 * 2 ^ 59
def prefixEnd_2201995 : Nat := 4983230072969 + 3 ^ 40 * 2201995 * 2
def baseEnd_2201995 : Nat := 376893944599072472711905

theorem tailTrace_2201995 : CollatzResearch.WordTrace tailWord_2201995 prefixEnd_2201995 376893944599072472711905 := by
  unfold tailWord_2201995
  simp only [CollatzResearch.WordTrace]
  refine ⟨80313355657555660650583439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53542237105037107100388959 80313355657555660650583439)
  ·
    refine ⟨120470033486333490975875159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80313355657555660650583439 120470033486333490975875159)
    ·
      refine ⟨180705050229500236463812739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120470033486333490975875159 180705050229500236463812739)
      ·
        refine ⟨271057575344250354695719109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180705050229500236463812739 271057575344250354695719109)
        ·
          refine ⟨50823295377046941505447333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271057575344250354695719109 50823295377046941505447333)
          ·
            refine ⟨9529367883196301532271375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50823295377046941505447333 9529367883196301532271375)
            ·
              refine ⟨14294051824794452298407063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529367883196301532271375 14294051824794452298407063)
              ·
                refine ⟨21441077737191678447610595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14294051824794452298407063 21441077737191678447610595)
                ·
                  refine ⟨32161616605787517671415893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21441077737191678447610595 32161616605787517671415893)
                  ·
                    refine ⟨376893944599072472711905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32161616605787517671415893 376893944599072472711905)
                    ·
                      rfl

theorem cell23_2201995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_2201995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2201995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2201995 prefixEnd_2201995 := by exact prefixLift 2201995
  have htrace : WordTrace (prefixWord ++ tailWord_2201995) baseStart_2201995 baseEnd_2201995 := by
    simpa [prefixWord, tailWord_2201995, baseEnd_2201995] using wordTrace_append hprefix tailTrace_2201995
  have hstable : (prefixWord ++ tailWord_2201995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2201995).length < 2 ^ (prefixWord ++ tailWord_2201995).sum := by decide
  have hdescent : baseEnd_2201995 < baseStart_2201995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2201995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202019 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 4, 2]
def baseStart_2202019 : Nat := 118140960795 + 2202019 * 2 ^ 59
def prefixEnd_2202019 : Nat := 4983230072969 + 3 ^ 40 * 2202019 * 2
def baseEnd_2202019 : Nat := 1130694157332925324235605

theorem tailTrace_2202019 : CollatzResearch.WordTrace tailWord_2202019 prefixEnd_2202019 1130694157332925324235605 := by
  unfold tailWord_2202019
  simp only [CollatzResearch.WordTrace]
  refine ⟨80314231009468712749457111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53542820672979141832971407 80314231009468712749457111)
  ·
    refine ⟨120471346514203069124185667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80314231009468712749457111 120471346514203069124185667)
    ·
      refine ⟨180707019771304603686278501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120471346514203069124185667 180707019771304603686278501)
      ·
        refine ⟨33882566207119613191177219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180707019771304603686278501 33882566207119613191177219)
        ·
          refine ⟨50823849310679419786765829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33882566207119613191177219 50823849310679419786765829)
          ·
            refine ⟨9529471745752391210018593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50823849310679419786765829 9529471745752391210018593)
            ·
              refine ⟨7147103809314293407513945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9529471745752391210018593 7147103809314293407513945)
              ·
                refine ⟨5360327856985720055635459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7147103809314293407513945 5360327856985720055635459)
                ·
                  refine ⟨8040491785478580083453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360327856985720055635459 8040491785478580083453189)
                  ·
                    refine ⟨1507592209777233765647473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8040491785478580083453189 1507592209777233765647473)
                    ·
                      refine ⟨1130694157332925324235605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507592209777233765647473 1130694157332925324235605)
                      ·
                        rfl

theorem cell23_2202019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_2202019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202019 prefixEnd_2202019 := by exact prefixLift 2202019
  have htrace : WordTrace (prefixWord ++ tailWord_2202019) baseStart_2202019 baseEnd_2202019 := by
    simpa [prefixWord, tailWord_2202019, baseEnd_2202019] using wordTrace_append hprefix tailTrace_2202019
  have hstable : (prefixWord ++ tailWord_2202019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202019).length < 2 ^ (prefixWord ++ tailWord_2202019).sum := by decide
  have hdescent : baseEnd_2202019 < baseStart_2202019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202023 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_2202023 : Nat := 118140960795 + 2202023 * 2 ^ 59
def prefixEnd_2202023 : Nat := 4983230072969 + 3 ^ 40 * 2202023 * 2
def baseEnd_2202023 : Nat := 1130696211255543308585587

theorem tailTrace_2202023 : CollatzResearch.WordTrace tailWord_2202023 prefixEnd_2202023 1130696211255543308585587 := by
  unfold tailWord_2202023
  simp only [CollatzResearch.WordTrace]
  refine ⟨80314376901454221432602723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53542917934302814288401815 80314376901454221432602723)
  ·
    refine ⟨120471565352181332148904085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80314376901454221432602723 120471565352181332148904085)
    ·
      refine ⟨5647104625883499944479879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120471565352181332148904085 5647104625883499944479879)
      ·
        refine ⟨8470656938825249916719819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647104625883499944479879 8470656938825249916719819)
        ·
          refine ⟨12705985408237874875079729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8470656938825249916719819 12705985408237874875079729)
          ·
            refine ⟨9529489056178406156309797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12705985408237874875079729 9529489056178406156309797)
            ·
              refine ⟨1786779198033451154308087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9529489056178406156309797 1786779198033451154308087)
              ·
                refine ⟨2680168797050176731462131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786779198033451154308087 2680168797050176731462131)
                ·
                  refine ⟨4020253195575265097193197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680168797050176731462131 4020253195575265097193197)
                  ·
                    refine ⟨1507594948340724411447449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4020253195575265097193197 1507594948340724411447449)
                    ·
                      refine ⟨1130696211255543308585587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507594948340724411447449 1130696211255543308585587)
                      ·
                        rfl

theorem cell23_2202023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_2202023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202023 prefixEnd_2202023 := by exact prefixLift 2202023
  have htrace : WordTrace (prefixWord ++ tailWord_2202023) baseStart_2202023 baseEnd_2202023 := by
    simpa [prefixWord, tailWord_2202023, baseEnd_2202023] using wordTrace_append hprefix tailTrace_2202023
  have hstable : (prefixWord ++ tailWord_2202023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202023).length < 2 ^ (prefixWord ++ tailWord_2202023).sum := by decide
  have hdescent : baseEnd_2202023 < baseStart_2202023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202072 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_2202072 : Nat := 118140960795 + 2202072 * 2 ^ 59
def prefixEnd_2202072 : Nat := 4983230072969 + 3 ^ 40 * 2202072 * 2
def baseEnd_2202072 : Nat := 376907123935871205624287

theorem tailTrace_2202072 : CollatzResearch.WordTrace tailWord_2202072 prefixEnd_2202072 376907123935871205624287 := by
  unfold tailWord_2202072
  simp only [CollatzResearch.WordTrace]
  refine ⟨40158082039138351400568235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53544109385517801867424313 40158082039138351400568235)
  ·
    refine ⟨60237123058707527100852353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40158082039138351400568235 60237123058707527100852353)
    ·
      refine ⟨45177842294030645325639265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60237123058707527100852353 45177842294030645325639265)
      ·
        refine ⟨33883381720522983994229449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45177842294030645325639265 33883381720522983994229449)
        ·
          refine ⟨25412536290392237995672087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33883381720522983994229449 25412536290392237995672087)
          ·
            refine ⟨38118804435588356993508131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25412536290392237995672087 38118804435588356993508131)
            ·
              refine ⟨57178206653382535490262197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38118804435588356993508131 57178206653382535490262197)
              ·
                refine ⟨5360456873754612702212081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57178206653382535490262197 5360456873754612702212081)
                ·
                  refine ⟨4020342655315959526659061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5360456873754612702212081 4020342655315959526659061)
                  ·
                    refine ⟨376907123935871205624287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4020342655315959526659061 376907123935871205624287)
                    ·
                      rfl

theorem cell23_2202072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_2202072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202072 prefixEnd_2202072 := by exact prefixLift 2202072
  have htrace : WordTrace (prefixWord ++ tailWord_2202072) baseStart_2202072 baseEnd_2202072 := by
    simpa [prefixWord, tailWord_2202072, baseEnd_2202072] using wordTrace_append hprefix tailTrace_2202072
  have hstable : (prefixWord ++ tailWord_2202072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202072).length < 2 ^ (prefixWord ++ tailWord_2202072).sum := by decide
  have hdescent : baseEnd_2202072 < baseStart_2202072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202093 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2202093 : Nat := 118140960795 + 2202093 * 2 ^ 59
def prefixEnd_2202093 : Nat := 4983230072969 + 3 ^ 40 * 2202093 * 2
def baseEnd_2202093 : Nat := 125636906100150892745585

theorem tailTrace_2202093 : CollatzResearch.WordTrace tailWord_2202093 prefixEnd_2202093 125636906100150892745585 := by
  unfold tailWord_2202093
  simp only [CollatzResearch.WordTrace]
  refine ⟨80316930011200623387650933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53544620007467082258433955 80316930011200623387650933)
  ·
    refine ⟨7529712188550058442592275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80316930011200623387650933 7529712188550058442592275)
    ·
      refine ⟨11294568282825087663888413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529712188550058442592275 11294568282825087663888413)
      ·
        refine ⟨4235463106059407873958155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11294568282825087663888413 4235463106059407873958155)
        ·
          refine ⟨6353194659089111810937233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235463106059407873958155 6353194659089111810937233)
          ·
            refine ⟨4764895994316833858202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6353194659089111810937233 4764895994316833858202925)
            ·
              refine ⟨1786835997868812696826097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4764895994316833858202925 1786835997868812696826097)
              ·
                refine ⟨1340126998401609522619573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786835997868812696826097 1340126998401609522619573)
                ·
                  refine ⟨125636906100150892745585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340126998401609522619573 125636906100150892745585)
                  ·
                    rfl

theorem cell23_2202093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2202093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202093 prefixEnd_2202093 := by exact prefixLift 2202093
  have htrace : WordTrace (prefixWord ++ tailWord_2202093) baseStart_2202093 baseEnd_2202093 := by
    simpa [prefixWord, tailWord_2202093, baseEnd_2202093] using wordTrace_append hprefix tailTrace_2202093
  have hstable : (prefixWord ++ tailWord_2202093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202093).length < 2 ^ (prefixWord ++ tailWord_2202093).sum := by decide
  have hdescent : baseEnd_2202093 < baseStart_2202093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202109 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_2202109 : Nat := 118140960795 + 2202109 * 2 ^ 59
def prefixEnd_2202109 : Nat := 4983230072969 + 3 ^ 40 * 2202109 * 2
def baseEnd_2202109 : Nat := 1130740370591829972110191

theorem tailTrace_2202109 : CollatzResearch.WordTrace tailWord_2202109 prefixEnd_2202109 1130740370591829972110191 := by
  unfold tailWord_2202109
  simp only [CollatzResearch.WordTrace]
  refine ⟨80317513579142658120233381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53545009052761772080155587 80317513579142658120233381)
  ·
    refine ⟨15059533796089248397543759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80317513579142658120233381 15059533796089248397543759)
    ·
      refine ⟨22589300694133872596315639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15059533796089248397543759 22589300694133872596315639)
      ·
        refine ⟨33883951041200808894473459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22589300694133872596315639 33883951041200808894473459)
        ·
          refine ⟨50825926561801213341710189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33883951041200808894473459 50825926561801213341710189)
          ·
            refine ⟨19059722460675455003141321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50825926561801213341710189 19059722460675455003141321)
            ·
              refine ⟨14294791845506591252355991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19059722460675455003141321 14294791845506591252355991)
              ·
                refine ⟨21442187768259886878533987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14294791845506591252355991 21442187768259886878533987)
                ·
                  refine ⟨32163281652389830317800981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21442187768259886878533987 32163281652389830317800981)
                  ·
                    refine ⟨1507653827455773296146921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32163281652389830317800981 1507653827455773296146921)
                    ·
                      refine ⟨1130740370591829972110191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507653827455773296146921 1130740370591829972110191)
                      ·
                        rfl

theorem cell23_2202109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_2202109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202109 prefixEnd_2202109 := by exact prefixLift 2202109
  have htrace : WordTrace (prefixWord ++ tailWord_2202109) baseStart_2202109 baseEnd_2202109 := by
    simpa [prefixWord, tailWord_2202109, baseEnd_2202109] using wordTrace_append hprefix tailTrace_2202109
  have hstable : (prefixWord ++ tailWord_2202109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202109).length < 2 ^ (prefixWord ++ tailWord_2202109).sum := by decide
  have hdescent : baseEnd_2202109 < baseStart_2202109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202126 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2202126 : Nat := 118140960795 + 2202126 * 2 ^ 59
def prefixEnd_2202126 : Nat := 4983230072969 + 3 ^ 40 * 2202126 * 2
def baseEnd_2202126 : Nat := 1130749099762956405597613

theorem tailTrace_2202126 : CollatzResearch.WordTrace tailWord_2202126 prefixEnd_2202126 1130749099762956405597613 := by
  unfold tailWord_2202126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039766702510133752950279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53545422413387380015734821 10039766702510133752950279)
  ·
    refine ⟨15059650053765200629425419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10039766702510133752950279 15059650053765200629425419)
    ·
      refine ⟨22589475080647800944138129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15059650053765200629425419 22589475080647800944138129)
      ·
        refine ⟨16942106310485850708103597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22589475080647800944138129 16942106310485850708103597)
        ·
          refine ⟨6353289866432194015538849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16942106310485850708103597 6353289866432194015538849)
          ·
            refine ⟨4764967399824145511654137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6353289866432194015538849 4764967399824145511654137)
            ·
              refine ⟨3573725549868109133740603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4764967399824145511654137 3573725549868109133740603)
              ·
                refine ⟨5360588324802163700610905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573725549868109133740603 5360588324802163700610905)
                ·
                  refine ⟨4020441243601622775458179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5360588324802163700610905 4020441243601622775458179)
                  ·
                    refine ⟨6030661865402434163187269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020441243601622775458179 6030661865402434163187269)
                    ·
                      refine ⟨1130749099762956405597613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6030661865402434163187269 1130749099762956405597613)
                      ·
                        rfl

theorem cell23_2202126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2202126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202126 prefixEnd_2202126 := by exact prefixLift 2202126
  have htrace : WordTrace (prefixWord ++ tailWord_2202126) baseStart_2202126 baseEnd_2202126 := by
    simpa [prefixWord, tailWord_2202126, baseEnd_2202126] using wordTrace_append hprefix tailTrace_2202126
  have hstable : (prefixWord ++ tailWord_2202126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202126).length < 2 ^ (prefixWord ++ tailWord_2202126).sum := by decide
  have hdescent : baseEnd_2202126 < baseStart_2202126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202159 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_2202159 : Nat := 118140960795 + 2202159 * 2 ^ 59
def prefixEnd_2202159 : Nat := 4983230072969 + 3 ^ 40 * 2202159 * 2
def baseEnd_2202159 : Nat := 1130766044624554776484961

theorem tailTrace_2202159 : CollatzResearch.WordTrace tailWord_2202159 prefixEnd_2202159 1130766044624554776484961 := by
  unfold tailWord_2202159
  simp only [CollatzResearch.WordTrace]
  refine ⟨80319337228961516659553531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53546224819307677773035687 80319337228961516659553531)
  ·
    refine ⟨120479005843442274989330297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80319337228961516659553531 120479005843442274989330297)
    ·
      refine ⟨90359254382581706241997723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120479005843442274989330297 90359254382581706241997723)
      ·
        refine ⟨135538881573872559362996585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90359254382581706241997723 135538881573872559362996585)
        ·
          refine ⟨101654161180404419522247439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135538881573872559362996585 101654161180404419522247439)
          ·
            refine ⟨152481241770606629283371159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101654161180404419522247439 152481241770606629283371159)
            ·
              refine ⟨228721862655909943925056739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152481241770606629283371159 228721862655909943925056739)
              ·
                refine ⟨343082793983864915887585109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228721862655909943925056739 343082793983864915887585109)
                ·
                  refine ⟨2010250745999208491528819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 343082793983864915887585109 2010250745999208491528819)
                  ·
                    refine ⟨3015376118998812737293229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010250745999208491528819 3015376118998812737293229)
                    ·
                      refine ⟨1130766044624554776484961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015376118998812737293229 1130766044624554776484961)
                      ·
                        rfl

theorem cell23_2202159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_2202159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202159 prefixEnd_2202159 := by exact prefixLift 2202159
  have htrace : WordTrace (prefixWord ++ tailWord_2202159) baseStart_2202159 baseEnd_2202159 := by
    simpa [prefixWord, tailWord_2202159, baseEnd_2202159] using wordTrace_append hprefix tailTrace_2202159
  have hstable : (prefixWord ++ tailWord_2202159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202159).length < 2 ^ (prefixWord ++ tailWord_2202159).sum := by decide
  have hdescent : baseEnd_2202159 < baseStart_2202159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202166 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2202166 : Nat := 118140960795 + 2202166 * 2 ^ 59
def prefixEnd_2202166 : Nat := 4983230072969 + 3 ^ 40 * 2202166 * 2
def baseEnd_2202166 : Nat := 125641070998792916566381

theorem tailTrace_2202166 : CollatzResearch.WordTrace tailWord_2202166 prefixEnd_2202166 125641070998792916566381 := by
  unfold tailWord_2202166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019974533746009803441147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53546395026624104570038901 5019974533746009803441147)
  ·
    refine ⟨7529961800619014705161721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019974533746009803441147 7529961800619014705161721)
    ·
      refine ⟨5647471350464261028871291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7529961800619014705161721 5647471350464261028871291)
      ·
        refine ⟨8471207025696391543306937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5647471350464261028871291 8471207025696391543306937)
        ·
          refine ⟨6353405269272293657480203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8471207025696391543306937 6353405269272293657480203)
          ·
            refine ⟨9530107903908440486220305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353405269272293657480203 9530107903908440486220305)
            ·
              refine ⟨7147580927931330364665229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9530107903908440486220305 7147580927931330364665229)
              ·
                refine ⟨2680342847974248886749461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7147580927931330364665229 2680342847974248886749461)
                ·
                  refine ⟨125641070998792916566381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2680342847974248886749461 125641070998792916566381)
                  ·
                    rfl

theorem cell23_2202166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2202166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202166 prefixEnd_2202166 := by exact prefixLift 2202166
  have htrace : WordTrace (prefixWord ++ tailWord_2202166) baseStart_2202166 baseEnd_2202166 := by
    simpa [prefixWord, tailWord_2202166, baseEnd_2202166] using wordTrace_append hprefix tailTrace_2202166
  have hstable : (prefixWord ++ tailWord_2202166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202166).length < 2 ^ (prefixWord ++ tailWord_2202166).sum := by decide
  have hdescent : baseEnd_2202166 < baseStart_2202166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202180 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2202180 : Nat := 118140960795 + 2202180 * 2 ^ 59
def prefixEnd_2202180 : Nat := 4983230072969 + 3 ^ 40 * 2202180 * 2
def baseEnd_2202180 : Nat := 1130776827718299194322365

theorem tailTrace_2202180 : CollatzResearch.WordTrace tailWord_2202180 prefixEnd_2202180 1130776827718299194322365 := by
  unfold tailWord_2202180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160051580942718623033997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53546735441256958164045329 40160051580942718623033997)
  ·
    refine ⟨15060019342853519483637749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40160051580942718623033997 15060019342853519483637749)
    ·
      refine ⟨1411876813392517451591039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15060019342853519483637749 1411876813392517451591039)
      ·
        refine ⟨2117815220088776177386559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411876813392517451591039 2117815220088776177386559)
        ·
          refine ⟨3176722830133164266079839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117815220088776177386559 3176722830133164266079839)
          ·
            refine ⟨4765084245199746399119759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176722830133164266079839 4765084245199746399119759)
            ·
              refine ⟨7147626367799619598679639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765084245199746399119759 7147626367799619598679639)
              ·
                refine ⟨10721439551699429398019459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147626367799619598679639 10721439551699429398019459)
                ·
                  refine ⟨16082159327549144097029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10721439551699429398019459 16082159327549144097029189)
                  ·
                    refine ⟨3015404873915464518192973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16082159327549144097029189 3015404873915464518192973)
                    ·
                      refine ⟨1130776827718299194322365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015404873915464518192973 1130776827718299194322365)
                      ·
                        rfl

theorem cell23_2202180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2202180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202180 prefixEnd_2202180 := by exact prefixLift 2202180
  have htrace : WordTrace (prefixWord ++ tailWord_2202180) baseStart_2202180 baseEnd_2202180 := by
    simpa [prefixWord, tailWord_2202180, baseEnd_2202180] using wordTrace_append hprefix tailTrace_2202180
  have hstable : (prefixWord ++ tailWord_2202180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202180).length < 2 ^ (prefixWord ++ tailWord_2202180).sum := by decide
  have hdescent : baseEnd_2202180 < baseStart_2202180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202186 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_2202186 : Nat := 118140960795 + 2202186 * 2 ^ 59
def prefixEnd_2202186 : Nat := 4983230072969 + 3 ^ 40 * 2202186 * 2
def baseEnd_2202186 : Nat := 1130779908602226170847337

theorem tailTrace_2202186 : CollatzResearch.WordTrace tailWord_2202186 prefixEnd_2202186 1130779908602226170847337 := by
  unfold tailWord_2202186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20080080499965925067696603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53546881333242466847190941 20080080499965925067696603)
  ·
    refine ⟨30120120749948887601544905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20080080499965925067696603 30120120749948887601544905)
    ·
      refine ⟨22590090562461665701158679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30120120749948887601544905 22590090562461665701158679)
      ·
        refine ⟨33885135843692498551738019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22590090562461665701158679 33885135843692498551738019)
        ·
          refine ⟨50827703765538747827607029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33885135843692498551738019 50827703765538747827607029)
          ·
            refine ⟨4765097228019257608838159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50827703765538747827607029 4765097228019257608838159)
            ·
              refine ⟨7147645842028886413257239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765097228019257608838159 7147645842028886413257239)
              ·
                refine ⟨10721468763043329619885859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147645842028886413257239 10721468763043329619885859)
                ·
                  refine ⟨16082203144564994429828789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10721468763043329619885859 16082203144564994429828789)
                  ·
                    refine ⟨1507706544802968227796449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16082203144564994429828789 1507706544802968227796449)
                    ·
                      refine ⟨1130779908602226170847337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507706544802968227796449 1130779908602226170847337)
                      ·
                        rfl

theorem cell23_2202186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_2202186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202186 prefixEnd_2202186 := by exact prefixLift 2202186
  have htrace : WordTrace (prefixWord ++ tailWord_2202186) baseStart_2202186 baseEnd_2202186 := by
    simpa [prefixWord, tailWord_2202186, baseEnd_2202186] using wordTrace_append hprefix tailTrace_2202186
  have hstable : (prefixWord ++ tailWord_2202186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202186).length < 2 ^ (prefixWord ++ tailWord_2202186).sum := by decide
  have hdescent : baseEnd_2202186 < baseStart_2202186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202192 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_2202192 : Nat := 118140960795 + 2202192 * 2 ^ 59
def prefixEnd_2202192 : Nat := 4983230072969 + 3 ^ 40 * 2202192 * 2
def baseEnd_2202192 : Nat := 376927663162051049124103

theorem tailTrace_2202192 : CollatzResearch.WordTrace tailWord_2202192 prefixEnd_2202192 376927663162051049124103 := by
  unfold tailWord_2202192
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160270418920981647752415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53547027225227975530336553 40160270418920981647752415)
  ·
    refine ⟨60240405628381472471628623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40160270418920981647752415 60240405628381472471628623)
    ·
      refine ⟨90360608442572208707442935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60240405628381472471628623 90360608442572208707442935)
      ·
        refine ⟨135540912663858313061164403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90360608442572208707442935 135540912663858313061164403)
        ·
          refine ⟨203311368995787469591746605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135540912663858313061164403 203311368995787469591746605)
          ·
            refine ⟨76241763373420301096904977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203311368995787469591746605 76241763373420301096904977)
            ·
              refine ⟨57181322530065225822678733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76241763373420301096904977 57181322530065225822678733)
              ·
                refine ⟨21442995948774459683504525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57181322530065225822678733 21442995948774459683504525)
                ·
                  refine ⟨8041123480790422381314197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21442995948774459683504525 8041123480790422381314197)
                  ·
                    refine ⟨376927663162051049124103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8041123480790422381314197 376927663162051049124103)
                    ·
                      rfl

theorem cell23_2202192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_2202192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202192 prefixEnd_2202192 := by exact prefixLift 2202192
  have htrace : WordTrace (prefixWord ++ tailWord_2202192) baseStart_2202192 baseEnd_2202192 := by
    simpa [prefixWord, tailWord_2202192, baseEnd_2202192] using wordTrace_append hprefix tailTrace_2202192
  have hstable : (prefixWord ++ tailWord_2202192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202192).length < 2 ^ (prefixWord ++ tailWord_2202192).sum := by decide
  have hdescent : baseEnd_2202192 < baseStart_2202192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202193 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_2202193 : Nat := 118140960795 + 2202193 * 2 ^ 59
def prefixEnd_2202193 : Nat := 4983230072969 + 3 ^ 40 * 2202193 * 2
def baseEnd_2202193 : Nat := 1130783502966807643459805

theorem tailTrace_2202193 : CollatzResearch.WordTrace tailWord_2202193 prefixEnd_2202193 1130783502966807643459805 := by
  unfold tailWord_2202193
  simp only [CollatzResearch.WordTrace]
  refine ⟨80320577310838340466291233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53547051540558893644194155 80320577310838340466291233)
  ·
    refine ⟨60240432983128755349718425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80320577310838340466291233 60240432983128755349718425)
    ·
      refine ⟨45180324737346566512288819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60240432983128755349718425 45180324737346566512288819)
      ·
        refine ⟨67770487106019849768433229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45180324737346566512288819 67770487106019849768433229)
        ·
          refine ⟨25413932664757443663162461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67770487106019849768433229 25413932664757443663162461)
          ·
            refine ⟨9530224749284041373685923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25413932664757443663162461 9530224749284041373685923)
            ·
              refine ⟨14295337123926062060528885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9530224749284041373685923 14295337123926062060528885)
              ·
                refine ⟨1340187855368068318174583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14295337123926062060528885 1340187855368068318174583)
                ·
                  refine ⟨2010281783052102477261875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340187855368068318174583 2010281783052102477261875)
                  ·
                    refine ⟨3015422674578153715892813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010281783052102477261875 3015422674578153715892813)
                    ·
                      refine ⟨1130783502966807643459805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015422674578153715892813 1130783502966807643459805)
                      ·
                        rfl

theorem cell23_2202193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_2202193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202193 prefixEnd_2202193 := by exact prefixLift 2202193
  have htrace : WordTrace (prefixWord ++ tailWord_2202193) baseStart_2202193 baseEnd_2202193 := by
    simpa [prefixWord, tailWord_2202193, baseEnd_2202193] using wordTrace_append hprefix tailTrace_2202193
  have hstable : (prefixWord ++ tailWord_2202193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202193).length < 2 ^ (prefixWord ++ tailWord_2202193).sum := by decide
  have hdescent : baseEnd_2202193 < baseStart_2202193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202196 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2202196 : Nat := 118140960795 + 2202196 * 2 ^ 59
def prefixEnd_2202196 : Nat := 4983230072969 + 3 ^ 40 * 2202196 * 2
def baseEnd_2202196 : Nat := 376928347802923710574097

theorem tailTrace_2202196 : CollatzResearch.WordTrace tailWord_2202196 prefixEnd_2202196 376928347802923710574097 := by
  unfold tailWord_2202196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160343364913735989325221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53547124486551647985766961 40160343364913735989325221)
  ·
    refine ⟨7530064380921325497998479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40160343364913735989325221 7530064380921325497998479)
    ·
      refine ⟨11295096571381988246997719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7530064380921325497998479 11295096571381988246997719)
      ·
        refine ⟨16942644857072982370496579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11295096571381988246997719 16942644857072982370496579)
        ·
          refine ⟨25413967285609473555744869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16942644857072982370496579 25413967285609473555744869)
          ·
            refine ⟨4765118866051776291702163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25413967285609473555744869 4765118866051776291702163)
            ·
              refine ⟨7147678299077664437553245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765118866051776291702163 7147678299077664437553245)
              ·
                refine ⟨2680379362154124164082467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7147678299077664437553245 2680379362154124164082467)
                ·
                  refine ⟨4020569043231186246123701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680379362154124164082467 4020569043231186246123701)
                  ·
                    refine ⟨376928347802923710574097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4020569043231186246123701 376928347802923710574097)
                    ·
                      rfl

theorem cell23_2202196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2202196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202196 prefixEnd_2202196 := by exact prefixLift 2202196
  have htrace : WordTrace (prefixWord ++ tailWord_2202196) baseStart_2202196 baseEnd_2202196 := by
    simpa [prefixWord, tailWord_2202196, baseEnd_2202196] using wordTrace_append hprefix tailTrace_2202196
  have hstable : (prefixWord ++ tailWord_2202196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202196).length < 2 ^ (prefixWord ++ tailWord_2202196).sum := by decide
  have hdescent : baseEnd_2202196 < baseStart_2202196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202219 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3]
def baseStart_2202219 : Nat := 118140960795 + 2202219 * 2 ^ 59
def prefixEnd_2202219 : Nat := 4983230072969 + 3 ^ 40 * 2202219 * 2
def baseEnd_2202219 : Nat := 1130796853463824541734685

theorem tailTrace_2202219 : CollatzResearch.WordTrace tailWord_2202219 prefixEnd_2202219 1130796853463824541734685 := by
  unfold tailWord_2202219
  simp only [CollatzResearch.WordTrace]
  refine ⟨80321525608744146906737711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53547683739162764604491807 80321525608744146906737711)
  ·
    refine ⟨120482288413116220360106567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80321525608744146906737711 120482288413116220360106567)
    ·
      refine ⟨180723432619674330540159851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120482288413116220360106567 180723432619674330540159851)
      ·
        refine ⟨271085148929511495810239777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180723432619674330540159851 271085148929511495810239777)
        ·
          refine ⟨203313861697133621857679833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271085148929511495810239777 203313861697133621857679833)
          ·
            refine ⟨152485396272850216393259875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203313861697133621857679833 152485396272850216393259875)
            ·
              refine ⟨228728094409275324589889813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152485396272850216393259875 228728094409275324589889813)
              ·
                refine ⟨10721629425434780840151085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228728094409275324589889813 10721629425434780840151085)
                ·
                  refine ⟨4020611034538042815056657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10721629425434780840151085 4020611034538042815056657)
                  ·
                    refine ⟨3015458275903532111292493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020611034538042815056657 3015458275903532111292493)
                    ·
                      refine ⟨1130796853463824541734685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015458275903532111292493 1130796853463824541734685)
                      ·
                        rfl

theorem cell23_2202219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].length) (baseStart_2202219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202219 prefixEnd_2202219 := by exact prefixLift 2202219
  have htrace : WordTrace (prefixWord ++ tailWord_2202219) baseStart_2202219 baseEnd_2202219 := by
    simpa [prefixWord, tailWord_2202219, baseEnd_2202219] using wordTrace_append hprefix tailTrace_2202219
  have hstable : (prefixWord ++ tailWord_2202219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202219).length < 2 ^ (prefixWord ++ tailWord_2202219).sum := by decide
  have hdescent : baseEnd_2202219 < baseStart_2202219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2202232 : Nat := 118140960795 + 2202232 * 2 ^ 59
def prefixEnd_2202232 : Nat := 4983230072969 + 3 ^ 40 * 2202232 * 2
def baseEnd_2202232 : Nat := 1130803528712332990872125

theorem tailTrace_2202232 : CollatzResearch.WordTrace tailWord_2202232 prefixEnd_2202232 1130803528712332990872125 := by
  unfold tailWord_2202232
  simp only [CollatzResearch.WordTrace]
  refine ⟨40160999878848525063480475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53547999838464700084640633 40160999878848525063480475)
  ·
    refine ⟨60241499818272787595220713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40160999878848525063480475 60241499818272787595220713)
    ·
      refine ⟨45181124863704590696415535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60241499818272787595220713 45181124863704590696415535)
      ·
        refine ⟨67771687295556886044623303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45181124863704590696415535 67771687295556886044623303)
        ·
          refine ⟨101657530943335329066934955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67771687295556886044623303 101657530943335329066934955)
          ·
            refine ⟨152486296415002993600402433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101657530943335329066934955 152486296415002993600402433)
            ·
              refine ⟨114364722311252245200301825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152486296415002993600402433 114364722311252245200301825)
              ·
                refine ⟨85773541733439183900226369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114364722311252245200301825 85773541733439183900226369)
                ·
                  refine ⟨64330156300079387925169777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85773541733439183900226369 64330156300079387925169777)
                  ·
                    refine ⟨48247617225059540943877333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64330156300079387925169777 48247617225059540943877333)
                    ·
                      refine ⟨1130803528712332990872125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48247617225059540943877333 1130803528712332990872125)
                      ·
                        rfl

theorem cell23_2202232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2202232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202232 prefixEnd_2202232 := by exact prefixLift 2202232
  have htrace : WordTrace (prefixWord ++ tailWord_2202232) baseStart_2202232 baseEnd_2202232 := by
    simpa [prefixWord, tailWord_2202232, baseEnd_2202232] using wordTrace_append hprefix tailTrace_2202232
  have hstable : (prefixWord ++ tailWord_2202232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202232).length < 2 ^ (prefixWord ++ tailWord_2202232).sum := by decide
  have hdescent : baseEnd_2202232 < baseStart_2202232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202233 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 3, 2, 2]
def baseStart_2202233 : Nat := 118140960795 + 2202233 * 2 ^ 59
def prefixEnd_2202233 : Nat := 4983230072969 + 3 ^ 40 * 2202233 * 2
def baseEnd_2202233 : Nat := 1130804042192987486959621

theorem tailTrace_2202233 : CollatzResearch.WordTrace tailWord_2202233 prefixEnd_2202233 1130804042192987486959621 := by
  unfold tailWord_2202233
  simp only [CollatzResearch.WordTrace]
  refine ⟨80322036230693427297747353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53548024153795618198498235 80322036230693427297747353)
  ·
    refine ⟨60241527173020070473310515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80322036230693427297747353 60241527173020070473310515)
    ·
      refine ⟨90362290759530105709965773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60241527173020070473310515 90362290759530105709965773)
      ·
        refine ⟨33885859034823789641237165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90362290759530105709965773 33885859034823789641237165)
        ·
          refine ⟨12707197138058921115463937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33885859034823789641237165 12707197138058921115463937)
          ·
            refine ⟨9530397853544190836597953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12707197138058921115463937 9530397853544190836597953)
            ·
              refine ⟨7147798390158143127448465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9530397853544190836597953 7147798390158143127448465)
              ·
                refine ⟨5360848792618607345586349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7147798390158143127448465 5360848792618607345586349)
                ·
                  refine ⟨2010318297231977754594881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5360848792618607345586349 2010318297231977754594881)
                  ·
                    refine ⟨1507738722923983315946161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010318297231977754594881 1507738722923983315946161)
                    ·
                      refine ⟨1130804042192987486959621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507738722923983315946161 1130804042192987486959621)
                      ·
                        rfl

theorem cell23_2202233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_2202233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202233 prefixEnd_2202233 := by exact prefixLift 2202233
  have htrace : WordTrace (prefixWord ++ tailWord_2202233) baseStart_2202233 baseEnd_2202233 := by
    simpa [prefixWord, tailWord_2202233, baseEnd_2202233] using wordTrace_append hprefix tailTrace_2202233
  have hstable : (prefixWord ++ tailWord_2202233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202233).length < 2 ^ (prefixWord ++ tailWord_2202233).sum := by decide
  have hdescent : baseEnd_2202233 < baseStart_2202233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202236 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_2202236 : Nat := 118140960795 + 2202236 * 2 ^ 59
def prefixEnd_2202236 : Nat := 4983230072969 + 3 ^ 40 * 2202236 * 2
def baseEnd_2202236 : Nat := 1130805582634950975222107

theorem tailTrace_2202236 : CollatzResearch.WordTrace tailWord_2202236 prefixEnd_2202236 1130805582634950975222107 := by
  unfold tailWord_2202236
  simp only [CollatzResearch.WordTrace]
  refine ⟨40161072824841279405053281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53548097099788372540071041 40161072824841279405053281)
  ·
    refine ⟨30120804618630959553789961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40161072824841279405053281 30120804618630959553789961)
    ·
      refine ⟨22590603463973219665342471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30120804618630959553789961 22590603463973219665342471)
      ·
        refine ⟨33885905195959829498013707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22590603463973219665342471 33885905195959829498013707)
        ·
          refine ⟨50828857793939744247020561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33885905195959829498013707 50828857793939744247020561)
          ·
            refine ⟨38121643345454808185265421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50828857793939744247020561 38121643345454808185265421)
            ·
              refine ⟨14295616254545553069474533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38121643345454808185265421 14295616254545553069474533)
              ·
                refine ⟨2680428047727291200526475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14295616254545553069474533 2680428047727291200526475)
                ·
                  refine ⟨4020642071590936800789713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680428047727291200526475 4020642071590936800789713)
                  ·
                    refine ⟨3015481553693202600592285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020642071590936800789713 3015481553693202600592285)
                    ·
                      refine ⟨1130805582634950975222107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015481553693202600592285 1130805582634950975222107)
                      ·
                        rfl

theorem cell23_2202236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_2202236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202236 prefixEnd_2202236 := by exact prefixLift 2202236
  have htrace : WordTrace (prefixWord ++ tailWord_2202236) baseStart_2202236 baseEnd_2202236 := by
    simpa [prefixWord, tailWord_2202236, baseEnd_2202236] using wordTrace_append hprefix tailTrace_2202236
  have hstable : (prefixWord ++ tailWord_2202236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202236).length < 2 ^ (prefixWord ++ tailWord_2202236).sum := by decide
  have hdescent : baseEnd_2202236 < baseStart_2202236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202249 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_2202249 : Nat := 118140960795 + 2202249 * 2 ^ 59
def prefixEnd_2202249 : Nat := 4983230072969 + 3 ^ 40 * 2202249 * 2
def baseEnd_2202249 : Nat := 1130812257883459424359547

theorem tailTrace_2202249 : CollatzResearch.WordTrace tailWord_2202249 prefixEnd_2202249 1130812257883459424359547 := by
  unfold tailWord_2202249
  simp only [CollatzResearch.WordTrace]
  refine ⟨80322619798635462030329801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53548413199090308020219867 80322619798635462030329801)
  ·
    refine ⟨60241964848976596522747351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80322619798635462030329801 60241964848976596522747351)
    ·
      refine ⟨90362947273464894784121027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60241964848976596522747351 90362947273464894784121027)
      ·
        refine ⟨135544420910197342176181541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90362947273464894784121027 135544420910197342176181541)
        ·
          refine ⟨25414578920662001658034039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135544420910197342176181541 25414578920662001658034039)
          ·
            refine ⟨38121868380993002487051059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25414578920662001658034039 38121868380993002487051059)
            ·
              refine ⟨57182802571489503730576589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38121868380993002487051059 57182802571489503730576589)
              ·
                refine ⟨21443550964308563898966221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57182802571489503730576589 21443550964308563898966221)
                ·
                  refine ⟨8041331611615711462112333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21443550964308563898966221 8041331611615711462112333)
                  ·
                    refine ⟨3015499354355891798292125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8041331611615711462112333 3015499354355891798292125)
                    ·
                      refine ⟨1130812257883459424359547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015499354355891798292125 1130812257883459424359547)
                      ·
                        rfl

theorem cell23_2202249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_2202249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202249 prefixEnd_2202249 := by exact prefixLift 2202249
  have htrace : WordTrace (prefixWord ++ tailWord_2202249) baseStart_2202249 baseEnd_2202249 := by
    simpa [prefixWord, tailWord_2202249, baseEnd_2202249] using wordTrace_append hprefix tailTrace_2202249
  have hstable : (prefixWord ++ tailWord_2202249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202249).length < 2 ^ (prefixWord ++ tailWord_2202249).sum := by decide
  have hdescent : baseEnd_2202249 < baseStart_2202249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202309 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_2202309 : Nat := 118140960795 + 2202309 * 2 ^ 59
def prefixEnd_2202309 : Nat := 4983230072969 + 3 ^ 40 * 2202309 * 2
def baseEnd_2202309 : Nat := 1130843066722729189609271

theorem tailTrace_2202309 : CollatzResearch.WordTrace tailWord_2202309 prefixEnd_2202309 1130843066722729189609271 := by
  unfold tailWord_2202309
  simp only [CollatzResearch.WordTrace]
  refine ⟨80324808178418092277513981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53549872118945394851675987 80324808178418092277513981)
  ·
    refine ⟨30121803066906784604067743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80324808178418092277513981 30121803066906784604067743)
    ·
      refine ⟨45182704600360176906101615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30121803066906784604067743 45182704600360176906101615)
      ·
        refine ⟨67774056900540265359152423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45182704600360176906101615 67774056900540265359152423)
        ·
          refine ⟨101661085350810398038728635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67774056900540265359152423 101661085350810398038728635)
          ·
            refine ⟨152491628026215597058092953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101661085350810398038728635 152491628026215597058092953)
            ·
              refine ⟨114368721019661697793569715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152491628026215597058092953 114368721019661697793569715)
              ·
                refine ⟨171553081529492546690354573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114368721019661697793569715 171553081529492546690354573)
                ·
                  refine ⟨64332405573559705008882965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171553081529492546690354573 64332405573559705008882965)
                  ·
                    refine ⟨3015581511260611172291389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64332405573559705008882965 3015581511260611172291389)
                    ·
                      refine ⟨1130843066722729189609271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015581511260611172291389 1130843066722729189609271)
                      ·
                        rfl

theorem cell23_2202309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_2202309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202309 prefixEnd_2202309 := by exact prefixLift 2202309
  have htrace : WordTrace (prefixWord ++ tailWord_2202309) baseStart_2202309 baseEnd_2202309 := by
    simpa [prefixWord, tailWord_2202309, baseEnd_2202309] using wordTrace_append hprefix tailTrace_2202309
  have hstable : (prefixWord ++ tailWord_2202309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202309).length < 2 ^ (prefixWord ++ tailWord_2202309).sum := by decide
  have hdescent : baseEnd_2202309 < baseStart_2202309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202329 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 7]
def baseStart_2202329 : Nat := 118140960795 + 2202329 * 2 ^ 59
def prefixEnd_2202329 : Nat := 4983230072969 + 3 ^ 40 * 2202329 * 2
def baseEnd_2202329 : Nat := 125650370703979901262131

theorem tailTrace_2202329 : CollatzResearch.WordTrace tailWord_2202329 prefixEnd_2202329 125650370703979901262131 := by
  unfold tailWord_2202329
  simp only [CollatzResearch.WordTrace]
  refine ⟨80325537638345635693242041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53550358425563757128828027 80325537638345635693242041)
  ·
    refine ⟨60244153228759226769931531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80325537638345635693242041 60244153228759226769931531)
    ·
      refine ⟨90366229843138840154897297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60244153228759226769931531 90366229843138840154897297)
      ·
        refine ⟨67774672382354130116172973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90366229843138840154897297 67774672382354130116172973)
        ·
          refine ⟨25415502143382798793564865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67774672382354130116172973 25415502143382798793564865)
          ·
            refine ⟨19061626607537099095173649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25415502143382798793564865 19061626607537099095173649)
            ·
              refine ⟨14296219955652824321380237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19061626607537099095173649 14296219955652824321380237)
              ·
                refine ⟨5361082483369809120517589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14296219955652824321380237 5361082483369809120517589)
                ·
                  refine ⟨125650370703979901262131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5361082483369809120517589 125650370703979901262131)
                  ·
                    rfl

theorem cell23_2202329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_2202329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202329 prefixEnd_2202329 := by exact prefixLift 2202329
  have htrace : WordTrace (prefixWord ++ tailWord_2202329) baseStart_2202329 baseEnd_2202329 := by
    simpa [prefixWord, tailWord_2202329, baseEnd_2202329] using wordTrace_append hprefix tailTrace_2202329
  have hstable : (prefixWord ++ tailWord_2202329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202329).length < 2 ^ (prefixWord ++ tailWord_2202329).sum := by decide
  have hdescent : baseEnd_2202329 < baseStart_2202329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202340 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_2202340 : Nat := 118140960795 + 2202340 * 2 ^ 59
def prefixEnd_2202340 : Nat := 4983230072969 + 3 ^ 40 * 2202340 * 2
def baseEnd_2202340 : Nat := 1130858984623018568321629

theorem tailTrace_2202340 : CollatzResearch.WordTrace tailWord_2202340 prefixEnd_2202340 1130858984623018568321629 := by
  unfold tailWord_2202340
  simp only [CollatzResearch.WordTrace]
  refine ⟨40162969420652892285946237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53550625894203856381261649 40162969420652892285946237)
  ·
    refine ⟨15061113532744834607229839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40162969420652892285946237 15061113532744834607229839)
    ·
      refine ⟨22591670299117251910844759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15061113532744834607229839 22591670299117251910844759)
      ·
        refine ⟨33887505448675877866267139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22591670299117251910844759 33887505448675877866267139)
        ·
          refine ⟨50831258173013816799400709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33887505448675877866267139 50831258173013816799400709)
          ·
            refine ⟨9530860907440090649887633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50831258173013816799400709 9530860907440090649887633)
            ·
              refine ⟨7148145680580067987415725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9530860907440090649887633 7148145680580067987415725)
              ·
                refine ⟨2680554630217525495280897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7148145680580067987415725 2680554630217525495280897)
                ·
                  refine ⟨2010415972663144121460673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2680554630217525495280897 2010415972663144121460673)
                  ·
                    refine ⟨1507811979497358091095505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010415972663144121460673 1507811979497358091095505)
                    ·
                      refine ⟨1130858984623018568321629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507811979497358091095505 1130858984623018568321629)
                      ·
                        rfl

theorem cell23_2202340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_2202340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202340 prefixEnd_2202340 := by exact prefixLift 2202340
  have htrace : WordTrace (prefixWord ++ tailWord_2202340) baseStart_2202340 baseEnd_2202340 := by
    simpa [prefixWord, tailWord_2202340, baseEnd_2202340] using wordTrace_append hprefix tailTrace_2202340
  have hstable : (prefixWord ++ tailWord_2202340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202340).length < 2 ^ (prefixWord ++ tailWord_2202340).sum := by decide
  have hdescent : baseEnd_2202340 < baseStart_2202340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202396 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2202396 : Nat := 118140960795 + 2202396 * 2 ^ 59
def prefixEnd_2202396 : Nat := 4983230072969 + 3 ^ 40 * 2202396 * 2
def baseEnd_2202396 : Nat := 1130887739539670349221371

theorem tailTrace_2202396 : CollatzResearch.WordTrace tailWord_2202396 prefixEnd_2202396 1130887739539670349221371 := by
  unfold tailWord_2202396
  simp only [CollatzResearch.WordTrace]
  refine ⟨40163990664551453067965521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53551987552735270757287361 40163990664551453067965521)
  ·
    refine ⟨30122992998413589800974141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40163990664551453067965521 30122992998413589800974141)
    ·
      refine ⟨11296122374405096175365303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30122992998413589800974141 11296122374405096175365303)
      ·
        refine ⟨16944183561607644263047955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11296122374405096175365303 16944183561607644263047955)
        ·
          refine ⟨25416275342411466394571933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16944183561607644263047955 25416275342411466394571933)
          ·
            refine ⟨9531103253404299897964475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25416275342411466394571933 9531103253404299897964475)
            ·
              refine ⟨14296654880106449846946713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531103253404299897964475 14296654880106449846946713)
              ·
                refine ⟨10722491160079837385210035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14296654880106449846946713 10722491160079837385210035)
                ·
                  refine ⟨16083736740119756077815053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10722491160079837385210035 16083736740119756077815053)
                  ·
                    refine ⟨6031401277544908529180645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16083736740119756077815053 6031401277544908529180645)
                    ·
                      refine ⟨1130887739539670349221371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6031401277544908529180645 1130887739539670349221371)
                      ·
                        rfl

theorem cell23_2202396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2202396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202396 prefixEnd_2202396 := by exact prefixLift 2202396
  have htrace : WordTrace (prefixWord ++ tailWord_2202396) baseStart_2202396 baseEnd_2202396 := by
    simpa [prefixWord, tailWord_2202396, baseEnd_2202396] using wordTrace_append hprefix tailTrace_2202396
  have hstable : (prefixWord ++ tailWord_2202396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202396).length < 2 ^ (prefixWord ++ tailWord_2202396).sum := by decide
  have hdescent : baseEnd_2202396 < baseStart_2202396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202409 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_2202409 : Nat := 118140960795 + 2202409 * 2 ^ 59
def prefixEnd_2202409 : Nat := 4983230072969 + 3 ^ 40 * 2202409 * 2
def baseEnd_2202409 : Nat := 1130894414788178798358811

theorem tailTrace_2202409 : CollatzResearch.WordTrace tailWord_2202409 prefixEnd_2202409 1130894414788178798358811 := by
  unfold tailWord_2202409
  simp only [CollatzResearch.WordTrace]
  refine ⟨80328455478055809356154281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53552303652037206237436187 80328455478055809356154281)
  ·
    refine ⟨60246341608541857017115711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80328455478055809356154281 60246341608541857017115711)
    ·
      refine ⟨90369512412812785525673567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60246341608541857017115711 90369512412812785525673567)
      ·
        refine ⟨135554268619219178288510351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90369512412812785525673567 135554268619219178288510351)
        ·
          refine ⟨203331402928828767432765527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135554268619219178288510351 203331402928828767432765527)
          ·
            refine ⟨304997104393243151149148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203331402928828767432765527 304997104393243151149148291)
            ·
              refine ⟨457495656589864726723722437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304997104393243151149148291 457495656589864726723722437)
              ·
                refine ⟨85780435610599636260697957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457495656589864726723722437 85780435610599636260697957)
                ·
                  refine ⟨16083831676987431798880867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85780435610599636260697957 16083831676987431798880867)
                  ·
                    refine ⟨24125747515481147698321301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16083831676987431798880867 24125747515481147698321301)
                    ·
                      refine ⟨1130894414788178798358811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24125747515481147698321301 1130894414788178798358811)
                      ·
                        rfl

theorem cell23_2202409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_2202409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202409 prefixEnd_2202409 := by exact prefixLift 2202409
  have htrace : WordTrace (prefixWord ++ tailWord_2202409) baseStart_2202409 baseEnd_2202409 := by
    simpa [prefixWord, tailWord_2202409, baseEnd_2202409] using wordTrace_append hprefix tailTrace_2202409
  have hstable : (prefixWord ++ tailWord_2202409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202409).length < 2 ^ (prefixWord ++ tailWord_2202409).sum := by decide
  have hdescent : baseEnd_2202409 < baseStart_2202409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202416 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_2202416 : Nat := 118140960795 + 2202416 * 2 ^ 59
def prefixEnd_2202416 : Nat := 4983230072969 + 3 ^ 40 * 2202416 * 2
def baseEnd_2202416 : Nat := 1130898009152760270971279

theorem tailTrace_2202416 : CollatzResearch.WordTrace tailWord_2202416 prefixEnd_2202416 1130898009152760270971279 := by
  unfold tailWord_2202416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40164355394515224775829551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53552473859353633034439401 40164355394515224775829551)
  ·
    refine ⟨60246533091772837163744327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40164355394515224775829551 60246533091772837163744327)
    ·
      refine ⟨90369799637659255745616491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60246533091772837163744327 90369799637659255745616491)
      ·
        refine ⟨135554699456488883618424737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90369799637659255745616491 135554699456488883618424737)
        ·
          refine ⟨101666024592366662713818553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135554699456488883618424737 101666024592366662713818553)
          ·
            refine ⟨76249518444274997035363915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101666024592366662713818553 76249518444274997035363915)
            ·
              refine ⟨114374277666412495553045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76249518444274997035363915 114374277666412495553045873)
              ·
                refine ⟨85780708249809371664784405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114374277666412495553045873 85780708249809371664784405)
                ·
                  refine ⟨4020970699209814296786769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85780708249809371664784405 4020970699209814296786769)
                  ·
                    refine ⟨3015728024407360722590077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4020970699209814296786769 3015728024407360722590077)
                    ·
                      refine ⟨1130898009152760270971279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015728024407360722590077 1130898009152760270971279)
                      ·
                        rfl

theorem cell23_2202416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_2202416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202416 prefixEnd_2202416 := by exact prefixLift 2202416
  have htrace : WordTrace (prefixWord ++ tailWord_2202416) baseStart_2202416 baseEnd_2202416 := by
    simpa [prefixWord, tailWord_2202416, baseEnd_2202416] using wordTrace_append hprefix tailTrace_2202416
  have hstable : (prefixWord ++ tailWord_2202416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202416).length < 2 ^ (prefixWord ++ tailWord_2202416).sum := by decide
  have hdescent : baseEnd_2202416 < baseStart_2202416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202430 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2202430 : Nat := 118140960795 + 2202430 * 2 ^ 59
def prefixEnd_2202430 : Nat := 4983230072969 + 3 ^ 40 * 2202430 * 2
def baseEnd_2202430 : Nat := 1130905197881923216196215

theorem tailTrace_2202430 : CollatzResearch.WordTrace tailWord_2202430 prefixEnd_2202430 1130905197881923216196215 := by
  unfold tailWord_2202430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041152676372466242833593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53552814273986486628445829 10041152676372466242833593)
  ·
    refine ⟨7530864507279349682125195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10041152676372466242833593 7530864507279349682125195)
    ·
      refine ⟨11296296760919024523187793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7530864507279349682125195 11296296760919024523187793)
      ·
        refine ⟨8472222570689268392390845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11296296760919024523187793 8472222570689268392390845)
        ·
          refine ⟨3177083464008475647146567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8472222570689268392390845 3177083464008475647146567)
          ·
            refine ⟨4765625196012713470719851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177083464008475647146567 4765625196012713470719851)
            ·
              refine ⟨7148437794019070206079777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765625196012713470719851 7148437794019070206079777)
              ·
                refine ⟨5361328345514302654559833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7148437794019070206079777 5361328345514302654559833)
                ·
                  refine ⟨4020996259135726990919875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361328345514302654559833 4020996259135726990919875)
                  ·
                    refine ⟨6031494388703590486379813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020996259135726990919875 6031494388703590486379813)
                    ·
                      refine ⟨1130905197881923216196215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6031494388703590486379813 1130905197881923216196215)
                      ·
                        rfl

theorem cell23_2202430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2202430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202430 prefixEnd_2202430 := by exact prefixLift 2202430
  have htrace : WordTrace (prefixWord ++ tailWord_2202430) baseStart_2202430 baseEnd_2202430 := by
    simpa [prefixWord, tailWord_2202430, baseEnd_2202430] using wordTrace_append hprefix tailTrace_2202430
  have hstable : (prefixWord ++ tailWord_2202430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202430).length < 2 ^ (prefixWord ++ tailWord_2202430).sum := by decide
  have hdescent : baseEnd_2202430 < baseStart_2202430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202463 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2202463 : Nat := 118140960795 + 2202463 * 2 ^ 59
def prefixEnd_2202463 : Nat := 4983230072969 + 3 ^ 40 * 2202463 * 2
def baseEnd_2202463 : Nat := 1130922142743521587083563

theorem tailTrace_2202463 : CollatzResearch.WordTrace tailWord_2202463 prefixEnd_2202463 1130922142743521587083563 := by
  unfold tailWord_2202463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80330425019860176578620043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53553616679906784385746695 80330425019860176578620043)
  ·
    refine ⟨120495637529790264867930065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80330425019860176578620043 120495637529790264867930065)
    ·
      refine ⟨90371728147342698650947549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120495637529790264867930065 90371728147342698650947549)
      ·
        refine ⟨33889398055253511994105331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90371728147342698650947549 33889398055253511994105331)
        ·
          refine ⟨50834097082880267991157997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33889398055253511994105331 50834097082880267991157997)
          ·
            refine ⟨19062786406080100496684249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50834097082880267991157997 19062786406080100496684249)
            ·
              refine ⟨14297089804560075372513187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19062786406080100496684249 14297089804560075372513187)
              ·
                refine ⟨21445634706840113058769781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14297089804560075372513187 21445634706840113058769781)
                ·
                  refine ⟨2010528253766260599259667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21445634706840113058769781 2010528253766260599259667)
                  ·
                    refine ⟨3015792380649390898889501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010528253766260599259667 3015792380649390898889501)
                    ·
                      refine ⟨1130922142743521587083563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3015792380649390898889501 1130922142743521587083563)
                      ·
                        rfl

theorem cell23_2202463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2202463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202463 prefixEnd_2202463 := by exact prefixLift 2202463
  have htrace : WordTrace (prefixWord ++ tailWord_2202463) baseStart_2202463 baseEnd_2202463 := by
    simpa [prefixWord, tailWord_2202463, baseEnd_2202463] using wordTrace_append hprefix tailTrace_2202463
  have hstable : (prefixWord ++ tailWord_2202463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202463).length < 2 ^ (prefixWord ++ tailWord_2202463).sum := by decide
  have hdescent : baseEnd_2202463 < baseStart_2202463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202503 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2202503 : Nat := 118140960795 + 2202503 * 2 ^ 59
def prefixEnd_2202503 : Nat := 4983230072969 + 3 ^ 40 * 2202503 * 2
def baseEnd_2202503 : Nat := 1130942681969701430583379

theorem tailTrace_2202503 : CollatzResearch.WordTrace tailWord_2202503 prefixEnd_2202503 1130942681969701430583379 := by
  unfold tailWord_2202503
  simp only [CollatzResearch.WordTrace]
  refine ⟨80331883939715263410076163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53554589293143508940050775 80331883939715263410076163)
  ·
    refine ⟨120497825909572895115114245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80331883939715263410076163 120497825909572895115114245)
    ·
      refine ⟨22593342358044917834083921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120497825909572895115114245 22593342358044917834083921)
      ·
        refine ⟨16945006768533688375562941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22593342358044917834083921 16945006768533688375562941)
        ·
          refine ⟨6354377538200133140836103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16945006768533688375562941 6354377538200133140836103)
          ·
            refine ⟨9531566307300199711254155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354377538200133140836103 9531566307300199711254155)
            ·
              refine ⟨14297349460950299566881233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9531566307300199711254155 14297349460950299566881233)
              ·
                refine ⟨10723012095712724675160925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14297349460950299566881233 10723012095712724675160925)
                ·
                  refine ⟨4021129535892271753185347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10723012095712724675160925 4021129535892271753185347)
                  ·
                    refine ⟨6031694303838407629778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4021129535892271753185347 6031694303838407629778021)
                    ·
                      refine ⟨1130942681969701430583379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6031694303838407629778021 1130942681969701430583379)
                      ·
                        rfl

theorem cell23_2202503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2202503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202503 prefixEnd_2202503 := by exact prefixLift 2202503
  have htrace : WordTrace (prefixWord ++ tailWord_2202503) baseStart_2202503 baseEnd_2202503 := by
    simpa [prefixWord, tailWord_2202503, baseEnd_2202503] using wordTrace_append hprefix tailTrace_2202503
  have hstable : (prefixWord ++ tailWord_2202503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202503).length < 2 ^ (prefixWord ++ tailWord_2202503).sum := by decide
  have hdescent : baseEnd_2202503 < baseStart_2202503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202524 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2202524 : Nat := 118140960795 + 2202524 * 2 ^ 59
def prefixEnd_2202524 : Nat := 4983230072969 + 3 ^ 40 * 2202524 * 2
def baseEnd_2202524 : Nat := 1130953465063445848420783

theorem tailTrace_2202524 : CollatzResearch.WordTrace tailWord_2202524 prefixEnd_2202524 1130953465063445848420783 := by
  unfold tailWord_2202524
  simp only [CollatzResearch.WordTrace]
  refine ⟨40166324936319591998295313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53555099915092789331060417 40166324936319591998295313)
  ·
    refine ⟨30124743702239693998721485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40166324936319591998295313 30124743702239693998721485)
    ·
      refine ⟨11296778888339885249520557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30124743702239693998721485 11296778888339885249520557)
      ·
        refine ⟨4236292083127456968570209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11296778888339885249520557 4236292083127456968570209)
        ·
          refine ⟨3177219062345592726427657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4236292083127456968570209 3177219062345592726427657)
          ·
            refine ⟨2382914296759194544820743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3177219062345592726427657 2382914296759194544820743)
            ·
              refine ⟨3574371445138791817231115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382914296759194544820743 3574371445138791817231115)
              ·
                refine ⟨5361557167708187725846673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574371445138791817231115 5361557167708187725846673)
                ·
                  refine ⟨4021167875781140794385005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361557167708187725846673 4021167875781140794385005)
                  ·
                    refine ⟨1507937953417927797894377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4021167875781140794385005 1507937953417927797894377)
                    ·
                      refine ⟨1130953465063445848420783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1507937953417927797894377 1130953465063445848420783)
                      ·
                        rfl

theorem cell23_2202524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2202524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202524 prefixEnd_2202524 := by exact prefixLift 2202524
  have htrace : WordTrace (prefixWord ++ tailWord_2202524) baseStart_2202524 baseEnd_2202524 := by
    simpa [prefixWord, tailWord_2202524, baseEnd_2202524] using wordTrace_append hprefix tailTrace_2202524
  have hstable : (prefixWord ++ tailWord_2202524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202524).length < 2 ^ (prefixWord ++ tailWord_2202524).sum := by decide
  have hdescent : baseEnd_2202524 < baseStart_2202524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202546 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2202546 : Nat := 118140960795 + 2202546 * 2 ^ 59
def prefixEnd_2202546 : Nat := 4983230072969 + 3 ^ 40 * 2202546 * 2
def baseEnd_2202546 : Nat := 1130964761637844762345681

theorem tailTrace_2202546 : CollatzResearch.WordTrace tailWord_2202546 prefixEnd_2202546 1130964761637844762345681 := by
  unfold tailWord_2202546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083363069639870438472873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53555634852372987835927661 20083363069639870438472873)
  ·
    refine ⟨15062522302229902828854655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20083363069639870438472873 15062522302229902828854655)
    ·
      refine ⟨22593783453344854243281983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062522302229902828854655 22593783453344854243281983)
      ·
        refine ⟨33890675180017281364922975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22593783453344854243281983 33890675180017281364922975)
        ·
          refine ⟨50836012770025922047384463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33890675180017281364922975 50836012770025922047384463)
          ·
            refine ⟨76254019155038883071076695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50836012770025922047384463 76254019155038883071076695)
            ·
              refine ⟨114381028732558324606615043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76254019155038883071076695 114381028732558324606615043)
              ·
                refine ⟨171571543098837486909922565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114381028732558324606615043 171571543098837486909922565)
                ·
                  refine ⟨32169664331032028795610481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171571543098837486909922565 32169664331032028795610481)
                  ·
                    refine ⟨24127248248274021596707861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32169664331032028795610481 24127248248274021596707861)
                    ·
                      refine ⟨1130964761637844762345681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24127248248274021596707861 1130964761637844762345681)
                      ·
                        rfl

theorem cell23_2202546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2202546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202546 prefixEnd_2202546 := by exact prefixLift 2202546
  have htrace : WordTrace (prefixWord ++ tailWord_2202546) baseStart_2202546 baseEnd_2202546 := by
    simpa [prefixWord, tailWord_2202546, baseEnd_2202546] using wordTrace_append hprefix tailTrace_2202546
  have hstable : (prefixWord ++ tailWord_2202546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202546).length < 2 ^ (prefixWord ++ tailWord_2202546).sum := by decide
  have hdescent : baseEnd_2202546 < baseStart_2202546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202564 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2202564 : Nat := 118140960795 + 2202564 * 2 ^ 59
def prefixEnd_2202564 : Nat := 4983230072969 + 3 ^ 40 * 2202564 * 2
def baseEnd_2202564 : Nat := 376991334763208563973533

theorem tailTrace_2202564 : CollatzResearch.WordTrace tailWord_2202564 prefixEnd_2202564 376991334763208563973533 := by
  unfold tailWord_2202564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40167054396247135414023373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53556072528329513885364497 40167054396247135414023373)
  ·
    refine ⟨15062645398592675780258765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40167054396247135414023373 15062645398592675780258765)
    ·
      refine ⟨5648492024472253417597037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15062645398592675780258765 5648492024472253417597037)
      ·
        refine ⟨2118184509177095031598889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5648492024472253417597037 2118184509177095031598889)
        ·
          refine ⟨1588638381882821273699167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118184509177095031598889 1588638381882821273699167)
          ·
            refine ⟨2382957572824231910548751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588638381882821273699167 2382957572824231910548751)
            ·
              refine ⟨3574436359236347865823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382957572824231910548751 3574436359236347865823127)
              ·
                refine ⟨5361654538854521798734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574436359236347865823127 5361654538854521798734691)
                ·
                  refine ⟨8042481808281782698102037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5361654538854521798734691 8042481808281782698102037)
                  ·
                    refine ⟨376991334763208563973533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8042481808281782698102037 376991334763208563973533)
                    ·
                      rfl

theorem cell23_2202564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2202564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202564 prefixEnd_2202564 := by exact prefixLift 2202564
  have htrace : WordTrace (prefixWord ++ tailWord_2202564) baseStart_2202564 baseEnd_2202564 := by
    simpa [prefixWord, tailWord_2202564, baseEnd_2202564] using wordTrace_append hprefix tailTrace_2202564
  have hstable : (prefixWord ++ tailWord_2202564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202564).length < 2 ^ (prefixWord ++ tailWord_2202564).sum := by decide
  have hdescent : baseEnd_2202564 < baseStart_2202564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202643 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3]
def baseStart_2202643 : Nat := 118140960795 + 2202643 * 2 ^ 59
def prefixEnd_2202643 : Nat := 4983230072969 + 3 ^ 40 * 2202643 * 2
def baseEnd_2202643 : Nat := 1131014569261330882832735

theorem tailTrace_2202643 : CollatzResearch.WordTrace tailWord_2202643 prefixEnd_2202643 1131014569261330882832735 := by
  unfold tailWord_2202643
  simp only [CollatzResearch.WordTrace]
  refine ⟨80336990159208067320172583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53557993439472044880115055 80336990159208067320172583)
  ·
    refine ⟨120505485238812100980258875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80336990159208067320172583 120505485238812100980258875)
    ·
      refine ⟨180758227858218151470388313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120505485238812100980258875 180758227858218151470388313)
      ·
        refine ⟨135568670893663613602791235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180758227858218151470388313 135568670893663613602791235)
        ·
          refine ⟨203353006340495420404186853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135568670893663613602791235 203353006340495420404186853)
          ·
            refine ⟨38128688688842891325785035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203353006340495420404186853 38128688688842891325785035)
            ·
              refine ⟨57193033033264336988677553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38128688688842891325785035 57193033033264336988677553)
              ·
                refine ⟨42894774774948252741508165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57193033033264336988677553 42894774774948252741508165)
                ·
                  refine ⟨8042770270302797389032781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42894774774948252741508165 8042770270302797389032781)
                  ·
                    refine ⟨3016038851363549020887293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8042770270302797389032781 3016038851363549020887293)
                    ·
                      refine ⟨1131014569261330882832735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016038851363549020887293 1131014569261330882832735)
                      ·
                        rfl

theorem cell23_2202643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_2202643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202643 prefixEnd_2202643 := by exact prefixLift 2202643
  have htrace : WordTrace (prefixWord ++ tailWord_2202643) baseStart_2202643 baseEnd_2202643 := by
    simpa [prefixWord, tailWord_2202643, baseEnd_2202643] using wordTrace_append hprefix tailTrace_2202643
  have hstable : (prefixWord ++ tailWord_2202643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202643).length < 2 ^ (prefixWord ++ tailWord_2202643).sum := by decide
  have hdescent : baseEnd_2202643 < baseStart_2202643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202650 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_2202650 : Nat := 118140960795 + 2202650 * 2 ^ 59
def prefixEnd_2202650 : Nat := 4983230072969 + 3 ^ 40 * 2202650 * 2
def baseEnd_2202650 : Nat := 125668684847323595049467

theorem tailTrace_2202650 : CollatzResearch.WordTrace tailWord_2202650 prefixEnd_2202650 125668684847323595049467 := by
  unfold tailWord_2202650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20084311367545676878919351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53558163646788471677118269 20084311367545676878919351)
  ·
    refine ⟨30126467051318515318379027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20084311367545676878919351 30126467051318515318379027)
    ·
      refine ⟨45189700576977772977568541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30126467051318515318379027 45189700576977772977568541)
      ·
        refine ⟨16946137716366664866588203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45189700576977772977568541 16946137716366664866588203)
        ·
          refine ⟨25419206574549997299882305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946137716366664866588203 25419206574549997299882305)
          ·
            refine ⟨19064404930912497974911729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25419206574549997299882305 19064404930912497974911729)
            ·
              refine ⟨14298303698184373481183797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19064404930912497974911729 14298303698184373481183797)
              ·
                refine ⟨1340465971704785013860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14298303698184373481183797 1340465971704785013860981)
                ·
                  refine ⟨125668684847323595049467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340465971704785013860981 125668684847323595049467)
                  ·
                    rfl

theorem cell23_2202650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_2202650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202650 prefixEnd_2202650 := by exact prefixLift 2202650
  have htrace : WordTrace (prefixWord ++ tailWord_2202650) baseStart_2202650 baseEnd_2202650 := by
    simpa [prefixWord, tailWord_2202650, baseEnd_2202650] using wordTrace_append hprefix tailTrace_2202650
  have hstable : (prefixWord ++ tailWord_2202650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202650).length < 2 ^ (prefixWord ++ tailWord_2202650).sum := by decide
  have hdescent : baseEnd_2202650 < baseStart_2202650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202673 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2202673 : Nat := 118140960795 + 2202673 * 2 ^ 59
def prefixEnd_2202673 : Nat := 4983230072969 + 3 ^ 40 * 2202673 * 2
def baseEnd_2202673 : Nat := 1131029973680965765457597

theorem tailTrace_2202673 : CollatzResearch.WordTrace tailWord_2202673 prefixEnd_2202673 1131029973680965765457597 := by
  unfold tailWord_2202673
  simp only [CollatzResearch.WordTrace]
  refine ⟨80338084349099382443764673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53558722899399588295843115 80338084349099382443764673)
  ·
    refine ⟨60253563261824536832823505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80338084349099382443764673 60253563261824536832823505)
    ·
      refine ⟨45190172446368402624617629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60253563261824536832823505 45190172446368402624617629)
      ·
        refine ⟨16946314667388150984231611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45190172446368402624617629 16946314667388150984231611)
        ·
          refine ⟨25419472001082226476347417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946314667388150984231611 25419472001082226476347417)
          ·
            refine ⟨19064604000811669857260563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25419472001082226476347417 19064604000811669857260563)
            ·
              refine ⟨28596906001217504785890845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19064604000811669857260563 28596906001217504785890845)
              ·
                refine ⟨10723839750456564294709067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28596906001217504785890845 10723839750456564294709067)
                ·
                  refine ⟨16085759625684846442063601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10723839750456564294709067 16085759625684846442063601)
                  ·
                    refine ⟨12064319719263634831547701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16085759625684846442063601 12064319719263634831547701)
                    ·
                      refine ⟨1131029973680965765457597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12064319719263634831547701 1131029973680965765457597)
                      ·
                        rfl

theorem cell23_2202673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2202673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202673 prefixEnd_2202673 := by exact prefixLift 2202673
  have htrace : WordTrace (prefixWord ++ tailWord_2202673) baseStart_2202673 baseEnd_2202673 := by
    simpa [prefixWord, tailWord_2202673, baseEnd_2202673] using wordTrace_append hprefix tailTrace_2202673
  have hstable : (prefixWord ++ tailWord_2202673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202673).length < 2 ^ (prefixWord ++ tailWord_2202673).sum := by decide
  have hdescent : baseEnd_2202673 < baseStart_2202673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202700 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2202700 : Nat := 118140960795 + 2202700 * 2 ^ 59
def prefixEnd_2202700 : Nat := 4983230072969 + 3 ^ 40 * 2202700 * 2
def baseEnd_2202700 : Nat := 1131043837658637159819973

theorem tailTrace_2202700 : CollatzResearch.WordTrace tailWord_2202700 prefixEnd_2202700 1131043837658637159819973 := by
  unfold tailWord_2202700
  simp only [CollatzResearch.WordTrace]
  refine ⟨40169534560000783027498777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53559379413334377369998369 40169534560000783027498777)
  ·
    refine ⟨30127150920000587270624083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40169534560000783027498777 30127150920000587270624083)
    ·
      refine ⟨45190726380000880905936125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30127150920000587270624083 45190726380000880905936125)
      ·
        refine ⟨16946522392500330339726047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45190726380000880905936125 16946522392500330339726047)
        ·
          refine ⟨25419783588750495509589071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946522392500330339726047 25419783588750495509589071)
          ·
            refine ⟨38129675383125743264383607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25419783588750495509589071 38129675383125743264383607)
            ·
              refine ⟨57194513074688614896575411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38129675383125743264383607 57194513074688614896575411)
              ·
                refine ⟨85791769612032922344863117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57194513074688614896575411 85791769612032922344863117)
                ·
                  refine ⟨32171913604512345879323669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85791769612032922344863117 32171913604512345879323669)
                  ·
                    refine ⟨1508058450211516213093297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32171913604512345879323669 1508058450211516213093297)
                    ·
                      refine ⟨1131043837658637159819973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508058450211516213093297 1131043837658637159819973)
                      ·
                        rfl

theorem cell23_2202700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2202700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202700 prefixEnd_2202700 := by exact prefixLift 2202700
  have htrace : WordTrace (prefixWord ++ tailWord_2202700) baseStart_2202700 baseEnd_2202700 := by
    simpa [prefixWord, tailWord_2202700, baseEnd_2202700] using wordTrace_append hprefix tailTrace_2202700
  have hstable : (prefixWord ++ tailWord_2202700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202700).length < 2 ^ (prefixWord ++ tailWord_2202700).sum := by decide
  have hdescent : baseEnd_2202700 < baseStart_2202700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202720 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2202720 : Nat := 118140960795 + 2202720 * 2 ^ 59
def prefixEnd_2202720 : Nat := 4983230072969 + 3 ^ 40 * 2202720 * 2
def baseEnd_2202720 : Nat := 1131054107271727081569881

theorem tailTrace_2202720 : CollatzResearch.WordTrace tailWord_2202720 prefixEnd_2202720 1131054107271727081569881 := by
  unfold tailWord_2202720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40169899289964554735362807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53559865719952739647150409 40169899289964554735362807)
  ·
    refine ⟨60254848934946832103044211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40169899289964554735362807 60254848934946832103044211)
    ·
      refine ⟨90382273402420248154566317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60254848934946832103044211 90382273402420248154566317)
      ·
        refine ⟨33893352525907593057962369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90382273402420248154566317 33893352525907593057962369)
        ·
          refine ⟨25420014394430694793471777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33893352525907593057962369 25420014394430694793471777)
          ·
            refine ⟨19065010795823021095103833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25420014394430694793471777 19065010795823021095103833)
            ·
              refine ⟨14298758096867265821327875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19065010795823021095103833 14298758096867265821327875)
              ·
                refine ⟨21448137145300898731991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14298758096867265821327875 21448137145300898731991813)
                ·
                  refine ⟨4021525714743918512248465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21448137145300898731991813 4021525714743918512248465)
                  ·
                    refine ⟨3016144286057938884186349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021525714743918512248465 3016144286057938884186349)
                    ·
                      refine ⟨1131054107271727081569881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016144286057938884186349 1131054107271727081569881)
                      ·
                        rfl

theorem cell23_2202720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2202720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202720 prefixEnd_2202720 := by exact prefixLift 2202720
  have htrace : WordTrace (prefixWord ++ tailWord_2202720) baseStart_2202720 baseEnd_2202720 := by
    simpa [prefixWord, tailWord_2202720, baseEnd_2202720] using wordTrace_append hprefix tailTrace_2202720
  have hstable : (prefixWord ++ tailWord_2202720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202720).length < 2 ^ (prefixWord ++ tailWord_2202720).sum := by decide
  have hdescent : baseEnd_2202720 < baseStart_2202720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202727 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2202727 : Nat := 118140960795 + 2202727 * 2 ^ 59
def prefixEnd_2202727 : Nat := 4983230072969 + 3 ^ 40 * 2202727 * 2
def baseEnd_2202727 : Nat := 377019233878769518060783

theorem tailTrace_2202727 : CollatzResearch.WordTrace tailWord_2202727 prefixEnd_2202727 377019233878769518060783 := by
  unfold tailWord_2202727
  simp only [CollatzResearch.WordTrace]
  refine ⟨80340053890903749666230435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53560035927269166444153623 80340053890903749666230435)
  ·
    refine ⟨120510080836355624499345653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80340053890903749666230435 120510080836355624499345653)
    ·
      refine ⟨11297820078408339796813655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120510080836355624499345653 11297820078408339796813655)
      ·
        refine ⟨16946730117612509695220483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11297820078408339796813655 16946730117612509695220483)
        ·
          refine ⟨25420095176418764542830725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16946730117612509695220483 25420095176418764542830725)
          ·
            refine ⟨4766267845578518351780761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25420095176418764542830725 4766267845578518351780761)
            ·
              refine ⟨3574700884183888763835571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4766267845578518351780761 3574700884183888763835571)
              ·
                refine ⟨5362051326275833145753357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574700884183888763835571 5362051326275833145753357)
                ·
                  refine ⟨2010769247353437429657509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5362051326275833145753357 2010769247353437429657509)
                  ·
                    refine ⟨377019233878769518060783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010769247353437429657509 377019233878769518060783)
                    ·
                      rfl

theorem cell23_2202727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2202727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202727 prefixEnd_2202727 := by exact prefixLift 2202727
  have htrace : WordTrace (prefixWord ++ tailWord_2202727) baseStart_2202727 baseEnd_2202727 := by
    simpa [prefixWord, tailWord_2202727, baseEnd_2202727] using wordTrace_append hprefix tailTrace_2202727
  have hstable : (prefixWord ++ tailWord_2202727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202727).length < 2 ^ (prefixWord ++ tailWord_2202727).sum := by decide
  have hdescent : baseEnd_2202727 < baseStart_2202727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202743 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_2202743 : Nat := 118140960795 + 2202743 * 2 ^ 59
def prefixEnd_2202743 : Nat := 4983230072969 + 3 ^ 40 * 2202743 * 2
def baseEnd_2202743 : Nat := 1131065917326780491582275

theorem tailTrace_2202743 : CollatzResearch.WordTrace tailWord_2202743 prefixEnd_2202743 1131065917326780491582275 := by
  unfold tailWord_2202743
  simp only [CollatzResearch.WordTrace]
  refine ⟨80340637458845784398812883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53560424972563856265875255 80340637458845784398812883)
  ·
    refine ⟨120510956188268676598219325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80340637458845784398812883 120510956188268676598219325)
    ·
      refine ⟨45191608570600753724332247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120510956188268676598219325 45191608570600753724332247)
      ·
        refine ⟨67787412855901130586498371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45191608570600753724332247 67787412855901130586498371)
        ·
          refine ⟨101681119283851695879747557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67787412855901130586498371 101681119283851695879747557)
          ·
            refine ⟨19065209865722192977452667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101681119283851695879747557 19065209865722192977452667)
            ·
              refine ⟨28597814798583289466179001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19065209865722192977452667 28597814798583289466179001)
              ·
                refine ⟨21448361098937467099634251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28597814798583289466179001 21448361098937467099634251)
                ·
                  refine ⟨32172541648406200649451377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21448361098937467099634251 32172541648406200649451377)
                  ·
                    refine ⟨24129406236304650487088533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32172541648406200649451377 24129406236304650487088533)
                    ·
                      refine ⟨1131065917326780491582275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24129406236304650487088533 1131065917326780491582275)
                      ·
                        rfl

theorem cell23_2202743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_2202743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202743 prefixEnd_2202743 := by exact prefixLift 2202743
  have htrace : WordTrace (prefixWord ++ tailWord_2202743) baseStart_2202743 baseEnd_2202743 := by
    simpa [prefixWord, tailWord_2202743, baseEnd_2202743] using wordTrace_append hprefix tailTrace_2202743
  have hstable : (prefixWord ++ tailWord_2202743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202743).length < 2 ^ (prefixWord ++ tailWord_2202743).sum := by decide
  have hdescent : baseEnd_2202743 < baseStart_2202743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202817 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2202817 : Nat := 118140960795 + 2202817 * 2 ^ 59
def prefixEnd_2202817 : Nat := 4983230072969 + 3 ^ 40 * 2202817 * 2
def baseEnd_2202817 : Nat := 377034638298404400685645

theorem tailTrace_2202817 : CollatzResearch.WordTrace tailWord_2202817 prefixEnd_2202817 377034638298404400685645 := by
  unfold tailWord_2202817
  simp only [CollatzResearch.WordTrace]
  refine ⟨80343336460577695037006705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53562224307051796691337803 80343336460577695037006705)
  ·
    refine ⟨60257502345433271277755029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80343336460577695037006705 60257502345433271277755029)
    ·
      refine ⟨2824570422442184591144767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60257502345433271277755029 2824570422442184591144767)
      ·
        refine ⟨4236855633663276886717151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824570422442184591144767 4236855633663276886717151)
        ·
          refine ⟨6355283450494915330075727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236855633663276886717151 6355283450494915330075727)
          ·
            refine ⟨9532925175742372995113591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355283450494915330075727 9532925175742372995113591)
            ·
              refine ⟨14299387763613559492670387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9532925175742372995113591 14299387763613559492670387)
              ·
                refine ⟨21449081645420339239005581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14299387763613559492670387 21449081645420339239005581)
                ·
                  refine ⟨8043405617032627214627093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21449081645420339239005581 8043405617032627214627093)
                  ·
                    refine ⟨377034638298404400685645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8043405617032627214627093 377034638298404400685645)
                    ·
                      rfl

theorem cell23_2202817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2202817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202817 prefixEnd_2202817 := by exact prefixLift 2202817
  have htrace : WordTrace (prefixWord ++ tailWord_2202817) baseStart_2202817 baseEnd_2202817 := by
    simpa [prefixWord, tailWord_2202817, baseEnd_2202817] using wordTrace_append hprefix tailTrace_2202817
  have hstable : (prefixWord ++ tailWord_2202817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202817).length < 2 ^ (prefixWord ++ tailWord_2202817).sum := by decide
  have hdescent : baseEnd_2202817 < baseStart_2202817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202830 : List Nat := [4, 1, 1, 1, 5, 11]
def baseStart_2202830 : Nat := 118140960795 + 2202830 * 2 ^ 59
def prefixEnd_2202830 : Nat := 4983230072969 + 3 ^ 40 * 2202830 * 2
def baseEnd_2202830 : Nat := 4654776091126426548125

theorem tailTrace_2202830 : CollatzResearch.WordTrace tailWord_2202830 prefixEnd_2202830 4654776091126426548125 := by
  unfold tailWord_2202830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042976326191324782153743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53562540406353732171486629 10042976326191324782153743)
  ·
    refine ⟨15064464489286987173230615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042976326191324782153743 15064464489286987173230615)
    ·
      refine ⟨22596696733930480759845923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15064464489286987173230615 22596696733930480759845923)
      ·
        refine ⟨33895045100895721139768885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22596696733930480759845923 33895045100895721139768885)
        ·
          refine ⟨3177660478208973856853333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33895045100895721139768885 3177660478208973856853333)
          ·
            refine ⟨4654776091126426548125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3177660478208973856853333 4654776091126426548125)
            ·
              rfl

theorem cell23_2202830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 11].length) (baseStart_2202830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202830 prefixEnd_2202830 := by exact prefixLift 2202830
  have htrace : WordTrace (prefixWord ++ tailWord_2202830) baseStart_2202830 baseEnd_2202830 := by
    simpa [prefixWord, tailWord_2202830, baseEnd_2202830] using wordTrace_append hprefix tailTrace_2202830
  have hstable : (prefixWord ++ tailWord_2202830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202830).length < 2 ^ (prefixWord ++ tailWord_2202830).sum := by decide
  have hdescent : baseEnd_2202830 < baseStart_2202830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202834 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2202834 : Nat := 118140960795 + 2202834 * 2 ^ 59
def prefixEnd_2202834 : Nat := 4983230072969 + 3 ^ 40 * 2202834 * 2
def baseEnd_2202834 : Nat := 377037548022113211848119

theorem tailTrace_2202834 : CollatzResearch.WordTrace tailWord_2202834 prefixEnd_2202834 377037548022113211848119 := by
  unfold tailWord_2202834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20085989125379026735093889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53562637667677404626917037 20085989125379026735093889)
  ·
    refine ⟨15064491844034270051320417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20085989125379026735093889 15064491844034270051320417)
    ·
      refine ⟨11298368883025702538490313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15064491844034270051320417 11298368883025702538490313)
      ·
        refine ⟨8473776662269276903867735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11298368883025702538490313 8473776662269276903867735)
        ·
          refine ⟨12710664993403915355801603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8473776662269276903867735 12710664993403915355801603)
          ·
            refine ⟨19065997490105873033702405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12710664993403915355801603 19065997490105873033702405)
            ·
              refine ⟨3574874529394851193819201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19065997490105873033702405 3574874529394851193819201)
              ·
                refine ⟨2681155897046138395364401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3574874529394851193819201 2681155897046138395364401)
                ·
                  refine ⟨2010866922784603796523301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681155897046138395364401 2010866922784603796523301)
                  ·
                    refine ⟨377037548022113211848119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010866922784603796523301 377037548022113211848119)
                    ·
                      rfl

theorem cell23_2202834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2202834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202834 prefixEnd_2202834 := by exact prefixLift 2202834
  have htrace : WordTrace (prefixWord ++ tailWord_2202834) baseStart_2202834 baseEnd_2202834 := by
    simpa [prefixWord, tailWord_2202834, baseEnd_2202834] using wordTrace_append hprefix tailTrace_2202834
  have hstable : (prefixWord ++ tailWord_2202834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202834).length < 2 ^ (prefixWord ++ tailWord_2202834).sum := by decide
  have hdescent : baseEnd_2202834 < baseStart_2202834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202878 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_2202878 : Nat := 118140960795 + 2202878 * 2 ^ 59
def prefixEnd_2202878 : Nat := 4983230072969 + 3 ^ 40 * 2202878 * 2
def baseEnd_2202878 : Nat := 1131135237215137463394155

theorem tailTrace_2202878 : CollatzResearch.WordTrace tailWord_2202878 prefixEnd_2202878 1131135237215137463394155 := by
  unfold tailWord_2202878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043195164169587806872161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53563707542237801636651525 10043195164169587806872161)
  ·
    refine ⟨7532396373127190855154121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10043195164169587806872161 7532396373127190855154121)
    ·
      refine ⟨5649297279845393141365591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7532396373127190855154121 5649297279845393141365591)
      ·
        refine ⟨8473945919768089712048387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649297279845393141365591 8473945919768089712048387)
        ·
          refine ⟨12710918879652134568072581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8473945919768089712048387 12710918879652134568072581)
          ·
            refine ⟨2383297289934775231513609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12710918879652134568072581 2383297289934775231513609)
            ·
              refine ⟨1787472967451081423635207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383297289934775231513609 1787472967451081423635207)
              ·
                refine ⟨2681209451176622135452811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787472967451081423635207 2681209451176622135452811)
                ·
                  refine ⟨4021814176764933203179217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681209451176622135452811 4021814176764933203179217)
                  ·
                    refine ⟨3016360632573699902384413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021814176764933203179217 3016360632573699902384413)
                    ·
                      refine ⟨1131135237215137463394155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016360632573699902384413 1131135237215137463394155)
                      ·
                        rfl

theorem cell23_2202878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_2202878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202878 prefixEnd_2202878 := by exact prefixLift 2202878
  have htrace : WordTrace (prefixWord ++ tailWord_2202878) baseStart_2202878 baseEnd_2202878 := by
    simpa [prefixWord, tailWord_2202878, baseEnd_2202878] using wordTrace_append hprefix tailTrace_2202878
  have hstable : (prefixWord ++ tailWord_2202878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202878).length < 2 ^ (prefixWord ++ tailWord_2202878).sum := by decide
  have hdescent : baseEnd_2202878 < baseStart_2202878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202891 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 3]
def baseStart_2202891 : Nat := 118140960795 + 2202891 * 2 ^ 59
def prefixEnd_2202891 : Nat := 4983230072969 + 3 ^ 40 * 2202891 * 2
def baseEnd_2202891 : Nat := 1131141912463645912531595

theorem tailTrace_2202891 : CollatzResearch.WordTrace tailWord_2202891 prefixEnd_2202891 1131141912463645912531595 := by
  unfold tailWord_2202891
  simp only [CollatzResearch.WordTrace]
  refine ⟨80346035462309605675200527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53564023641539737116800351 80346035462309605675200527)
  ·
    refine ⟨120519053193464408512800791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80346035462309605675200527 120519053193464408512800791)
    ·
      refine ⟨180778579790196612769201187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120519053193464408512800791 180778579790196612769201187)
      ·
        refine ⟨271167869685294919153801781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180778579790196612769201187 271167869685294919153801781)
        ·
          refine ⟨25421987782996398670668917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 271167869685294919153801781 25421987782996398670668917)
          ·
            refine ⟨2383311354655912375375211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25421987782996398670668917 2383311354655912375375211)
            ·
              refine ⟨3574967031983868563062817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383311354655912375375211 3574967031983868563062817)
              ·
                refine ⟨2681225273987901422297113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3574967031983868563062817 2681225273987901422297113)
                ·
                  refine ⟨2010918955490926066722835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681225273987901422297113 2010918955490926066722835)
                  ·
                    refine ⟨3016378433236389100084253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010918955490926066722835 3016378433236389100084253)
                    ·
                      refine ⟨1131141912463645912531595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016378433236389100084253 1131141912463645912531595)
                      ·
                        rfl

theorem cell23_2202891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 3].length) (baseStart_2202891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202891 prefixEnd_2202891 := by exact prefixLift 2202891
  have htrace : WordTrace (prefixWord ++ tailWord_2202891) baseStart_2202891 baseEnd_2202891 := by
    simpa [prefixWord, tailWord_2202891, baseEnd_2202891] using wordTrace_append hprefix tailTrace_2202891
  have hstable : (prefixWord ++ tailWord_2202891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202891).length < 2 ^ (prefixWord ++ tailWord_2202891).sum := by decide
  have hdescent : baseEnd_2202891 < baseStart_2202891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202948 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2202948 : Nat := 118140960795 + 2202948 * 2 ^ 59
def prefixEnd_2202948 : Nat := 4983230072969 + 3 ^ 40 * 2202948 * 2
def baseEnd_2202948 : Nat := 1131171180860952189518833

theorem tailTrace_2202948 : CollatzResearch.WordTrace tailWord_2202948 prefixEnd_2202948 1131171180860952189518833 := by
  unfold tailWord_2202948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40174057211551552205012749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53565409615402069606683665 40174057211551552205012749)
  ·
    refine ⟨15065271454331832076879781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40174057211551552205012749 15065271454331832076879781)
    ·
      refine ⟨2824738397687218514414959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15065271454331832076879781 2824738397687218514414959)
      ·
        refine ⟨4237107596530827771622439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824738397687218514414959 4237107596530827771622439)
        ·
          refine ⟨6355661394796241657433659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237107596530827771622439 6355661394796241657433659)
          ·
            refine ⟨9533492092194362486150489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355661394796241657433659 9533492092194362486150489)
            ·
              refine ⟨7150119069145771864612867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9533492092194362486150489 7150119069145771864612867)
              ·
                refine ⟨10725178603718657796919301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150119069145771864612867 10725178603718657796919301)
                ·
                  refine ⟨2010970988197248336922369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10725178603718657796919301 2010970988197248336922369)
                  ·
                    refine ⟨1508228241147936252691777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010970988197248336922369 1508228241147936252691777)
                    ·
                      refine ⟨1131171180860952189518833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508228241147936252691777 1131171180860952189518833)
                      ·
                        rfl

theorem cell23_2202948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2202948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202948 prefixEnd_2202948 := by exact prefixLift 2202948
  have htrace : WordTrace (prefixWord ++ tailWord_2202948) baseStart_2202948 baseEnd_2202948 := by
    simpa [prefixWord, tailWord_2202948, baseEnd_2202948] using wordTrace_append hprefix tailTrace_2202948
  have hstable : (prefixWord ++ tailWord_2202948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202948).length < 2 ^ (prefixWord ++ tailWord_2202948).sum := by decide
  have hdescent : baseEnd_2202948 < baseStart_2202948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2202965 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2202965 : Nat := 118140960795 + 2202965 * 2 ^ 59
def prefixEnd_2202965 : Nat := 4983230072969 + 3 ^ 40 * 2202965 * 2
def baseEnd_2202965 : Nat := 1131179910032078623006255

theorem tailTrace_2202965 : CollatzResearch.WordTrace tailWord_2202965 prefixEnd_2202965 1131179910032078623006255 := by
  unfold tailWord_2202965
  simp only [CollatzResearch.WordTrace]
  refine ⟨80348734464041516313394349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53565822976027677542262899 80348734464041516313394349)
  ·
    refine ⟨30130775424015568617522881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80348734464041516313394349 30130775424015568617522881)
    ·
      refine ⟨22598081568011676463142161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30130775424015568617522881 22598081568011676463142161)
      ·
        refine ⟨16948561176008757347356621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22598081568011676463142161 16948561176008757347356621)
        ·
          refine ⟨6355710441003284005258733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16948561176008757347356621 6355710441003284005258733)
          ·
            refine ⟨2383391415376231501972025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6355710441003284005258733 2383391415376231501972025)
            ·
              refine ⟨1787543561532173626479019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383391415376231501972025 1787543561532173626479019)
              ·
                refine ⟨2681315342298260439718529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787543561532173626479019 2681315342298260439718529)
                ·
                  refine ⟨2010986506723695329788897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681315342298260439718529 2010986506723695329788897)
                  ·
                    refine ⟨1508239880042771497341673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010986506723695329788897 1508239880042771497341673)
                    ·
                      refine ⟨1131179910032078623006255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508239880042771497341673 1131179910032078623006255)
                      ·
                        rfl

theorem cell23_2202965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2202965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2202965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2202965 prefixEnd_2202965 := by exact prefixLift 2202965
  have htrace : WordTrace (prefixWord ++ tailWord_2202965) baseStart_2202965 baseEnd_2202965 := by
    simpa [prefixWord, tailWord_2202965, baseEnd_2202965] using wordTrace_append hprefix tailTrace_2202965
  have hstable : (prefixWord ++ tailWord_2202965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2202965).length < 2 ^ (prefixWord ++ tailWord_2202965).sum := by decide
  have hdescent : baseEnd_2202965 < baseStart_2202965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2202965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203004 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_2203004 : Nat := 118140960795 + 2203004 * 2 ^ 59
def prefixEnd_2203004 : Nat := 4983230072969 + 3 ^ 40 * 2203004 * 2
def baseEnd_2203004 : Nat := 1131199935777603970418575

theorem tailTrace_2203004 : CollatzResearch.WordTrace tailWord_2203004 prefixEnd_2203004 1131199935777603970418575 := by
  unfold tailWord_2203004
  simp only [CollatzResearch.WordTrace]
  refine ⟨40175078455450112987032033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53566771273933483982709377 40175078455450112987032033)
  ·
    refine ⟨30131308841587584740274025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40175078455450112987032033 30131308841587584740274025)
    ·
      refine ⟨22598481631190688555205519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30131308841587584740274025 22598481631190688555205519)
      ·
        refine ⟨33897722446786032832808279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22598481631190688555205519 33897722446786032832808279)
        ·
          refine ⟨50846583670179049249212419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33897722446786032832808279 50846583670179049249212419)
          ·
            refine ⟨76269875505268573873818629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50846583670179049249212419 76269875505268573873818629)
            ·
              refine ⟨14300601657237857601340993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76269875505268573873818629 14300601657237857601340993)
              ·
                refine ⟨10725451242928393201005745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14300601657237857601340993 10725451242928393201005745)
                ·
                  refine ⟨8044088432196294900754309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10725451242928393201005745 8044088432196294900754309)
                  ·
                    refine ⟨1508266581036805293891433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8044088432196294900754309 1508266581036805293891433)
                    ·
                      refine ⟨1131199935777603970418575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508266581036805293891433 1131199935777603970418575)
                      ·
                        rfl

theorem cell23_2203004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_2203004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203004 prefixEnd_2203004 := by exact prefixLift 2203004
  have htrace : WordTrace (prefixWord ++ tailWord_2203004) baseStart_2203004 baseEnd_2203004 := by
    simpa [prefixWord, tailWord_2203004, baseEnd_2203004] using wordTrace_append hprefix tailTrace_2203004
  have hstable : (prefixWord ++ tailWord_2203004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203004).length < 2 ^ (prefixWord ++ tailWord_2203004).sum := by decide
  have hdescent : baseEnd_2203004 < baseStart_2203004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203061 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 6]
def baseStart_2203061 : Nat := 118140960795 + 2203061 * 2 ^ 59
def prefixEnd_2203061 : Nat := 4983230072969 + 3 ^ 40 * 2203061 * 2
def baseEnd_2203061 : Nat := 125692133797212249711757

theorem tailTrace_2203061 : CollatzResearch.WordTrace tailWord_2203061 prefixEnd_2203061 125692133797212249711757 := by
  unfold tailWord_2203061
  simp only [CollatzResearch.WordTrace]
  refine ⟨80352235871693724708889037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53568157247795816472592691 80352235871693724708889037)
  ·
    refine ⟨30132088451885146765833389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80352235871693724708889037 30132088451885146765833389)
    ·
      refine ⟨11299533169456930037187521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30132088451885146765833389 11299533169456930037187521)
      ·
        refine ⟨8474649877092697527890641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11299533169456930037187521 8474649877092697527890641)
        ·
          refine ⟨6355987407819523145917981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8474649877092697527890641 6355987407819523145917981)
          ·
            refine ⟨2383495277932321179719243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6355987407819523145917981 2383495277932321179719243)
            ·
              refine ⟨3575242916898481769578865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383495277932321179719243 3575242916898481769578865)
              ·
                refine ⟨2681432187673861327184149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575242916898481769578865 2681432187673861327184149)
                ·
                  refine ⟨125692133797212249711757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2681432187673861327184149 125692133797212249711757)
                  ·
                    rfl

theorem cell23_2203061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_2203061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203061 prefixEnd_2203061 := by exact prefixLift 2203061
  have htrace : WordTrace (prefixWord ++ tailWord_2203061) baseStart_2203061 baseEnd_2203061 := by
    simpa [prefixWord, tailWord_2203061, baseEnd_2203061] using wordTrace_append hprefix tailTrace_2203061
  have hstable : (prefixWord ++ tailWord_2203061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203061).length < 2 ^ (prefixWord ++ tailWord_2203061).sum := by decide
  have hdescent : baseEnd_2203061 < baseStart_2203061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203105 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_2203105 : Nat := 118140960795 + 2203105 * 2 ^ 59
def prefixEnd_2203105 : Nat := 4983230072969 + 3 ^ 40 * 2203105 * 2
def baseEnd_2203105 : Nat := 1131251797323708075255611

theorem tailTrace_2203105 : CollatzResearch.WordTrace tailWord_2203105 prefixEnd_2203105 1131251797323708075255611 := by
  unfold tailWord_2203105
  simp only [CollatzResearch.WordTrace]
  refine ⟨80353840683534320223490769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53569227122356213482327179 80353840683534320223490769)
  ·
    refine ⟨60265380512650740167618077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80353840683534320223490769 60265380512650740167618077)
    ·
      refine ⟨22599517692244027562856779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60265380512650740167618077 22599517692244027562856779)
      ·
        refine ⟨33899276538366041344285169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22599517692244027562856779 33899276538366041344285169)
        ·
          refine ⟨25424457403774531008213877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33899276538366041344285169 25424457403774531008213877)
          ·
            refine ⟨2383542881603862282020051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25424457403774531008213877 2383542881603862282020051)
            ·
              refine ⟨3575314322405793423030077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383542881603862282020051 3575314322405793423030077)
              ·
                refine ⟨1340742870902172533636279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3575314322405793423030077 1340742870902172533636279)
                ·
                  refine ⟨2011114306353258800454419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340742870902172533636279 2011114306353258800454419)
                  ·
                    refine ⟨3016671459529888200681629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011114306353258800454419 3016671459529888200681629)
                    ·
                      refine ⟨1131251797323708075255611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016671459529888200681629 1131251797323708075255611)
                      ·
                        rfl

theorem cell23_2203105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_2203105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203105 prefixEnd_2203105 := by exact prefixLift 2203105
  have htrace : WordTrace (prefixWord ++ tailWord_2203105) baseStart_2203105 baseEnd_2203105 := by
    simpa [prefixWord, tailWord_2203105, baseEnd_2203105] using wordTrace_append hprefix tailTrace_2203105
  have hstable : (prefixWord ++ tailWord_2203105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203105).length < 2 ^ (prefixWord ++ tailWord_2203105).sum := by decide
  have hdescent : baseEnd_2203105 < baseStart_2203105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203111 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2203111 : Nat := 118140960795 + 2203111 * 2 ^ 59
def prefixEnd_2203111 : Nat := 4983230072969 + 3 ^ 40 * 2203111 * 2
def baseEnd_2203111 : Nat := 1131254878207635051780583

theorem tailTrace_2203111 : CollatzResearch.WordTrace tailWord_2203111 prefixEnd_2203111 1131254878207635051780583 := by
  unfold tailWord_2203111
  simp only [CollatzResearch.WordTrace]
  refine ⟨80354059521512583248209187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53569373014341722165472791 80354059521512583248209187)
  ·
    refine ⟨120531089282268874872313781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80354059521512583248209187 120531089282268874872313781)
    ·
      refine ⟨11299789620212707019279417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120531089282268874872313781 11299789620212707019279417)
      ·
        refine ⟨8474842215159530264459563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11299789620212707019279417 8474842215159530264459563)
        ·
          refine ⟨12712263322739295396689345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8474842215159530264459563 12712263322739295396689345)
          ·
            refine ⟨9534197492054471547517009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12712263322739295396689345 9534197492054471547517009)
            ·
              refine ⟨7150648119040853660637757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9534197492054471547517009 7150648119040853660637757)
              ·
                refine ⟨2681493044640320122739159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7150648119040853660637757 2681493044640320122739159)
                ·
                  refine ⟨4022239566960480184108739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681493044640320122739159 4022239566960480184108739)
                  ·
                    refine ⟨6033359350440720276163109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4022239566960480184108739 6033359350440720276163109)
                    ·
                      refine ⟨1131254878207635051780583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6033359350440720276163109 1131254878207635051780583)
                      ·
                        rfl

theorem cell23_2203111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2203111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203111 prefixEnd_2203111 := by exact prefixLift 2203111
  have htrace : WordTrace (prefixWord ++ tailWord_2203111) baseStart_2203111 baseEnd_2203111 := by
    simpa [prefixWord, tailWord_2203111, baseEnd_2203111] using wordTrace_append hprefix tailTrace_2203111
  have hstable : (prefixWord ++ tailWord_2203111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203111).length < 2 ^ (prefixWord ++ tailWord_2203111).sum := by decide
  have hdescent : baseEnd_2203111 < baseStart_2203111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203122 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2203122 : Nat := 118140960795 + 2203122 * 2 ^ 59
def prefixEnd_2203122 : Nat := 4983230072969 + 3 ^ 40 * 2203122 * 2
def baseEnd_2203122 : Nat := 1131260526494834508743033

theorem tailTrace_2203122 : CollatzResearch.WordTrace tailWord_2203122 prefixEnd_2203122 1131260526494834508743033 := by
  unfold tailWord_2203122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20088615181118183031714905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53569640482981821417906413 20088615181118183031714905)
  ·
    refine ⟨15066461385838637273786179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20088615181118183031714905 15066461385838637273786179)
    ·
      refine ⟨22599692078757955910679269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15066461385838637273786179 22599692078757955910679269)
      ·
        refine ⟨4237442264767116733252363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22599692078757955910679269 4237442264767116733252363)
        ·
          refine ⟨6356163397150675099878545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237442264767116733252363 6356163397150675099878545)
          ·
            refine ⟨4767122547863006324908909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6356163397150675099878545 4767122547863006324908909)
            ·
              refine ⟨1787670955448627371840841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4767122547863006324908909 1787670955448627371840841)
              ·
                refine ⟨1340753216586470528880631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787670955448627371840841 1340753216586470528880631)
                ·
                  refine ⟨2011129824879705793320947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340753216586470528880631 2011129824879705793320947)
                  ·
                    refine ⟨3016694737319558689981421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011129824879705793320947 3016694737319558689981421)
                    ·
                      refine ⟨1131260526494834508743033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016694737319558689981421 1131260526494834508743033)
                      ·
                        rfl

theorem cell23_2203122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2203122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203122 prefixEnd_2203122 := by exact prefixLift 2203122
  have htrace : WordTrace (prefixWord ++ tailWord_2203122) baseStart_2203122 baseEnd_2203122 := by
    simpa [prefixWord, tailWord_2203122, baseEnd_2203122] using wordTrace_append hprefix tailTrace_2203122
  have hstable : (prefixWord ++ tailWord_2203122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203122).length < 2 ^ (prefixWord ++ tailWord_2203122).sum := by decide
  have hdescent : baseEnd_2203122 < baseStart_2203122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203128 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_2203128 : Nat := 118140960795 + 2203128 * 2 ^ 59
def prefixEnd_2203128 : Nat := 4983230072969 + 3 ^ 40 * 2203128 * 2
def baseEnd_2203128 : Nat := 1131263607378761485268005

theorem tailTrace_2203128 : CollatzResearch.WordTrace tailWord_2203128 prefixEnd_2203128 1131263607378761485268005 := by
  unfold tailWord_2203128
  simp only [CollatzResearch.WordTrace]
  refine ⟨40177339781225497575789019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53569786374967330101052025 40177339781225497575789019)
  ·
    refine ⟨60266009671838246363683529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40177339781225497575789019 60266009671838246363683529)
    ·
      refine ⟨45199507253878684772762647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60266009671838246363683529 45199507253878684772762647)
      ·
        refine ⟨67799260880818027159143971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45199507253878684772762647 67799260880818027159143971)
        ·
          refine ⟨101698891321227040738715957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67799260880818027159143971 101698891321227040738715957)
          ·
            refine ⟨9534271061365035069254621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101698891321227040738715957 9534271061365035069254621)
            ·
              refine ⟨3575351648011888150970483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9534271061365035069254621 3575351648011888150970483)
              ·
                refine ⟨5363027472017832226455725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575351648011888150970483 5363027472017832226455725)
                ·
                  refine ⟨2011135302006687084920897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5363027472017832226455725 2011135302006687084920897)
                  ·
                    refine ⟨1508351476505015313690673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011135302006687084920897 1508351476505015313690673)
                    ·
                      refine ⟨1131263607378761485268005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508351476505015313690673 1131263607378761485268005)
                      ·
                        rfl

theorem cell23_2203128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_2203128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203128 prefixEnd_2203128 := by exact prefixLift 2203128
  have htrace : WordTrace (prefixWord ++ tailWord_2203128) baseStart_2203128 baseEnd_2203128 := by
    simpa [prefixWord, tailWord_2203128, baseEnd_2203128] using wordTrace_append hprefix tailTrace_2203128
  have hstable : (prefixWord ++ tailWord_2203128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203128).length < 2 ^ (prefixWord ++ tailWord_2203128).sum := by decide
  have hdescent : baseEnd_2203128 < baseStart_2203128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203194 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_2203194 : Nat := 118140960795 + 2203194 * 2 ^ 59
def prefixEnd_2203194 : Nat := 4983230072969 + 3 ^ 40 * 2203194 * 2
def baseEnd_2203194 : Nat := 377099165700652742347567

theorem tailTrace_2203194 : CollatzResearch.WordTrace tailWord_2203194 prefixEnd_2203194 377099165700652742347567 := by
  unfold tailWord_2203194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089271695052972105870159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53571391186807925615653757 20089271695052972105870159)
  ·
    refine ⟨30133907542579458158805239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20089271695052972105870159 30133907542579458158805239)
    ·
      refine ⟨45200861313869187238207859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30133907542579458158805239 45200861313869187238207859)
      ·
        refine ⟨67801291970803780857311789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45200861313869187238207859 67801291970803780857311789)
        ·
          refine ⟨25425484489051417821491921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67801291970803780857311789 25425484489051417821491921)
          ·
            refine ⟨19069113366788563366118941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25425484489051417821491921 19069113366788563366118941)
            ·
              refine ⟨7150917512545711262294603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19069113366788563366118941 7150917512545711262294603)
              ·
                refine ⟨10726376268818566893441905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150917512545711262294603 10726376268818566893441905)
                ·
                  refine ⟨8044782201613925170081429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10726376268818566893441905 8044782201613925170081429)
                  ·
                    refine ⟨377099165700652742347567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8044782201613925170081429 377099165700652742347567)
                    ·
                      rfl

theorem cell23_2203194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_2203194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203194 prefixEnd_2203194 := by exact prefixLift 2203194
  have htrace : WordTrace (prefixWord ++ tailWord_2203194) baseStart_2203194 baseEnd_2203194 := by
    simpa [prefixWord, tailWord_2203194, baseEnd_2203194] using wordTrace_append hprefix tailTrace_2203194
  have hstable : (prefixWord ++ tailWord_2203194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203194).length < 2 ^ (prefixWord ++ tailWord_2203194).sum := by decide
  have hdescent : baseEnd_2203194 < baseStart_2203194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203214 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2203214 : Nat := 118140960795 + 2203214 * 2 ^ 59
def prefixEnd_2203214 : Nat := 4983230072969 + 3 ^ 40 * 2203214 * 2
def baseEnd_2203214 : Nat := 1131307766715048148792609

theorem tailTrace_2203214 : CollatzResearch.WordTrace tailWord_2203214 prefixEnd_2203214 1131307766715048148792609 := by
  unfold tailWord_2203214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044727030017428979901087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53571877493426287892805797 10044727030017428979901087)
  ·
    refine ⟨15067090545026143469851631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10044727030017428979901087 15067090545026143469851631)
    ·
      refine ⟨22600635817539215204777447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15067090545026143469851631 22600635817539215204777447)
      ·
        refine ⟨33900953726308822807166171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22600635817539215204777447 33900953726308822807166171)
        ·
          refine ⟨50851430589463234210749257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33900953726308822807166171 50851430589463234210749257)
          ·
            refine ⟨38138572942097425658061943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50851430589463234210749257 38138572942097425658061943)
            ·
              refine ⟨57207859413146138487092915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38138572942097425658061943 57207859413146138487092915)
              ·
                refine ⟨85811789119719207730639373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57207859413146138487092915 85811789119719207730639373)
                ·
                  refine ⟨32179420919894702898989765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85811789119719207730639373 32179420919894702898989765)
                  ·
                    refine ⟨6033641422480256793560581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32179420919894702898989765 6033641422480256793560581)
                    ·
                      refine ⟨1131307766715048148792609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6033641422480256793560581 1131307766715048148792609)
                      ·
                        rfl

theorem cell23_2203214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2203214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203214 prefixEnd_2203214 := by exact prefixLift 2203214
  have htrace : WordTrace (prefixWord ++ tailWord_2203214) baseStart_2203214 baseEnd_2203214 := by
    simpa [prefixWord, tailWord_2203214, baseEnd_2203214] using wordTrace_append hprefix tailTrace_2203214
  have hstable : (prefixWord ++ tailWord_2203214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203214).length < 2 ^ (prefixWord ++ tailWord_2203214).sum := by decide
  have hdescent : baseEnd_2203214 < baseStart_2203214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203218 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_2203218 : Nat := 118140960795 + 2203218 * 2 ^ 59
def prefixEnd_2203218 : Nat := 4983230072969 + 3 ^ 40 * 2203218 * 2
def baseEnd_2203218 : Nat := 1131309820637666133142591

theorem tailTrace_2203218 : CollatzResearch.WordTrace tailWord_2203218 prefixEnd_2203218 1131309820637666133142591 := by
  unfold tailWord_2203218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089490533031235130588577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53571974754749960348236205 20089490533031235130588577)
  ·
    refine ⟨15067117899773426347941433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20089490533031235130588577 15067117899773426347941433)
    ·
      refine ⟨11300338424830069760956075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15067117899773426347941433 11300338424830069760956075)
      ·
        refine ⟨16950507637245104641434113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11300338424830069760956075 16950507637245104641434113)
        ·
          refine ⟨12712880727933828481075585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16950507637245104641434113 12712880727933828481075585)
          ·
            refine ⟨9534660545950371360806689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12712880727933828481075585 9534660545950371360806689)
            ·
              refine ⟨7150995409462778520605017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9534660545950371360806689 7150995409462778520605017)
              ·
                refine ⟨5363246557097083890453763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7150995409462778520605017 5363246557097083890453763)
                ·
                  refine ⟨8044869835645625835680645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363246557097083890453763 8044869835645625835680645)
                  ·
                    refine ⟨1508413094183554844190121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8044869835645625835680645 1508413094183554844190121)
                    ·
                      refine ⟨1131309820637666133142591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508413094183554844190121 1131309820637666133142591)
                      ·
                        rfl

theorem cell23_2203218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_2203218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203218 prefixEnd_2203218 := by exact prefixLift 2203218
  have htrace : WordTrace (prefixWord ++ tailWord_2203218) baseStart_2203218 baseEnd_2203218 := by
    simpa [prefixWord, tailWord_2203218, baseEnd_2203218] using wordTrace_append hprefix tailTrace_2203218
  have hstable : (prefixWord ++ tailWord_2203218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203218).length < 2 ^ (prefixWord ++ tailWord_2203218).sum := by decide
  have hdescent : baseEnd_2203218 < baseStart_2203218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203229 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2203229 : Nat := 118140960795 + 2203229 * 2 ^ 59
def prefixEnd_2203229 : Nat := 4983230072969 + 3 ^ 40 * 2203229 * 2
def baseEnd_2203229 : Nat := 1131315468924865590105041

theorem tailTrace_2203229 : CollatzResearch.WordTrace tailWord_2203229 prefixEnd_2203229 1131315468924865590105041 := by
  unfold tailWord_2203229
  simp only [CollatzResearch.WordTrace]
  refine ⟨80358363335085089401004741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53572242223390059600669827 80358363335085089401004741)
  ·
    refine ⟨15067193125328454262688389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80358363335085089401004741 15067193125328454262688389)
    ·
      refine ⟨2825098710999085174254073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15067193125328454262688389 2825098710999085174254073)
      ·
        refine ⟨2118824033249313880690555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825098710999085174254073 2118824033249313880690555)
        ·
          refine ⟨3178236049873970821035833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118824033249313880690555 3178236049873970821035833)
          ·
            refine ⟨2383677037405478115776875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178236049873970821035833 2383677037405478115776875)
            ·
              refine ⟨3575515556108217173665313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383677037405478115776875 3575515556108217173665313)
              ·
                refine ⟨2681636667081162880248985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575515556108217173665313 2681636667081162880248985)
                ·
                  refine ⟨2011227500310872160186739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681636667081162880248985 2011227500310872160186739)
                  ·
                    refine ⟨3016841250466308240280109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011227500310872160186739 3016841250466308240280109)
                    ·
                      refine ⟨1131315468924865590105041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016841250466308240280109 1131315468924865590105041)
                      ·
                        rfl

theorem cell23_2203229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2203229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203229 prefixEnd_2203229 := by exact prefixLift 2203229
  have htrace : WordTrace (prefixWord ++ tailWord_2203229) baseStart_2203229 baseEnd_2203229 := by
    simpa [prefixWord, tailWord_2203229, baseEnd_2203229] using wordTrace_append hprefix tailTrace_2203229
  have hstable : (prefixWord ++ tailWord_2203229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203229).length < 2 ^ (prefixWord ++ tailWord_2203229).sum := by decide
  have hdescent : baseEnd_2203229 < baseStart_2203229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203235 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 2, 2, 2]
def baseStart_2203235 : Nat := 118140960795 + 2203235 * 2 ^ 59
def prefixEnd_2203235 : Nat := 4983230072969 + 3 ^ 40 * 2203235 * 2
def baseEnd_2203235 : Nat := 1131318549808792566630013

theorem tailTrace_2203235 : CollatzResearch.WordTrace tailWord_2203235 prefixEnd_2203235 1131318549808792566630013 := by
  unfold tailWord_2203235
  simp only [CollatzResearch.WordTrace]
  refine ⟨80358582173063352425723159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53572388115375568283815439 80358582173063352425723159)
  ·
    refine ⟨120537873259595028638584739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80358582173063352425723159 120537873259595028638584739)
    ·
      refine ⟨180806809889392542957877109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120537873259595028638584739 180806809889392542957877109)
      ·
        refine ⟨16950638427130550902300979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180806809889392542957877109 16950638427130550902300979)
        ·
          refine ⟨25425957640695826353451469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16950638427130550902300979 25425957640695826353451469)
          ·
            refine ⟨9534734115260934882544301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25425957640695826353451469 9534734115260934882544301)
            ·
              refine ⟨3575525293222850580954113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9534734115260934882544301 3575525293222850580954113)
              ·
                refine ⟨2681643969917137935715585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575525293222850580954113 2681643969917137935715585)
                ·
                  refine ⟨2011232977437853451786689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681643969917137935715585 2011232977437853451786689)
                  ·
                    refine ⟨1508424733078390088840017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011232977437853451786689 1508424733078390088840017)
                    ·
                      refine ⟨1131318549808792566630013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508424733078390088840017 1131318549808792566630013)
                      ·
                        rfl

theorem cell23_2203235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_2203235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203235 prefixEnd_2203235 := by exact prefixLift 2203235
  have htrace : WordTrace (prefixWord ++ tailWord_2203235) baseStart_2203235 baseEnd_2203235 := by
    simpa [prefixWord, tailWord_2203235, baseEnd_2203235] using wordTrace_append hprefix tailTrace_2203235
  have hstable : (prefixWord ++ tailWord_2203235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203235).length < 2 ^ (prefixWord ++ tailWord_2203235).sum := by decide
  have hdescent : baseEnd_2203235 < baseStart_2203235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203241 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 5]
def baseStart_2203241 : Nat := 118140960795 + 2203241 * 2 ^ 59
def prefixEnd_2203241 : Nat := 4983230072969 + 3 ^ 40 * 2203241 * 2
def baseEnd_2203241 : Nat := 125702403410302171461665

theorem tailTrace_2203241 : CollatzResearch.WordTrace tailWord_2203241 prefixEnd_2203241 125702403410302171461665 := by
  unfold tailWord_2203241
  simp only [CollatzResearch.WordTrace]
  refine ⟨80358801011041615450441577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53572534007361076966961051 80358801011041615450441577)
  ·
    refine ⟨60269100758281211587831183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80358801011041615450441577 60269100758281211587831183)
    ·
      refine ⟨90403651137421817381746775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60269100758281211587831183 90403651137421817381746775)
      ·
        refine ⟨135605476706132726072620163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90403651137421817381746775 135605476706132726072620163)
        ·
          refine ⟨203408215059199089108930245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135605476706132726072620163 203408215059199089108930245)
          ·
            refine ⟨38139040323599829207924421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203408215059199089108930245 38139040323599829207924421)
            ·
              refine ⟨7151070060674967976485829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38139040323599829207924421 7151070060674967976485829)
              ·
                refine ⟨1340825636376556495591093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7151070060674967976485829 1340825636376556495591093)
                ·
                  refine ⟨125702403410302171461665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340825636376556495591093 125702403410302171461665)
                  ·
                    rfl

theorem cell23_2203241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 5].length) (baseStart_2203241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203241 prefixEnd_2203241 := by exact prefixLift 2203241
  have htrace : WordTrace (prefixWord ++ tailWord_2203241) baseStart_2203241 baseEnd_2203241 := by
    simpa [prefixWord, tailWord_2203241, baseEnd_2203241] using wordTrace_append hprefix tailTrace_2203241
  have hstable : (prefixWord ++ tailWord_2203241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203241).length < 2 ^ (prefixWord ++ tailWord_2203241).sum := by decide
  have hdescent : baseEnd_2203241 < baseStart_2203241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203311 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_2203311 : Nat := 118140960795 + 2203311 * 2 ^ 59
def prefixEnd_2203311 : Nat := 4983230072969 + 3 ^ 40 * 2203311 * 2
def baseEnd_2203311 : Nat := 1131357574338534269279663

theorem tailTrace_2203311 : CollatzResearch.WordTrace tailWord_2203311 prefixEnd_2203311 1131357574338534269279663 := by
  unfold tailWord_2203311
  simp only [CollatzResearch.WordTrace]
  refine ⟨80361354120788017405489787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53574236080525344936993191 80361354120788017405489787)
  ·
    refine ⟨120542031181182026108234681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80361354120788017405489787 120542031181182026108234681)
    ·
      refine ⟨90406523385886519581176011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120542031181182026108234681 90406523385886519581176011)
      ·
        refine ⟨135609785078829779371764017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90406523385886519581176011 135609785078829779371764017)
        ·
          refine ⟨101707338809122334528823013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135609785078829779371764017 101707338809122334528823013)
          ·
            refine ⟨19070126026710437724154315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101707338809122334528823013 19070126026710437724154315)
            ·
              refine ⟨28605189040065656586231473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19070126026710437724154315 28605189040065656586231473)
              ·
                refine ⟨21453891780049242439673605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28605189040065656586231473 21453891780049242439673605)
                ·
                  refine ⟨4022604708759232957438801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21453891780049242439673605 4022604708759232957438801)
                  ·
                    refine ⟨3016953531569424718079101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022604708759232957438801 3016953531569424718079101)
                    ·
                      refine ⟨1131357574338534269279663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016953531569424718079101 1131357574338534269279663)
                      ·
                        rfl

theorem cell23_2203311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_2203311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203311 prefixEnd_2203311 := by exact prefixLift 2203311
  have htrace : WordTrace (prefixWord ++ tailWord_2203311) baseStart_2203311 baseEnd_2203311 := by
    simpa [prefixWord, tailWord_2203311, baseEnd_2203311] using wordTrace_append hprefix tailTrace_2203311
  have hstable : (prefixWord ++ tailWord_2203311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203311).length < 2 ^ (prefixWord ++ tailWord_2203311).sum := by decide
  have hdescent : baseEnd_2203311 < baseStart_2203311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203328 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_2203328 : Nat := 118140960795 + 2203328 * 2 ^ 59
def prefixEnd_2203328 : Nat := 4983230072969 + 3 ^ 40 * 2203328 * 2
def baseEnd_2203328 : Nat := 1131366303509660702767085

theorem tailTrace_2203328 : CollatzResearch.WordTrace tailWord_2203328 prefixEnd_2203328 1131366303509660702767085 := by
  unfold tailWord_2203328
  simp only [CollatzResearch.WordTrace]
  refine ⟨40180987080863214654429319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53574649441150952872572425 40180987080863214654429319)
  ·
    refine ⟨60271480621294821981643979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40180987080863214654429319 60271480621294821981643979)
    ·
      refine ⟨90407220931942232972465969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60271480621294821981643979 90407220931942232972465969)
      ·
        refine ⟨67805415698956674729349477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90407220931942232972465969 67805415698956674729349477)
        ·
          refine ⟨12713515443554376511753027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67805415698956674729349477 12713515443554376511753027)
          ·
            refine ⟨19070273165331564767629541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713515443554376511753027 19070273165331564767629541)
            ·
              refine ⟨3575676218499668393930539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19070273165331564767629541 3575676218499668393930539)
              ·
                refine ⟨5363514327749502590895809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575676218499668393930539 5363514327749502590895809)
                ·
                  refine ⟨4022635745812126943171857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363514327749502590895809 4022635745812126943171857)
                  ·
                    refine ⟨3016976809359095207378893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4022635745812126943171857 3016976809359095207378893)
                    ·
                      refine ⟨1131366303509660702767085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3016976809359095207378893 1131366303509660702767085)
                      ·
                        rfl

theorem cell23_2203328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_2203328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203328 prefixEnd_2203328 := by exact prefixLift 2203328
  have htrace : WordTrace (prefixWord ++ tailWord_2203328) baseStart_2203328 baseEnd_2203328 := by
    simpa [prefixWord, tailWord_2203328, baseEnd_2203328] using wordTrace_append hprefix tailTrace_2203328
  have hstable : (prefixWord ++ tailWord_2203328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203328).length < 2 ^ (prefixWord ++ tailWord_2203328).sum := by decide
  have hdescent : baseEnd_2203328 < baseStart_2203328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203348 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 6]
def baseStart_2203348 : Nat := 118140960795 + 2203348 * 2 ^ 59
def prefixEnd_2203348 : Nat := 4983230072969 + 3 ^ 40 * 2203348 * 2
def baseEnd_2203348 : Nat := 125708508124750069390777

theorem tailTrace_2203348 : CollatzResearch.WordTrace tailWord_2203348 prefixEnd_2203348 125708508124750069390777 := by
  unfold tailWord_2203348
  simp only [CollatzResearch.WordTrace]
  refine ⟨40181351810826986362293349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53575135747769315149724465 40181351810826986362293349)
  ·
    refine ⟨7534003464530059942930003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40181351810826986362293349 7534003464530059942930003)
    ·
      refine ⟨11301005196795089914395005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534003464530059942930003 11301005196795089914395005)
      ·
        refine ⟨4237876948798158717898127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11301005196795089914395005 4237876948798158717898127)
        ·
          refine ⟨6356815423197238076847191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237876948798158717898127 6356815423197238076847191)
          ·
            refine ⟨9535223134795857115270787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356815423197238076847191 9535223134795857115270787)
            ·
              refine ⟨14302834702193785672906181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535223134795857115270787 14302834702193785672906181)
              ·
                refine ⟨2681781506661334813669909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14302834702193785672906181 2681781506661334813669909)
                ·
                  refine ⟨125708508124750069390777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2681781506661334813669909 125708508124750069390777)
                  ·
                    rfl

theorem cell23_2203348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_2203348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203348 prefixEnd_2203348 := by exact prefixLift 2203348
  have htrace : WordTrace (prefixWord ++ tailWord_2203348) baseStart_2203348 baseEnd_2203348 := by
    simpa [prefixWord, tailWord_2203348, baseEnd_2203348] using wordTrace_append hprefix tailTrace_2203348
  have hstable : (prefixWord ++ tailWord_2203348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203348).length < 2 ^ (prefixWord ++ tailWord_2203348).sum := by decide
  have hdescent : baseEnd_2203348 < baseStart_2203348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203378 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_2203378 : Nat := 118140960795 + 2203378 * 2 ^ 59
def prefixEnd_2203378 : Nat := 4983230072969 + 3 ^ 40 * 2203378 * 2
def baseEnd_2203378 : Nat := 377130659180795169047285

theorem tailTrace_2203378 : CollatzResearch.WordTrace tailWord_2203378 prefixEnd_2203378 377130659180795169047285 := by
  unfold tailWord_2203378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20090949452886321962044697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53575865207696858565452525 20090949452886321962044697)
  ·
    refine ⟨15068212089664741471533523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20090949452886321962044697 15068212089664741471533523)
    ·
      refine ⟨22602318134497112207300285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068212089664741471533523 22602318134497112207300285)
      ·
        refine ⟨8475869300436417077737607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22602318134497112207300285 8475869300436417077737607)
        ·
          refine ⟨12713803950654625616606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8475869300436417077737607 12713803950654625616606411)
          ·
            refine ⟨19070705925981938424909617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713803950654625616606411 19070705925981938424909617)
            ·
              refine ⟨14303029444486453818682213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19070705925981938424909617 14303029444486453818682213)
              ·
                refine ⟨2681818020841210091002915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14303029444486453818682213 2681818020841210091002915)
                ·
                  refine ⟨4022727031261815136504373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681818020841210091002915 4022727031261815136504373)
                  ·
                    refine ⟨377130659180795169047285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4022727031261815136504373 377130659180795169047285)
                    ·
                      rfl

theorem cell23_2203378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_2203378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203378 prefixEnd_2203378 := by exact prefixLift 2203378
  have htrace : WordTrace (prefixWord ++ tailWord_2203378) baseStart_2203378 baseEnd_2203378 := by
    simpa [prefixWord, tailWord_2203378, baseEnd_2203378] using wordTrace_append hprefix tailTrace_2203378
  have hstable : (prefixWord ++ tailWord_2203378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203378).length < 2 ^ (prefixWord ++ tailWord_2203378).sum := by decide
  have hdescent : baseEnd_2203378 < baseStart_2203378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203391 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 6]
def baseStart_2203391 : Nat := 118140960795 + 2203391 * 2 ^ 59
def prefixEnd_2203391 : Nat := 4983230072969 + 3 ^ 40 * 2203391 * 2
def baseEnd_2203391 : Nat := 377132884263631318759765

theorem tailTrace_2203391 : CollatzResearch.WordTrace tailWord_2203391 prefixEnd_2203391 377132884263631318759765 := by
  unfold tailWord_2203391
  simp only [CollatzResearch.WordTrace]
  refine ⟨80364271960498191068402027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53576181306998794045601351 80364271960498191068402027)
  ·
    refine ⟨120546407940747286602603041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80364271960498191068402027 120546407940747286602603041)
    ·
      refine ⟨90409805955560464951952281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120546407940747286602603041 90409805955560464951952281)
      ·
        refine ⟨67807354466670348713964211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90409805955560464951952281 67807354466670348713964211)
        ·
          refine ⟨101711031700005523070946317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67807354466670348713964211 101711031700005523070946317)
          ·
            refine ⟨38141636887502071151604869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101711031700005523070946317 38141636887502071151604869)
            ·
              refine ⟨7151556916406638340925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38141636887502071151604869 7151556916406638340925913)
              ·
                refine ⟨5363667687304978755694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151556916406638340925913 5363667687304978755694435)
                ·
                  refine ⟨8045501530957468133541653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363667687304978755694435 8045501530957468133541653)
                  ·
                    refine ⟨377132884263631318759765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8045501530957468133541653 377132884263631318759765)
                    ·
                      rfl

theorem cell23_2203391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_2203391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203391 prefixEnd_2203391 := by exact prefixLift 2203391
  have htrace : WordTrace (prefixWord ++ tailWord_2203391) baseStart_2203391 baseEnd_2203391 := by
    simpa [prefixWord, tailWord_2203391, baseEnd_2203391] using wordTrace_append hprefix tailTrace_2203391
  have hstable : (prefixWord ++ tailWord_2203391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203391).length < 2 ^ (prefixWord ++ tailWord_2203391).sum := by decide
  have hdescent : baseEnd_2203391 < baseStart_2203391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203401 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_2203401 : Nat := 118140960795 + 2203401 * 2 ^ 59
def prefixEnd_2203401 : Nat := 4983230072969 + 3 ^ 40 * 2203401 * 2
def baseEnd_2203401 : Nat := 1131403787597438917154249

theorem tailTrace_2203401 : CollatzResearch.WordTrace tailWord_2203401 prefixEnd_2203401 1131403787597438917154249 := by
  unfold tailWord_2203401
  simp only [CollatzResearch.WordTrace]
  refine ⟨80364636690461962776266057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53576424460307975184177371 80364636690461962776266057)
  ·
    refine ⟨60273477517846472082199543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80364636690461962776266057 60273477517846472082199543)
    ·
      refine ⟨90410216276769708123299315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60273477517846472082199543 90410216276769708123299315)
      ·
        refine ⟨135615324415154562184948973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90410216276769708123299315 135615324415154562184948973)
        ·
          refine ⟨50855746655682960819355865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135615324415154562184948973 50855746655682960819355865)
          ·
            refine ⟨38141809991762220614516899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50855746655682960819355865 38141809991762220614516899)
            ·
              refine ⟨57212714987643330921775349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38141809991762220614516899 57212714987643330921775349)
              ·
                refine ⟨5363692030091562273916439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57212714987643330921775349 5363692030091562273916439)
                ·
                  refine ⟨8045538045137343410874659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363692030091562273916439 8045538045137343410874659)
                  ·
                    refine ⟨12068307067706015116311989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8045538045137343410874659 12068307067706015116311989)
                    ·
                      refine ⟨1131403787597438917154249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12068307067706015116311989 1131403787597438917154249)
                      ·
                        rfl

theorem cell23_2203401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_2203401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203401 prefixEnd_2203401 := by exact prefixLift 2203401
  have htrace : WordTrace (prefixWord ++ tailWord_2203401) baseStart_2203401 baseEnd_2203401 := by
    simpa [prefixWord, tailWord_2203401, baseEnd_2203401] using wordTrace_append hprefix tailTrace_2203401
  have hstable : (prefixWord ++ tailWord_2203401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203401).length < 2 ^ (prefixWord ++ tailWord_2203401).sum := by decide
  have hdescent : baseEnd_2203401 < baseStart_2203401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203418 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2203418 : Nat := 118140960795 + 2203418 * 2 ^ 59
def prefixEnd_2203418 : Nat := 4983230072969 + 3 ^ 40 * 2203418 * 2
def baseEnd_2203418 : Nat := 1131412516768565350641671

theorem tailTrace_2203418 : CollatzResearch.WordTrace tailWord_2203418 prefixEnd_2203418 1131412516768565350641671 := by
  unfold tailWord_2203418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20091314182850093669908727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53576837820933583119756605 20091314182850093669908727)
  ·
    refine ⟨30136971274275140504863091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20091314182850093669908727 30136971274275140504863091)
    ·
      refine ⟨45205456911412710757294637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30136971274275140504863091 45205456911412710757294637)
      ·
        refine ⟨16952046341779766533985489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45205456911412710757294637 16952046341779766533985489)
        ·
          refine ⟨12714034756334824900489117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16952046341779766533985489 12714034756334824900489117)
          ·
            refine ⟨4767763033625559337683419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12714034756334824900489117 4767763033625559337683419)
            ·
              refine ⟨7151644550438339006525129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767763033625559337683419 7151644550438339006525129)
              ·
                refine ⟨5363733412828754254893847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151644550438339006525129 5363733412828754254893847)
                ·
                  refine ⟨8045600119243131382340771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363733412828754254893847 8045600119243131382340771)
                  ·
                    refine ⟨12068400178864697073511157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8045600119243131382340771 12068400178864697073511157)
                    ·
                      refine ⟨1131412516768565350641671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12068400178864697073511157 1131412516768565350641671)
                      ·
                        rfl

theorem cell23_2203418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2203418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203418 prefixEnd_2203418 := by exact prefixLift 2203418
  have htrace : WordTrace (prefixWord ++ tailWord_2203418) baseStart_2203418 baseEnd_2203418 := by
    simpa [prefixWord, tailWord_2203418, baseEnd_2203418] using wordTrace_append hprefix tailTrace_2203418
  have hstable : (prefixWord ++ tailWord_2203418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203418).length < 2 ^ (prefixWord ++ tailWord_2203418).sum := by decide
  have hdescent : baseEnd_2203418 < baseStart_2203418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203428 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2203428 : Nat := 118140960795 + 2203428 * 2 ^ 59
def prefixEnd_2203428 : Nat := 4983230072969 + 3 ^ 40 * 2203428 * 2
def baseEnd_2203428 : Nat := 1131417651575110311516625

theorem tailTrace_2203428 : CollatzResearch.WordTrace tailWord_2203428 prefixEnd_2203428 1131417651575110311516625 := by
  unfold tailWord_2203428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182810730682073193749469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53577080974242764258332625 40182810730682073193749469)
  ·
    refine ⟨15068554024005777447656051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40182810730682073193749469 15068554024005777447656051)
    ·
      refine ⟨22602831036008666171484077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068554024005777447656051 22602831036008666171484077)
      ·
        refine ⟨8476061638503249814306529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22602831036008666171484077 8476061638503249814306529)
        ·
          refine ⟨6357046228877437360729897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8476061638503249814306529 6357046228877437360729897)
          ·
            refine ⟨4767784671658078020547423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6357046228877437360729897 4767784671658078020547423)
            ·
              refine ⟨7151677007487117030821135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767784671658078020547423 7151677007487117030821135)
              ·
                refine ⟨10727515511230675546231703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151677007487117030821135 10727515511230675546231703)
                ·
                  refine ⟨16091273266846013319347555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10727515511230675546231703 16091273266846013319347555)
                  ·
                    refine ⟨24136909900269019979021333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16091273266846013319347555 24136909900269019979021333)
                    ·
                      refine ⟨1131417651575110311516625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24136909900269019979021333 1131417651575110311516625)
                      ·
                        rfl

theorem cell23_2203428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2203428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203428 prefixEnd_2203428 := by exact prefixLift 2203428
  have htrace : WordTrace (prefixWord ++ tailWord_2203428) baseStart_2203428 baseEnd_2203428 := by
    simpa [prefixWord, tailWord_2203428, baseEnd_2203428] using wordTrace_append hprefix tailTrace_2203428
  have hstable : (prefixWord ++ tailWord_2203428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203428).length < 2 ^ (prefixWord ++ tailWord_2203428).sum := by decide
  have hdescent : baseEnd_2203428 < baseStart_2203428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203432 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2203432 : Nat := 118140960795 + 2203432 * 2 ^ 59
def prefixEnd_2203432 : Nat := 4983230072969 + 3 ^ 40 * 2203432 * 2
def baseEnd_2203432 : Nat := 1131419705497728295866607

theorem tailTrace_2203432 : CollatzResearch.WordTrace tailWord_2203432 prefixEnd_2203432 1131419705497728295866607 := by
  unfold tailWord_2203432
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182883676674827535322275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53577178235566436713763033 40182883676674827535322275)
  ·
    refine ⟨60274325515012241302983413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182883676674827535322275 60274325515012241302983413)
    ·
      refine ⟨5650718017032397622154695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60274325515012241302983413 5650718017032397622154695)
      ·
        refine ⟨8476077025548596433232043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650718017032397622154695 8476077025548596433232043)
        ·
          refine ⟨12714115538322894649848065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476077025548596433232043 12714115538322894649848065)
          ·
            refine ⟨9535586653742170987386049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12714115538322894649848065 9535586653742170987386049)
            ·
              refine ⟨7151689990306628240539537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9535586653742170987386049 7151689990306628240539537)
              ·
                refine ⟨5363767492729971180404653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151689990306628240539537 5363767492729971180404653)
                ·
                  refine ⟨2011412809773739192651745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5363767492729971180404653 2011412809773739192651745)
                  ·
                    refine ⟨1508559607330304394488809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011412809773739192651745 1508559607330304394488809)
                    ·
                      refine ⟨1131419705497728295866607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508559607330304394488809 1131419705497728295866607)
                      ·
                        rfl

theorem cell23_2203432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2203432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203432 prefixEnd_2203432 := by exact prefixLift 2203432
  have htrace : WordTrace (prefixWord ++ tailWord_2203432) baseStart_2203432 baseEnd_2203432 := by
    simpa [prefixWord, tailWord_2203432, baseEnd_2203432] using wordTrace_append hprefix tailTrace_2203432
  have hstable : (prefixWord ++ tailWord_2203432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203432).length < 2 ^ (prefixWord ++ tailWord_2203432).sum := by decide
  have hdescent : baseEnd_2203432 < baseStart_2203432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203461 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_2203461 : Nat := 118140960795 + 2203461 * 2 ^ 59
def prefixEnd_2203461 : Nat := 4983230072969 + 3 ^ 40 * 2203461 * 2
def baseEnd_2203461 : Nat := 1131434596436708682403973

theorem tailTrace_2203461 : CollatzResearch.WordTrace tailWord_2203461 prefixEnd_2203461 1131434596436708682403973 := by
  unfold tailWord_2203461
  simp only [CollatzResearch.WordTrace]
  refine ⟨80366825070244593023450237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53577883380163062015633491 80366825070244593023450237)
  ·
    refine ⟨30137559401341722383793839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80366825070244593023450237 30137559401341722383793839)
    ·
      refine ⟨45206339102012583575690759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30137559401341722383793839 45206339102012583575690759)
      ·
        refine ⟨67809508653018875363536139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45206339102012583575690759 67809508653018875363536139)
        ·
          refine ⟨101714262979528313045304209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67809508653018875363536139 101714262979528313045304209)
          ·
            refine ⟨76285697234646234783978157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101714262979528313045304209 76285697234646234783978157)
            ·
              refine ⟨28607136462992338043991809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76285697234646234783978157 28607136462992338043991809)
              ·
                refine ⟨21455352347244253532993857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28607136462992338043991809 21455352347244253532993857)
                ·
                  refine ⟨16091514260433190149745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21455352347244253532993857 16091514260433190149745393)
                  ·
                    refine ⟨12068635695324892612309045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16091514260433190149745393 12068635695324892612309045)
                    ·
                      refine ⟨1131434596436708682403973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12068635695324892612309045 1131434596436708682403973)
                      ·
                        rfl

theorem cell23_2203461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_2203461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203461 prefixEnd_2203461 := by exact prefixLift 2203461
  have htrace : WordTrace (prefixWord ++ tailWord_2203461) baseStart_2203461 baseEnd_2203461 := by
    simpa [prefixWord, tailWord_2203461, baseEnd_2203461] using wordTrace_append hprefix tailTrace_2203461
  have hstable : (prefixWord ++ tailWord_2203461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203461).length < 2 ^ (prefixWord ++ tailWord_2203461).sum := by decide
  have hdescent : baseEnd_2203461 < baseStart_2203461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203465 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_2203465 : Nat := 118140960795 + 2203465 * 2 ^ 59
def prefixEnd_2203465 : Nat := 4983230072969 + 3 ^ 40 * 2203465 * 2
def baseEnd_2203465 : Nat := 1131436650359326666753955

theorem tailTrace_2203465 : CollatzResearch.WordTrace tailWord_2203465 prefixEnd_2203465 1131436650359326666753955 := by
  unfold tailWord_2203465
  simp only [CollatzResearch.WordTrace]
  refine ⟨80366970962230101706595849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53577980641486734471063899 80366970962230101706595849)
  ·
    refine ⟨60275228221672576279946887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80366970962230101706595849 60275228221672576279946887)
    ·
      refine ⟨90412842332508864419920331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60275228221672576279946887 90412842332508864419920331)
      ·
        refine ⟨135619263498763296629880497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90412842332508864419920331 135619263498763296629880497)
        ·
          refine ⟨101714447624072472472410373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135619263498763296629880497 101714447624072472472410373)
          ·
            refine ⟨19071458929513588588576945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101714447624072472472410373 19071458929513588588576945)
            ·
              refine ⟨14303594197135191441432709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19071458929513588588576945 14303594197135191441432709)
              ·
                refine ⟨2681923911962848395268633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14303594197135191441432709 2681923911962848395268633)
                ·
                  refine ⟨2011442933972136296451475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681923911962848395268633 2011442933972136296451475)
                  ·
                    refine ⟨3017164400958204444677213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011442933972136296451475 3017164400958204444677213)
                    ·
                      refine ⟨1131436650359326666753955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017164400958204444677213 1131436650359326666753955)
                      ·
                        rfl

theorem cell23_2203465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_2203465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203465 prefixEnd_2203465 := by exact prefixLift 2203465
  have htrace : WordTrace (prefixWord ++ tailWord_2203465) baseStart_2203465 baseEnd_2203465 := by
    simpa [prefixWord, tailWord_2203465, baseEnd_2203465] using wordTrace_append hprefix tailTrace_2203465
  have hstable : (prefixWord ++ tailWord_2203465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203465).length < 2 ^ (prefixWord ++ tailWord_2203465).sum := by decide
  have hdescent : baseEnd_2203465 < baseStart_2203465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203481 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_2203481 : Nat := 118140960795 + 2203481 * 2 ^ 59
def prefixEnd_2203481 : Nat := 4983230072969 + 3 ^ 40 * 2203481 * 2
def baseEnd_2203481 : Nat := 377148288683266201384627

theorem tailTrace_2203481 : CollatzResearch.WordTrace tailWord_2203481 prefixEnd_2203481 377148288683266201384627 := by
  unfold tailWord_2203481
  simp only [CollatzResearch.WordTrace]
  refine ⟨80367554530172136439178297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53578369686781424292785531 80367554530172136439178297)
  ·
    refine ⟨60275665897629102329383723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80367554530172136439178297 60275665897629102329383723)
    ·
      refine ⟨90413498846443653494075585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60275665897629102329383723 90413498846443653494075585)
      ·
        refine ⟨67810124134832740120556689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90413498846443653494075585 67810124134832740120556689)
        ·
          refine ⟨50857593101124555090417517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67810124134832740120556689 50857593101124555090417517)
          ·
            refine ⟨19071597412921708158906569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50857593101124555090417517 19071597412921708158906569)
            ·
              refine ⟨14303698059691281119179927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19071597412921708158906569 14303698059691281119179927)
              ·
                refine ⟨21455547089536921678769891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14303698059691281119179927 21455547089536921678769891)
                ·
                  refine ⟨32183320634305382518154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21455547089536921678769891 32183320634305382518154837)
                  ·
                    refine ⟨377148288683266201384627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32183320634305382518154837 377148288683266201384627)
                    ·
                      rfl

theorem cell23_2203481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_2203481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203481 prefixEnd_2203481 := by exact prefixLift 2203481
  have htrace : WordTrace (prefixWord ++ tailWord_2203481) baseStart_2203481 baseEnd_2203481 := by
    simpa [prefixWord, tailWord_2203481, baseEnd_2203481] using wordTrace_append hprefix tailTrace_2203481
  have hstable : (prefixWord ++ tailWord_2203481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203481).length < 2 ^ (prefixWord ++ tailWord_2203481).sum := by decide
  have hdescent : baseEnd_2203481 < baseStart_2203481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203492 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_2203492 : Nat := 118140960795 + 2203492 * 2 ^ 59
def prefixEnd_2203492 : Nat := 4983230072969 + 3 ^ 40 * 2203492 * 2
def baseEnd_2203492 : Nat := 1131450514336998061116331

theorem tailTrace_2203492 : CollatzResearch.WordTrace tailWord_2203492 prefixEnd_2203492 1131450514336998061116331 := by
  unfold tailWord_2203492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40183977866566142658914365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53578637155421523545219153 40183977866566142658914365)
  ·
    refine ⟨15068991699962303497092887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40183977866566142658914365 15068991699962303497092887)
    ·
      refine ⟨22603487549943455245639331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068991699962303497092887 22603487549943455245639331)
      ·
        refine ⟨33905231324915182868458997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22603487549943455245639331 33905231324915182868458997)
        ·
          refine ⟨3178615436710798393918031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33905231324915182868458997 3178615436710798393918031)
          ·
            refine ⟨4767923155066197590877047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178615436710798393918031 4767923155066197590877047)
            ·
              refine ⟨7151884732599296386315571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767923155066197590877047 7151884732599296386315571)
              ·
                refine ⟨10727827098898944579473357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7151884732599296386315571 10727827098898944579473357)
                ·
                  refine ⟨4022935162087104217302509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10727827098898944579473357 4022935162087104217302509)
                  ·
                    refine ⟨1508600685782664081488441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4022935162087104217302509 1508600685782664081488441)
                    ·
                      refine ⟨1131450514336998061116331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508600685782664081488441 1131450514336998061116331)
                      ·
                        rfl

theorem cell23_2203492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_2203492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203492 prefixEnd_2203492 := by exact prefixLift 2203492
  have htrace : WordTrace (prefixWord ++ tailWord_2203492) baseStart_2203492 baseEnd_2203492 := by
    simpa [prefixWord, tailWord_2203492, baseEnd_2203492] using wordTrace_append hprefix tailTrace_2203492
  have hstable : (prefixWord ++ tailWord_2203492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203492).length < 2 ^ (prefixWord ++ tailWord_2203492).sum := by decide
  have hdescent : baseEnd_2203492 < baseStart_2203492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203505 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_2203505 : Nat := 118140960795 + 2203505 * 2 ^ 59
def prefixEnd_2203505 : Nat := 4983230072969 + 3 ^ 40 * 2203505 * 2
def baseEnd_2203505 : Nat := 1131457189585506510253771

theorem tailTrace_2203505 : CollatzResearch.WordTrace tailWord_2203505 prefixEnd_2203505 1131457189585506510253771 := by
  unfold tailWord_2203505
  simp only [CollatzResearch.WordTrace]
  refine ⟨80368429882085188538051969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53578953254723459025367979 80368429882085188538051969)
  ·
    refine ⟨60276322411563891403538977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80368429882085188538051969 60276322411563891403538977)
    ·
      refine ⟨45207241808672918552654233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60276322411563891403538977 45207241808672918552654233)
      ·
        refine ⟨33905431356504688914490675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45207241808672918552654233 33905431356504688914490675)
        ·
          refine ⟨50858147034757033371736013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33905431356504688914490675 50858147034757033371736013)
          ·
            refine ⟨19071805138033887514401005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50858147034757033371736013 19071805138033887514401005)
            ·
              refine ⟨7151926926762707817900377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19071805138033887514401005 7151926926762707817900377)
              ·
                refine ⟨5363945195072030863425283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151926926762707817900377 5363945195072030863425283)
                ·
                  refine ⟨8045917792608046295137925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5363945195072030863425283 8045917792608046295137925)
                  ·
                    refine ⟨1508609586114008680338361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8045917792608046295137925 1508609586114008680338361)
                    ·
                      refine ⟨1131457189585506510253771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508609586114008680338361 1131457189585506510253771)
                      ·
                        rfl

theorem cell23_2203505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_2203505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203505 prefixEnd_2203505 := by exact prefixLift 2203505
  have htrace : WordTrace (prefixWord ++ tailWord_2203505) baseStart_2203505 baseEnd_2203505 := by
    simpa [prefixWord, tailWord_2203505, baseEnd_2203505] using wordTrace_append hprefix tailTrace_2203505
  have hstable : (prefixWord ++ tailWord_2203505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203505).length < 2 ^ (prefixWord ++ tailWord_2203505).sum := by decide
  have hdescent : baseEnd_2203505 < baseStart_2203505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203509 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2203509 : Nat := 118140960795 + 2203509 * 2 ^ 59
def prefixEnd_2203509 : Nat := 4983230072969 + 3 ^ 40 * 2203509 * 2
def baseEnd_2203509 : Nat := 1131459243508124494603753

theorem tailTrace_2203509 : CollatzResearch.WordTrace tailWord_2203509 prefixEnd_2203509 1131459243508124494603753 := by
  unfold tailWord_2203509
  simp only [CollatzResearch.WordTrace]
  refine ⟨80368575774070697221197581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53579050516047131480798387 80368575774070697221197581)
  ·
    refine ⟨30138215915276511457949093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80368575774070697221197581 30138215915276511457949093)
    ·
      refine ⟨5650915484114345898365455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30138215915276511457949093 5650915484114345898365455)
      ·
        refine ⟨8476373226171518847548183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650915484114345898365455 8476373226171518847548183)
        ·
          refine ⟨12714559839257278271322275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8476373226171518847548183 12714559839257278271322275)
          ·
            refine ⟨19071839758885917406983413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12714559839257278271322275 19071839758885917406983413)
            ·
              refine ⟨1787984977395554756904695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19071839758885917406983413 1787984977395554756904695)
              ·
                refine ⟨2681977466093332135357043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787984977395554756904695 2681977466093332135357043)
                ·
                  refine ⟨4022966199139998203035565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2681977466093332135357043 4022966199139998203035565)
                  ·
                    refine ⟨1508612324677499326138337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4022966199139998203035565 1508612324677499326138337)
                    ·
                      refine ⟨1131459243508124494603753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508612324677499326138337 1131459243508124494603753)
                      ·
                        rfl

theorem cell23_2203509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2203509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203509 prefixEnd_2203509 := by exact prefixLift 2203509
  have htrace : WordTrace (prefixWord ++ tailWord_2203509) baseStart_2203509 baseEnd_2203509 := by
    simpa [prefixWord, tailWord_2203509, baseEnd_2203509] using wordTrace_append hprefix tailTrace_2203509
  have hstable : (prefixWord ++ tailWord_2203509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203509).length < 2 ^ (prefixWord ++ tailWord_2203509).sum := by decide
  have hdescent : baseEnd_2203509 < baseStart_2203509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203531 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_2203531 : Nat := 118140960795 + 2203531 * 2 ^ 59
def prefixEnd_2203531 : Nat := 4983230072969 + 3 ^ 40 * 2203531 * 2
def baseEnd_2203531 : Nat := 1131470540082523408528651

theorem tailTrace_2203531 : CollatzResearch.WordTrace tailWord_2203531 prefixEnd_2203531 1131470540082523408528651 := by
  unfold tailWord_2203531
  simp only [CollatzResearch.WordTrace]
  refine ⟨80369378179990994978498447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53579585453327329985665631 80369378179990994978498447)
  ·
    refine ⟨120554067269986492467747671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80369378179990994978498447 120554067269986492467747671)
    ·
      refine ⟨180831100904979738701621507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120554067269986492467747671 180831100904979738701621507)
      ·
        refine ⟨271246651357469608052432261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180831100904979738701621507 271246651357469608052432261)
        ·
          refine ⟨50858747129525551509831049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271246651357469608052432261 50858747129525551509831049)
          ·
            refine ⟨38144060347144163632373287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50858747129525551509831049 38144060347144163632373287)
            ·
              refine ⟨57216090520716245448559931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38144060347144163632373287 57216090520716245448559931)
              ·
                refine ⟨85824135781074368172839897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57216090520716245448559931 85824135781074368172839897)
                ·
                  refine ⟨64368101835805776129629923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85824135781074368172839897 64368101835805776129629923)
                  ·
                    refine ⟨96552152753708664194444885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64368101835805776129629923 96552152753708664194444885)
                    ·
                      refine ⟨1131470540082523408528651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 96552152753708664194444885 1131470540082523408528651)
                      ·
                        rfl

theorem cell23_2203531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_2203531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203531 prefixEnd_2203531 := by exact prefixLift 2203531
  have htrace : WordTrace (prefixWord ++ tailWord_2203531) baseStart_2203531 baseEnd_2203531 := by
    simpa [prefixWord, tailWord_2203531, baseEnd_2203531] using wordTrace_append hprefix tailTrace_2203531
  have hstable : (prefixWord ++ tailWord_2203531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203531).length < 2 ^ (prefixWord ++ tailWord_2203531).sum := by decide
  have hdescent : baseEnd_2203531 < baseStart_2203531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203560 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2203560 : Nat := 118140960795 + 2203560 * 2 ^ 59
def prefixEnd_2203560 : Nat := 4983230072969 + 3 ^ 40 * 2203560 * 2
def baseEnd_2203560 : Nat := 1131485431021503795066019

theorem tailTrace_2203560 : CollatzResearch.WordTrace tailWord_2203560 prefixEnd_2203560 1131485431021503795066019 := by
  unfold tailWord_2203560
  simp only [CollatzResearch.WordTrace]
  refine ⟨40185217948442966465652067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53580290597923955287536089 40185217948442966465652067)
  ·
    refine ⟨60277826922664449698478101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40185217948442966465652067 60277826922664449698478101)
    ·
      refine ⟨2825523136999896079616161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60277826922664449698478101 2825523136999896079616161)
      ·
        refine ⟨2119142352749922059712121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2825523136999896079616161 2119142352749922059712121)
        ·
          refine ⟨1589356764562441544784091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119142352749922059712121 1589356764562441544784091)
          ·
            refine ⟨2384035146843662317176137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589356764562441544784091 2384035146843662317176137)
            ·
              refine ⟨1788026360132746737882103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384035146843662317176137 1788026360132746737882103)
              ·
                refine ⟨2682039540199120106823155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788026360132746737882103 2682039540199120106823155)
                ·
                  refine ⟨4023059310298680160234733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682039540199120106823155 4023059310298680160234733)
                  ·
                    refine ⟨1508647241362005060088025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4023059310298680160234733 1508647241362005060088025)
                    ·
                      refine ⟨1131485431021503795066019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508647241362005060088025 1131485431021503795066019)
                      ·
                        rfl

theorem cell23_2203560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2203560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203560 prefixEnd_2203560 := by exact prefixLift 2203560
  have htrace : WordTrace (prefixWord ++ tailWord_2203560) baseStart_2203560 baseEnd_2203560 := by
    simpa [prefixWord, tailWord_2203560, baseEnd_2203560] using wordTrace_append hprefix tailTrace_2203560
  have hstable : (prefixWord ++ tailWord_2203560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203560).length < 2 ^ (prefixWord ++ tailWord_2203560).sum := by decide
  have hdescent : baseEnd_2203560 < baseStart_2203560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203595 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 4, 2]
def baseStart_2203595 : Nat := 118140960795 + 2203595 * 2 ^ 59
def prefixEnd_2203595 : Nat := 4983230072969 + 3 ^ 40 * 2203595 * 2
def baseEnd_2203595 : Nat := 1131503402844411158128357

theorem tailTrace_2203595 : CollatzResearch.WordTrace tailWord_2203595 prefixEnd_2203595 1131503402844411158128357 := by
  unfold tailWord_2203595
  simp only [CollatzResearch.WordTrace]
  refine ⟨80371712451759133908828239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53581141634506089272552159 80371712451759133908828239)
  ·
    refine ⟨120557568677638700863242359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80371712451759133908828239 120557568677638700863242359)
    ·
      refine ⟨180836353016458051294863539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120557568677638700863242359 180836353016458051294863539)
      ·
        refine ⟨271254529524687076942295309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180836353016458051294863539 271254529524687076942295309)
        ·
          refine ⟨101720448571757653853360741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271254529524687076942295309 101720448571757653853360741)
          ·
            refine ⟨19072584107204560097505139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101720448571757653853360741 19072584107204560097505139)
            ·
              refine ⟨28608876160806840146257709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19072584107204560097505139 28608876160806840146257709)
              ·
                refine ⟨10728328560302565054846641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28608876160806840146257709 10728328560302565054846641)
                ·
                  refine ⟨8046246420226923791134981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10728328560302565054846641 8046246420226923791134981)
                  ·
                    refine ⟨1508671203792548210837809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8046246420226923791134981 1508671203792548210837809)
                    ·
                      refine ⟨1131503402844411158128357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508671203792548210837809 1131503402844411158128357)
                      ·
                        rfl

theorem cell23_2203595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 4, 2].length) (baseStart_2203595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203595 prefixEnd_2203595 := by exact prefixLift 2203595
  have htrace : WordTrace (prefixWord ++ tailWord_2203595) baseStart_2203595 baseEnd_2203595 := by
    simpa [prefixWord, tailWord_2203595, baseEnd_2203595] using wordTrace_append hprefix tailTrace_2203595
  have hstable : (prefixWord ++ tailWord_2203595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203595).length < 2 ^ (prefixWord ++ tailWord_2203595).sum := by decide
  have hdescent : baseEnd_2203595 < baseStart_2203595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203608 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2203608 : Nat := 118140960795 + 2203608 * 2 ^ 59
def prefixEnd_2203608 : Nat := 4983230072969 + 3 ^ 40 * 2203608 * 2
def baseEnd_2203608 : Nat := 1131510078092919607265797

theorem tailTrace_2203608 : CollatzResearch.WordTrace tailWord_2203608 prefixEnd_2203608 1131510078092919607265797 := by
  unfold tailWord_2203608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186093300356018564525739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53581457733808024752700985 40186093300356018564525739)
  ·
    refine ⟨60279139950534027846788609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40186093300356018564525739 60279139950534027846788609)
    ·
      refine ⟨45209354962900520885091457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60279139950534027846788609 45209354962900520885091457)
      ·
        refine ⟨33907016222175390663818593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45209354962900520885091457 33907016222175390663818593)
        ·
          refine ⟨25430262166631542997863945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33907016222175390663818593 25430262166631542997863945)
          ·
            refine ⟨19072696624973657248397959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25430262166631542997863945 19072696624973657248397959)
            ·
              refine ⟨28609044937460485872596939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19072696624973657248397959 28609044937460485872596939)
              ·
                refine ⟨42913567406190728808895409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28609044937460485872596939 42913567406190728808895409)
                ·
                  refine ⟨32185175554643046606671557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42913567406190728808895409 32185175554643046606671557)
                  ·
                    refine ⟨6034720416495571238750917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32185175554643046606671557 6034720416495571238750917)
                    ·
                      refine ⟨1131510078092919607265797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6034720416495571238750917 1131510078092919607265797)
                      ·
                        rfl

theorem cell23_2203608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2203608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203608 prefixEnd_2203608 := by exact prefixLift 2203608
  have htrace : WordTrace (prefixWord ++ tailWord_2203608) baseStart_2203608 baseEnd_2203608 := by
    simpa [prefixWord, tailWord_2203608, baseEnd_2203608] using wordTrace_append hprefix tailTrace_2203608
  have hstable : (prefixWord ++ tailWord_2203608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203608).length < 2 ^ (prefixWord ++ tailWord_2203608).sum := by decide
  have hdescent : baseEnd_2203608 < baseStart_2203608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203615 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2203615 : Nat := 118140960795 + 2203615 * 2 ^ 59
def prefixEnd_2203615 : Nat := 4983230072969 + 3 ^ 40 * 2203615 * 2
def baseEnd_2203615 : Nat := 1131513672457501079878265

theorem tailTrace_2203615 : CollatzResearch.WordTrace tailWord_2203615 prefixEnd_2203615 1131513672457501079878265 := by
  unfold tailWord_2203615
  simp only [CollatzResearch.WordTrace]
  refine ⟨80372441911686677324556299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53581627941124451549704199 80372441911686677324556299)
  ·
    refine ⟨120558662867530015986834449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80372441911686677324556299 120558662867530015986834449)
    ·
      refine ⟨90418997150647511990125837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120558662867530015986834449 90418997150647511990125837)
      ·
        refine ⟨33907123931492816996297189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90418997150647511990125837 33907123931492816996297189)
        ·
          refine ⟨6357585737154903186805723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33907123931492816996297189 6357585737154903186805723)
          ·
            refine ⟨9536378605732354780208585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357585737154903186805723 9536378605732354780208585)
            ·
              refine ⟨7152283954299266085156439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9536378605732354780208585 7152283954299266085156439)
              ·
                refine ⟨10728425931448899127734659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152283954299266085156439 10728425931448899127734659)
                ·
                  refine ⟨16092638897173348691601989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10728425931448899127734659 16092638897173348691601989)
                  ·
                    refine ⟨3017369793220002879675373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16092638897173348691601989 3017369793220002879675373)
                    ·
                      refine ⟨1131513672457501079878265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017369793220002879675373 1131513672457501079878265)
                      ·
                        rfl

theorem cell23_2203615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2203615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203615 prefixEnd_2203615 := by exact prefixLift 2203615
  have htrace : WordTrace (prefixWord ++ tailWord_2203615) baseStart_2203615 baseEnd_2203615 := by
    simpa [prefixWord, tailWord_2203615, baseEnd_2203615] using wordTrace_append hprefix tailTrace_2203615
  have hstable : (prefixWord ++ tailWord_2203615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203615).length < 2 ^ (prefixWord ++ tailWord_2203615).sum := by decide
  have hdescent : baseEnd_2203615 < baseStart_2203615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203629 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2203629 : Nat := 118140960795 + 2203629 * 2 ^ 59
def prefixEnd_2203629 : Nat := 4983230072969 + 3 ^ 40 * 2203629 * 2
def baseEnd_2203629 : Nat := 1131520861186664025103201

theorem tailTrace_2203629 : CollatzResearch.WordTrace tailWord_2203629 prefixEnd_2203629 1131520861186664025103201 := by
  unfold tailWord_2203629
  simp only [CollatzResearch.WordTrace]
  refine ⟨80372952533635957715565941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53581968355757305143710627 80372952533635957715565941)
  ·
    refine ⟨7534964300028371035834307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80372952533635957715565941 7534964300028371035834307)
    ·
      refine ⟨11302446450042556553751461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534964300028371035834307 11302446450042556553751461)
      ·
        refine ⟨2119208709382979353828399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11302446450042556553751461 2119208709382979353828399)
        ·
          refine ⟨3178813064074469030742599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119208709382979353828399 3178813064074469030742599)
          ·
            refine ⟨4768219596111703546113899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178813064074469030742599 4768219596111703546113899)
            ·
              refine ⟨7152329394167555319170849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768219596111703546113899 7152329394167555319170849)
              ·
                refine ⟨5364247045625666489378137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152329394167555319170849 5364247045625666489378137)
                ·
                  refine ⟨4023185284219249867033603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364247045625666489378137 4023185284219249867033603)
                  ·
                    refine ⟨6034777926328874800550405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023185284219249867033603 6034777926328874800550405)
                    ·
                      refine ⟨1131520861186664025103201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6034777926328874800550405 1131520861186664025103201)
                      ·
                        rfl

theorem cell23_2203629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2203629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203629 prefixEnd_2203629 := by exact prefixLift 2203629
  have htrace : WordTrace (prefixWord ++ tailWord_2203629) baseStart_2203629 baseEnd_2203629 := by
    simpa [prefixWord, tailWord_2203629, baseEnd_2203629] using wordTrace_append hprefix tailTrace_2203629
  have hstable : (prefixWord ++ tailWord_2203629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203629).length < 2 ^ (prefixWord ++ tailWord_2203629).sum := by decide
  have hdescent : baseEnd_2203629 < baseStart_2203629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203662 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2203662 : Nat := 118140960795 + 2203662 * 2 ^ 59
def prefixEnd_2203662 : Nat := 4983230072969 + 3 ^ 40 * 2203662 * 2
def baseEnd_2203662 : Nat := 1131537806048262395990549

theorem tailTrace_2203662 : CollatzResearch.WordTrace tailWord_2203662 prefixEnd_2203662 1131537806048262395990549 := by
  unfold tailWord_2203662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046769517814550543939655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53582770761677602901011493 10046769517814550543939655)
  ·
    refine ⟨15070154276721825815909483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10046769517814550543939655 15070154276721825815909483)
    ·
      refine ⟨22605231415082738723864225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15070154276721825815909483 22605231415082738723864225)
      ·
        refine ⟨16953923561312054042898169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22605231415082738723864225 16953923561312054042898169)
        ·
          refine ⟨12715442670984040532173627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16953923561312054042898169 12715442670984040532173627)
          ·
            refine ⟨19073164006476060798260441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715442670984040532173627 19073164006476060798260441)
            ·
              refine ⟨14304873004857045598695331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19073164006476060798260441 14304873004857045598695331)
              ·
                refine ⟨21457309507285568398042997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14304873004857045598695331 21457309507285568398042997)
                ·
                  refine ⟨2011622766308022037316531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21457309507285568398042997 2011622766308022037316531)
                  ·
                    refine ⟨3017434149462033055974797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011622766308022037316531 3017434149462033055974797)
                    ·
                      refine ⟨1131537806048262395990549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017434149462033055974797 1131537806048262395990549)
                      ·
                        rfl

theorem cell23_2203662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2203662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203662 prefixEnd_2203662 := by exact prefixLift 2203662
  have htrace : WordTrace (prefixWord ++ tailWord_2203662) baseStart_2203662 baseEnd_2203662 := by
    simpa [prefixWord, tailWord_2203662, baseEnd_2203662] using wordTrace_append hprefix tailTrace_2203662
  have hstable : (prefixWord ++ tailWord_2203662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203662).length < 2 ^ (prefixWord ++ tailWord_2203662).sum := by decide
  have hdescent : baseEnd_2203662 < baseStart_2203662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203679 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 1, 1, 3]
def baseStart_2203679 : Nat := 118140960795 + 2203679 * 2 ^ 59
def prefixEnd_2203679 : Nat := 4983230072969 + 3 ^ 40 * 2203679 * 2
def baseEnd_2203679 : Nat := 1131546535219388829477971

theorem tailTrace_2203679 : CollatzResearch.WordTrace tailWord_2203679 prefixEnd_2203679 1131546535219388829477971 := by
  unfold tailWord_2203679
  simp only [CollatzResearch.WordTrace]
  refine ⟨80374776183454816254886091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53583184122303210836590727 80374776183454816254886091)
  ·
    refine ⟨120562164275182224382329137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80374776183454816254886091 120562164275182224382329137)
    ·
      refine ⟨90421623206386668286746853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120562164275182224382329137 90421623206386668286746853)
      ·
        refine ⟨16954054351197500303765035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90421623206386668286746853 16954054351197500303765035)
        ·
          refine ⟨25431081526796250455647553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16954054351197500303765035 25431081526796250455647553)
          ·
            refine ⟨19073311145097187841735665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25431081526796250455647553 19073311145097187841735665)
            ·
              refine ⟨14304983358822890881301749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19073311145097187841735665 14304983358822890881301749)
              ·
                refine ⟨1341092189889646020122039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14304983358822890881301749 1341092189889646020122039)
                ·
                  refine ⟨2011638284834469030183059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341092189889646020122039 2011638284834469030183059)
                  ·
                    refine ⟨3017457427251703545274589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011638284834469030183059 3017457427251703545274589)
                    ·
                      refine ⟨1131546535219388829477971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017457427251703545274589 1131546535219388829477971)
                      ·
                        rfl

theorem cell23_2203679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_2203679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203679 prefixEnd_2203679 := by exact prefixLift 2203679
  have htrace : WordTrace (prefixWord ++ tailWord_2203679) baseStart_2203679 baseEnd_2203679 := by
    simpa [prefixWord, tailWord_2203679, baseEnd_2203679] using wordTrace_append hprefix tailTrace_2203679
  have hstable : (prefixWord ++ tailWord_2203679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203679).length < 2 ^ (prefixWord ++ tailWord_2203679).sum := by decide
  have hdescent : baseEnd_2203679 < baseStart_2203679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203696 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 1, 1, 3]
def baseStart_2203696 : Nat := 118140960795 + 2203696 * 2 ^ 59
def prefixEnd_2203696 : Nat := 4983230072969 + 3 ^ 40 * 2203696 * 2
def baseEnd_2203696 : Nat := 1131555264390515262965393

theorem tailTrace_2203696 : CollatzResearch.WordTrace tailWord_2203696 prefixEnd_2203696 1131555264390515262965393 := by
  unfold tailWord_2203696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40187698112196614079127471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53583597482928818772169961 40187698112196614079127471)
  ·
    refine ⟨60281547168294921118691207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40187698112196614079127471 60281547168294921118691207)
    ·
      refine ⟨90422320752442381678036811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60281547168294921118691207 90422320752442381678036811)
      ·
        refine ⟨135633481128663572517055217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90422320752442381678036811 135633481128663572517055217)
        ·
          refine ⟨101725110846497679387791413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135633481128663572517055217 101725110846497679387791413)
          ·
            refine ⟨9536729141859157442605445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101725110846497679387791413 9536729141859157442605445)
            ·
              refine ⟨1788136714098592020488521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9536729141859157442605445 1788136714098592020488521)
              ·
                refine ⟨1341102535573944015366391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788136714098592020488521 1341102535573944015366391)
                ·
                  refine ⟨2011653803360916023049587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341102535573944015366391 2011653803360916023049587)
                  ·
                    refine ⟨3017480705041374034574381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2011653803360916023049587 3017480705041374034574381)
                    ·
                      refine ⟨1131555264390515262965393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017480705041374034574381 1131555264390515262965393)
                      ·
                        rfl

theorem cell23_2203696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 1, 3].length) (baseStart_2203696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203696 prefixEnd_2203696 := by exact prefixLift 2203696
  have htrace : WordTrace (prefixWord ++ tailWord_2203696) baseStart_2203696 baseEnd_2203696 := by
    simpa [prefixWord, tailWord_2203696, baseEnd_2203696] using wordTrace_append hprefix tailTrace_2203696
  have hstable : (prefixWord ++ tailWord_2203696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203696).length < 2 ^ (prefixWord ++ tailWord_2203696).sum := by decide
  have hdescent : baseEnd_2203696 < baseStart_2203696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203702 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2203702 : Nat := 118140960795 + 2203702 * 2 ^ 59
def prefixEnd_2203702 : Nat := 4983230072969 + 3 ^ 40 * 2203702 * 2
def baseEnd_2203702 : Nat := 1131558345274442239490365

theorem tailTrace_2203702 : CollatzResearch.WordTrace tailWord_2203702 prefixEnd_2203702 1131558345274442239490365 := by
  unfold tailWord_2203702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023475941398218198935835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53583743374914327455315573 5023475941398218198935835)
  ·
    refine ⟨7535213912097327298403753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5023475941398218198935835 7535213912097327298403753)
    ·
      refine ⟨5651410434072995473802815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7535213912097327298403753 5651410434072995473802815)
      ·
        refine ⟨8477115651109493210704223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651410434072995473802815 8477115651109493210704223)
        ·
          refine ⟨12715673476664239816056335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477115651109493210704223 12715673476664239816056335)
          ·
            refine ⟨19073510214996359724084503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715673476664239816056335 19073510214996359724084503)
            ·
              refine ⟨28610265322494539586126755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19073510214996359724084503 28610265322494539586126755)
              ·
                refine ⟨42915397983741809379190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28610265322494539586126755 42915397983741809379190133)
                ·
                  refine ⟨4023318560975794629299075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42915397983741809379190133 4023318560975794629299075)
                  ·
                    refine ⟨6034977841463691943948613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023318560975794629299075 6034977841463691943948613)
                    ·
                      refine ⟨1131558345274442239490365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6034977841463691943948613 1131558345274442239490365)
                      ·
                        rfl

theorem cell23_2203702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2203702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203702 prefixEnd_2203702 := by exact prefixLift 2203702
  have htrace : WordTrace (prefixWord ++ tailWord_2203702) baseStart_2203702 baseEnd_2203702 := by
    simpa [prefixWord, tailWord_2203702, baseEnd_2203702] using wordTrace_append hprefix tailTrace_2203702
  have hstable : (prefixWord ++ tailWord_2203702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203702).length < 2 ^ (prefixWord ++ tailWord_2203702).sum := by decide
  have hdescent : baseEnd_2203702 < baseStart_2203702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203712 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_2203712 : Nat := 118140960795 + 2203712 * 2 ^ 59
def prefixEnd_2203712 : Nat := 4983230072969 + 3 ^ 40 * 2203712 * 2
def baseEnd_2203712 : Nat := 377187826693662400121773

theorem tailTrace_2203712 : CollatzResearch.WordTrace tailWord_2203712 prefixEnd_2203712 377187826693662400121773 := by
  unfold tailWord_2203712
  simp only [CollatzResearch.WordTrace]
  refine ⟨40187989896167631445418695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53583986528223508593891593 40187989896167631445418695)
  ·
    refine ⟨60281984844251447168128043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40187989896167631445418695 60281984844251447168128043)
    ·
      refine ⟨90422977266377170752192065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60281984844251447168128043 90422977266377170752192065)
      ·
        refine ⟨67817232949782878064144049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90422977266377170752192065 67817232949782878064144049)
        ·
          refine ⟨50862924712337158548108037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67817232949782878064144049 50862924712337158548108037)
          ·
            refine ⟨9536798383563217227770257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50862924712337158548108037 9536798383563217227770257)
            ·
              refine ⟨7152598787672412920827693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9536798383563217227770257 7152598787672412920827693)
              ·
                refine ⟨2682224545377154845310385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7152598787672412920827693 2682224545377154845310385)
                ·
                  refine ⟨2011668409032866133982789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682224545377154845310385 2011668409032866133982789)
                  ·
                    refine ⟨377187826693662400121773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2011668409032866133982789 377187826693662400121773)
                    ·
                      rfl

theorem cell23_2203712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_2203712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203712 prefixEnd_2203712 := by exact prefixLift 2203712
  have htrace : WordTrace (prefixWord ++ tailWord_2203712) baseStart_2203712 baseEnd_2203712 := by
    simpa [prefixWord, tailWord_2203712, baseEnd_2203712] using wordTrace_append hprefix tailTrace_2203712
  have hstable : (prefixWord ++ tailWord_2203712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203712).length < 2 ^ (prefixWord ++ tailWord_2203712).sum := by decide
  have hdescent : baseEnd_2203712 < baseStart_2203712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203719 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_2203719 : Nat := 118140960795 + 2203719 * 2 ^ 59
def prefixEnd_2203719 : Nat := 4983230072969 + 3 ^ 40 * 2203719 * 2
def baseEnd_2203719 : Nat := 1131567074445568672977787

theorem tailTrace_2203719 : CollatzResearch.WordTrace tailWord_2203719 prefixEnd_2203719 1131567074445568672977787 := by
  unfold tailWord_2203719
  simp only [CollatzResearch.WordTrace]
  refine ⟨80376235103309903086342211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53584156735539935390894807 80376235103309903086342211)
  ·
    refine ⟨120564352654964854629513317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80376235103309903086342211 120564352654964854629513317)
    ·
      refine ⟨22605816122805910243033747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120564352654964854629513317 22605816122805910243033747)
      ·
        refine ⟨33908724184208865364550621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22605816122805910243033747 33908724184208865364550621)
        ·
          refine ⟨12715771569078324511706483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33908724184208865364550621 12715771569078324511706483)
          ·
            refine ⟨19073657353617486767559725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715771569078324511706483 19073657353617486767559725)
            ·
              refine ⟨7152621507606557537834897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19073657353617486767559725 7152621507606557537834897)
              ·
                refine ⟨5364466130704918153376173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152621507606557537834897 5364466130704918153376173)
                ·
                  refine ⟨2011674799014344307516065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5364466130704918153376173 2011674799014344307516065)
                  ·
                    refine ⟨1508756099260758230637049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011674799014344307516065 1508756099260758230637049)
                    ·
                      refine ⟨1131567074445568672977787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508756099260758230637049 1131567074445568672977787)
                      ·
                        rfl

theorem cell23_2203719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_2203719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203719 prefixEnd_2203719 := by exact prefixLift 2203719
  have htrace : WordTrace (prefixWord ++ tailWord_2203719) baseStart_2203719 baseEnd_2203719 := by
    simpa [prefixWord, tailWord_2203719, baseEnd_2203719] using wordTrace_append hprefix tailTrace_2203719
  have hstable : (prefixWord ++ tailWord_2203719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203719).length < 2 ^ (prefixWord ++ tailWord_2203719).sum := by decide
  have hdescent : baseEnd_2203719 < baseStart_2203719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203722 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_2203722 : Nat := 118140960795 + 2203722 * 2 ^ 59
def prefixEnd_2203722 : Nat := 4983230072969 + 3 ^ 40 * 2203722 * 2
def baseEnd_2203722 : Nat := 1131568614887532161240273

theorem tailTrace_2203722 : CollatzResearch.WordTrace tailWord_2203722 prefixEnd_2203722 1131568614887532161240273 := by
  unfold tailWord_2203722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094086130574758649675355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53584229681532689732467613 20094086130574758649675355)
  ·
    refine ⟨30141129195862137974513033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20094086130574758649675355 30141129195862137974513033)
    ·
      refine ⟨22605846896896603480884775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30141129195862137974513033 22605846896896603480884775)
      ·
        refine ⟨33908770345344905221327163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22605846896896603480884775 33908770345344905221327163)
        ·
          refine ⟨50863155518017357831990745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33908770345344905221327163 50863155518017357831990745)
          ·
            refine ⟨38147366638513018373993059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50863155518017357831990745 38147366638513018373993059)
            ·
              refine ⟨57221049957769527560989589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38147366638513018373993059 57221049957769527560989589)
              ·
                refine ⟨2682236716770446604421387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57221049957769527560989589 2682236716770446604421387)
                ·
                  refine ⟨4023355075155669906632081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682236716770446604421387 4023355075155669906632081)
                  ·
                    refine ⟨3017516306366752429974061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023355075155669906632081 3017516306366752429974061)
                    ·
                      refine ⟨1131568614887532161240273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017516306366752429974061 1131568614887532161240273)
                      ·
                        rfl

theorem cell23_2203722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_2203722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203722 prefixEnd_2203722 := by exact prefixLift 2203722
  have htrace : WordTrace (prefixWord ++ tailWord_2203722) baseStart_2203722 baseEnd_2203722 := by
    simpa [prefixWord, tailWord_2203722, baseEnd_2203722] using wordTrace_append hprefix tailTrace_2203722
  have hstable : (prefixWord ++ tailWord_2203722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203722).length < 2 ^ (prefixWord ++ tailWord_2203722).sum := by decide
  have hdescent : baseEnd_2203722 < baseStart_2203722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203736 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_2203736 : Nat := 118140960795 + 2203736 * 2 ^ 59
def prefixEnd_2203736 : Nat := 4983230072969 + 3 ^ 40 * 2203736 * 2
def baseEnd_2203736 : Nat := 1131575803616695106465209

theorem tailTrace_2203736 : CollatzResearch.WordTrace tailWord_2203736 prefixEnd_2203736 1131575803616695106465209 := by
  unfold tailWord_2203736
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188427572124157494855531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53584570096165543326474041 40188427572124157494855531)
  ·
    refine ⟨60282641358186236242283297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40188427572124157494855531 60282641358186236242283297)
    ·
      refine ⟨45211981018639677181712473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60282641358186236242283297 45211981018639677181712473)
      ·
        refine ⟨33908985763979757886284355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45211981018639677181712473 33908985763979757886284355)
        ·
          refine ⟨50863478645969636829426533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33908985763979757886284355 50863478645969636829426533)
          ·
            refine ⟨9536902246119306905517475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50863478645969636829426533 9536902246119306905517475)
            ·
              refine ⟨14305353369178960358276213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9536902246119306905517475 14305353369178960358276213)
              ·
                refine ⟨1341126878360527533588395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14305353369178960358276213 1341126878360527533588395)
                ·
                  refine ⟨2011690317540791300382593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341126878360527533588395 2011690317540791300382593)
                  ·
                    refine ⟨1508767738155593475286945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011690317540791300382593 1508767738155593475286945)
                    ·
                      refine ⟨1131575803616695106465209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508767738155593475286945 1131575803616695106465209)
                      ·
                        rfl

theorem cell23_2203736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_2203736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203736 prefixEnd_2203736 := by exact prefixLift 2203736
  have htrace : WordTrace (prefixWord ++ tailWord_2203736) baseStart_2203736 baseEnd_2203736 := by
    simpa [prefixWord, tailWord_2203736, baseEnd_2203736] using wordTrace_append hprefix tailTrace_2203736
  have hstable : (prefixWord ++ tailWord_2203736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203736).length < 2 ^ (prefixWord ++ tailWord_2203736).sum := by decide
  have hdescent : baseEnd_2203736 < baseStart_2203736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203769 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2203769 : Nat := 118140960795 + 2203769 * 2 ^ 59
def prefixEnd_2203769 : Nat := 4983230072969 + 3 ^ 40 * 2203769 * 2
def baseEnd_2203769 : Nat := 1131592748478293477352557

theorem tailTrace_2203769 : CollatzResearch.WordTrace tailWord_2203769 prefixEnd_2203769 1131592748478293477352557 := by
  unfold tailWord_2203769
  simp only [CollatzResearch.WordTrace]
  refine ⟨80378058753128761625662361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53585372502085841083774907 80378058753128761625662361)
  ·
    refine ⟨60283544064846571219246771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80378058753128761625662361 60283544064846571219246771)
    ·
      refine ⟨90425316097269856828870157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60283544064846571219246771 90425316097269856828870157)
      ·
        refine ⟨33909493536476196310826309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90425316097269856828870157 33909493536476196310826309)
        ·
          refine ⟨6358030038089286808279933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33909493536476196310826309 6358030038089286808279933)
          ·
            refine ⟨2384261264283482553104975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6358030038089286808279933 2384261264283482553104975)
            ·
              refine ⟨3576391896425223829657463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384261264283482553104975 3576391896425223829657463)
              ·
                refine ⟨5364587844637835744486195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576391896425223829657463 5364587844637835744486195)
                ·
                  refine ⟨8046881766956753616729293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5364587844637835744486195 8046881766956753616729293)
                  ·
                    refine ⟨3017580662608782606273485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8046881766956753616729293 3017580662608782606273485)
                    ·
                      refine ⟨1131592748478293477352557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017580662608782606273485 1131592748478293477352557)
                      ·
                        rfl

theorem cell23_2203769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2203769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203769 prefixEnd_2203769 := by exact prefixLift 2203769
  have htrace : WordTrace (prefixWord ++ tailWord_2203769) baseStart_2203769 baseEnd_2203769 := by
    simpa [prefixWord, tailWord_2203769, baseEnd_2203769] using wordTrace_append hprefix tailTrace_2203769
  have hstable : (prefixWord ++ tailWord_2203769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203769).length < 2 ^ (prefixWord ++ tailWord_2203769).sum := by decide
  have hdescent : baseEnd_2203769 < baseStart_2203769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203779 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 1, 3, 2]
def baseStart_2203779 : Nat := 118140960795 + 2203779 * 2 ^ 59
def prefixEnd_2203779 : Nat := 4983230072969 + 3 ^ 40 * 2203779 * 2
def baseEnd_2203779 : Nat := 1131597883284838438227511

theorem tailTrace_2203779 : CollatzResearch.WordTrace tailWord_2203779 prefixEnd_2203779 1131597883284838438227511 := by
  unfold tailWord_2203779
  simp only [CollatzResearch.WordTrace]
  refine ⟨80378423483092533333526391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53585615655395022222350927 80378423483092533333526391)
  ·
    refine ⟨120567635224638800000289587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80378423483092533333526391 120567635224638800000289587)
    ·
      refine ⟨180851452836958200000434381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120567635224638800000289587 180851452836958200000434381)
      ·
        refine ⟨67819294813859325000162893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180851452836958200000434381 67819294813859325000162893)
        ·
          refine ⟨25432235555197246875061085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67819294813859325000162893 25432235555197246875061085)
          ·
            refine ⟨9537088333198967578147907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25432235555197246875061085 9537088333198967578147907)
            ·
              refine ⟨14305632499798451367221861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537088333198967578147907 14305632499798451367221861)
              ·
                refine ⟨2682306093712209631354099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14305632499798451367221861 2682306093712209631354099)
                ·
                  refine ⟨4023459140568314447031149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682306093712209631354099 4023459140568314447031149)
                  ·
                    refine ⟨1508797177713117917636681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4023459140568314447031149 1508797177713117917636681)
                    ·
                      refine ⟨1131597883284838438227511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508797177713117917636681 1131597883284838438227511)
                      ·
                        rfl

theorem cell23_2203779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_2203779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203779 prefixEnd_2203779 := by exact prefixLift 2203779
  have htrace : WordTrace (prefixWord ++ tailWord_2203779) baseStart_2203779 baseEnd_2203779 := by
    simpa [prefixWord, tailWord_2203779, baseEnd_2203779] using wordTrace_append hprefix tailTrace_2203779
  have hstable : (prefixWord ++ tailWord_2203779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203779).length < 2 ^ (prefixWord ++ tailWord_2203779).sum := by decide
  have hdescent : baseEnd_2203779 < baseStart_2203779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203792 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2]
def baseStart_2203792 : Nat := 118140960795 + 2203792 * 2 ^ 59
def prefixEnd_2203792 : Nat := 4983230072969 + 3 ^ 40 * 2203792 * 2
def baseEnd_2203792 : Nat := 1131604558533346887364951

theorem tailTrace_2203792 : CollatzResearch.WordTrace tailWord_2203792 prefixEnd_2203792 1131604558533346887364951 := by
  unfold tailWord_2203792
  simp only [CollatzResearch.WordTrace]
  refine ⟨40189448816022718276874815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53585931754696957702499753 40189448816022718276874815)
  ·
    refine ⟨60284173224034077415312223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40189448816022718276874815 60284173224034077415312223)
    ·
      refine ⟨90426259836051116122968335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60284173224034077415312223 90426259836051116122968335)
      ·
        refine ⟨135639389754076674184452503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90426259836051116122968335 135639389754076674184452503)
        ·
          refine ⟨203459084631115011276678755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135639389754076674184452503 203459084631115011276678755)
          ·
            refine ⟨305188626946672516915018133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203459084631115011276678755 305188626946672516915018133)
            ·
              refine ⟨14305716888125274230391475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 305188626946672516915018133 14305716888125274230391475)
              ·
                refine ⟨21458575332187911345587213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14305716888125274230391475 21458575332187911345587213)
                ·
                  refine ⟨8046965749570466754595205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21458575332187911345587213 8046965749570466754595205)
                  ·
                    refine ⟨1508806078044462516486601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8046965749570466754595205 1508806078044462516486601)
                    ·
                      refine ⟨1131604558533346887364951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508806078044462516486601 1131604558533346887364951)
                      ·
                        rfl

theorem cell23_2203792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2].length) (baseStart_2203792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203792 prefixEnd_2203792 := by exact prefixLift 2203792
  have htrace : WordTrace (prefixWord ++ tailWord_2203792) baseStart_2203792 baseEnd_2203792 := by
    simpa [prefixWord, tailWord_2203792, baseEnd_2203792] using wordTrace_append hprefix tailTrace_2203792
  have hstable : (prefixWord ++ tailWord_2203792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203792).length < 2 ^ (prefixWord ++ tailWord_2203792).sum := by decide
  have hdescent : baseEnd_2203792 < baseStart_2203792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203795 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3]
def baseStart_2203795 : Nat := 118140960795 + 2203795 * 2 ^ 59
def prefixEnd_2203795 : Nat := 4983230072969 + 3 ^ 40 * 2203795 * 2
def baseEnd_2203795 : Nat := 1131606098975310375627437

theorem tailTrace_2203795 : CollatzResearch.WordTrace tailWord_2203795 prefixEnd_2203795 1131606098975310375627437 := by
  unfold tailWord_2203795
  simp only [CollatzResearch.WordTrace]
  refine ⟨80379007051034568066108839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53586004700689712044072559 80379007051034568066108839)
  ·
    refine ⟨120568510576551852099163259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80379007051034568066108839 120568510576551852099163259)
    ·
      refine ⟨180852765864827778148744889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120568510576551852099163259 180852765864827778148744889)
      ·
        refine ⟨135639574398620833611558667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180852765864827778148744889 135639574398620833611558667)
        ·
          refine ⟨203459361597931250417338001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135639574398620833611558667 203459361597931250417338001)
          ·
            refine ⟨152594521198448437813003501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203459361597931250417338001 152594521198448437813003501)
            ·
              refine ⟨57222945449418164179876313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152594521198448437813003501 57222945449418164179876313)
              ·
                refine ⟨42917209087063623134907235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57222945449418164179876313 42917209087063623134907235)
                ·
                  refine ⟨64375813630595434702360853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42917209087063623134907235 64375813630595434702360853)
                  ·
                    refine ⟨3017616263934161001673165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64375813630595434702360853 3017616263934161001673165)
                    ·
                      refine ⟨1131606098975310375627437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017616263934161001673165 1131606098975310375627437)
                      ·
                        rfl

theorem cell23_2203795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_2203795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203795 prefixEnd_2203795 := by exact prefixLift 2203795
  have htrace : WordTrace (prefixWord ++ tailWord_2203795) baseStart_2203795 baseEnd_2203795 := by
    simpa [prefixWord, tailWord_2203795, baseEnd_2203795] using wordTrace_append hprefix tailTrace_2203795
  have hstable : (prefixWord ++ tailWord_2203795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203795).length < 2 ^ (prefixWord ++ tailWord_2203795).sum := by decide
  have hdescent : baseEnd_2203795 < baseStart_2203795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203826 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_2203826 : Nat := 118140960795 + 2203826 * 2 ^ 59
def prefixEnd_2203826 : Nat := 4983230072969 + 3 ^ 40 * 2203826 * 2
def baseEnd_2203826 : Nat := 1131622016875599754339795

theorem tailTrace_2203826 : CollatzResearch.WordTrace tailWord_2203826 prefixEnd_2203826 1131622016875599754339795 := by
  unfold tailWord_2203826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095034428480565090121833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53586758475948173573658221 20095034428480565090121833)
  ·
    refine ⟨15071275821360423817591375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20095034428480565090121833 15071275821360423817591375)
    ·
      refine ⟨22606913732040635726387063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15071275821360423817591375 22606913732040635726387063)
      ·
        refine ⟨33910370598060953589580595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22606913732040635726387063 33910370598060953589580595)
        ·
          refine ⟨50865555897091430384370893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33910370598060953589580595 50865555897091430384370893)
          ·
            refine ⟨19074583461409286394139085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50865555897091430384370893 19074583461409286394139085)
            ·
              refine ⟨7152968798028482397802157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19074583461409286394139085 7152968798028482397802157)
              ·
                refine ⟨2682363299260680899175809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7152968798028482397802157 2682363299260680899175809)
                ·
                  refine ⟨2011772474445510674381857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682363299260680899175809 2011772474445510674381857)
                  ·
                    refine ⟨1508829355834133005786393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011772474445510674381857 1508829355834133005786393)
                    ·
                      refine ⟨1131622016875599754339795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508829355834133005786393 1131622016875599754339795)
                      ·
                        rfl

theorem cell23_2203826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_2203826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203826 prefixEnd_2203826 := by exact prefixLift 2203826
  have htrace : WordTrace (prefixWord ++ tailWord_2203826) baseStart_2203826 baseEnd_2203826 := by
    simpa [prefixWord, tailWord_2203826, baseEnd_2203826] using wordTrace_append hprefix tailTrace_2203826
  have hstable : (prefixWord ++ tailWord_2203826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203826).length < 2 ^ (prefixWord ++ tailWord_2203826).sum := by decide
  have hdescent : baseEnd_2203826 < baseStart_2203826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203845 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_2203845 : Nat := 118140960795 + 2203845 * 2 ^ 59
def prefixEnd_2203845 : Nat := 4983230072969 + 3 ^ 40 * 2203845 * 2
def baseEnd_2203845 : Nat := 377210591002678393334069

theorem tailTrace_2203845 : CollatzResearch.WordTrace tailWord_2203845 prefixEnd_2203845 377210591002678393334069 := by
  unfold tailWord_2203845
  simp only [CollatzResearch.WordTrace]
  refine ⟨80380830700853426605428989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53587220467235617736952659 80380830700853426605428989)
  ·
    refine ⟨30142811512820034977035871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80380830700853426605428989 30142811512820034977035871)
    ·
      refine ⟨45214217269230052465553807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30142811512820034977035871 45214217269230052465553807)
      ·
        refine ⟨67821325903845078698330711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45214217269230052465553807 67821325903845078698330711)
        ·
          refine ⟨101731988855767618047496067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67821325903845078698330711 101731988855767618047496067)
          ·
            refine ⟨152597983283651427071244101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101731988855767618047496067 152597983283651427071244101)
            ·
              refine ⟨28612121865684642575858269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152597983283651427071244101 28612121865684642575858269)
              ·
                refine ⟨10729545699631740965946851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28612121865684642575858269 10729545699631740965946851)
                ·
                  refine ⟨16094318549447611448920277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729545699631740965946851 16094318549447611448920277)
                  ·
                    refine ⟨377210591002678393334069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16094318549447611448920277 377210591002678393334069)
                    ·
                      rfl

theorem cell23_2203845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_2203845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203845 prefixEnd_2203845 := by exact prefixLift 2203845
  have htrace : WordTrace (prefixWord ++ tailWord_2203845) baseStart_2203845 baseEnd_2203845 := by
    simpa [prefixWord, tailWord_2203845, baseEnd_2203845] using wordTrace_append hprefix tailTrace_2203845
  have hstable : (prefixWord ++ tailWord_2203845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203845).length < 2 ^ (prefixWord ++ tailWord_2203845).sum := by decide
  have hdescent : baseEnd_2203845 < baseStart_2203845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203855 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_2203855 : Nat := 118140960795 + 2203855 * 2 ^ 59
def prefixEnd_2203855 : Nat := 4983230072969 + 3 ^ 40 * 2203855 * 2
def baseEnd_2203855 : Nat := 1131636907814580140877161

theorem tailTrace_2203855 : CollatzResearch.WordTrace tailWord_2203855 prefixEnd_2203855 1131636907814580140877161 := by
  unfold tailWord_2203855
  simp only [CollatzResearch.WordTrace]
  refine ⟨80381195430817198313293019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53587463620544798875528679 80381195430817198313293019)
  ·
    refine ⟨120571793146225797469939529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80381195430817198313293019 120571793146225797469939529)
    ·
      refine ⟨90428844859669348102454647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120571793146225797469939529 90428844859669348102454647)
      ·
        refine ⟨135643267289504022153681971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90428844859669348102454647 135643267289504022153681971)
        ·
          refine ⟨203464900934256033230522957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135643267289504022153681971 203464900934256033230522957)
          ·
            refine ⟨76299337850346012461446109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203464900934256033230522957 76299337850346012461446109)
            ·
              refine ⟨28612251693879754673042291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76299337850346012461446109 28612251693879754673042291)
              ·
                refine ⟨42918377540819632009563437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28612251693879754673042291 42918377540819632009563437)
                ·
                  refine ⟨16094391577807362003586289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42918377540819632009563437 16094391577807362003586289)
                  ·
                    refine ⟨12070793683355521502689717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16094391577807362003586289 12070793683355521502689717)
                    ·
                      refine ⟨1131636907814580140877161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12070793683355521502689717 1131636907814580140877161)
                      ·
                        rfl

theorem cell23_2203855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_2203855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203855 prefixEnd_2203855 := by exact prefixLift 2203855
  have htrace : WordTrace (prefixWord ++ tailWord_2203855) baseStart_2203855 baseEnd_2203855 := by
    simpa [prefixWord, tailWord_2203855, baseEnd_2203855] using wordTrace_append hprefix tailTrace_2203855
  have hstable : (prefixWord ++ tailWord_2203855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203855).length < 2 ^ (prefixWord ++ tailWord_2203855).sum := by decide
  have hdescent : baseEnd_2203855 < baseStart_2203855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203882 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2203882 : Nat := 118140960795 + 2203882 * 2 ^ 59
def prefixEnd_2203882 : Nat := 4983230072969 + 3 ^ 40 * 2203882 * 2
def baseEnd_2203882 : Nat := 1131650771792251535239537

theorem tailTrace_2203882 : CollatzResearch.WordTrace tailWord_2203882 prefixEnd_2203882 1131650771792251535239537 := by
  unfold tailWord_2203882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095545050429845481131475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53588120134479587949683933 20095545050429845481131475)
  ·
    refine ⟨30143317575644768221697213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20095545050429845481131475 30143317575644768221697213)
    ·
      refine ⟨11303744090866788083136455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30143317575644768221697213 11303744090866788083136455)
      ·
        refine ⟨16955616136300182124704683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11303744090866788083136455 16955616136300182124704683)
        ·
          refine ⟨25433424204450273187057025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16955616136300182124704683 25433424204450273187057025)
          ·
            refine ⟨19075068153337704890292769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25433424204450273187057025 19075068153337704890292769)
            ·
              refine ⟨14306301115003278667719577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19075068153337704890292769 14306301115003278667719577)
              ·
                refine ⟨10729725836252459000789683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14306301115003278667719577 10729725836252459000789683)
                ·
                  refine ⟨16094588754378688501184525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729725836252459000789683 16094588754378688501184525)
                  ·
                    refine ⟨6035470782892008187944197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16094588754378688501184525 6035470782892008187944197)
                    ·
                      refine ⟨1131650771792251535239537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6035470782892008187944197 1131650771792251535239537)
                      ·
                        rfl

theorem cell23_2203882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2203882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203882 prefixEnd_2203882 := by exact prefixLift 2203882
  have htrace : WordTrace (prefixWord ++ tailWord_2203882) baseStart_2203882 baseEnd_2203882 := by
    simpa [prefixWord, tailWord_2203882, baseEnd_2203882] using wordTrace_append hprefix tailTrace_2203882
  have hstable : (prefixWord ++ tailWord_2203882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203882).length < 2 ^ (prefixWord ++ tailWord_2203882).sum := by decide
  have hdescent : baseEnd_2203882 < baseStart_2203882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_2203895 : Nat := 118140960795 + 2203895 * 2 ^ 59
def prefixEnd_2203895 : Nat := 4983230072969 + 3 ^ 40 * 2203895 * 2
def baseEnd_2203895 : Nat := 1131657447040759984376977

theorem tailTrace_2203895 : CollatzResearch.WordTrace tailWord_2203895 prefixEnd_2203895 1131657447040759984376977 := by
  unfold tailWord_2203895
  simp only [CollatzResearch.WordTrace]
  refine ⟨80382654350672285144749139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53588436233781523429832759 80382654350672285144749139)
  ·
    refine ⟨120573981526008427717123709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80382654350672285144749139 120573981526008427717123709)
    ·
      refine ⟨45215243072253160393921391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120573981526008427717123709 45215243072253160393921391)
      ·
        refine ⟨67822864608379740590882087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45215243072253160393921391 67822864608379740590882087)
        ·
          refine ⟨101734296912569610886323131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67822864608379740590882087 101734296912569610886323131)
          ·
            refine ⟨152601445368854416329484697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101734296912569610886323131 152601445368854416329484697)
            ·
              refine ⟨114451084026640812247113523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152601445368854416329484697 114451084026640812247113523)
              ·
                refine ⟨171676626039961218370670285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114451084026640812247113523 171676626039961218370670285)
                ·
                  refine ⟨64378734764985456889001357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171676626039961218370670285 64378734764985456889001357)
                  ·
                    refine ⟨24142025536869546333375509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64378734764985456889001357 24142025536869546333375509)
                    ·
                      refine ⟨1131657447040759984376977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24142025536869546333375509 1131657447040759984376977)
                      ·
                        rfl

theorem cell23_2203895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_2203895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203895 prefixEnd_2203895 := by exact prefixLift 2203895
  have htrace : WordTrace (prefixWord ++ tailWord_2203895) baseStart_2203895 baseEnd_2203895 := by
    simpa [prefixWord, tailWord_2203895, baseEnd_2203895] using wordTrace_append hprefix tailTrace_2203895
  have hstable : (prefixWord ++ tailWord_2203895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203895).length < 2 ^ (prefixWord ++ tailWord_2203895).sum := by decide
  have hdescent : baseEnd_2203895 < baseStart_2203895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203912 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2203912 : Nat := 118140960795 + 2203912 * 2 ^ 59
def prefixEnd_2203912 : Nat := 4983230072969 + 3 ^ 40 * 2203912 * 2
def baseEnd_2203912 : Nat := 1131666176211886417864399

theorem tailTrace_2203912 : CollatzResearch.WordTrace tailWord_2203912 prefixEnd_2203912 1131666176211886417864399 := by
  unfold tailWord_2203912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40191637195805348524058995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53588849594407131365411993 40191637195805348524058995)
  ·
    refine ⟨60287455793708022786088493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40191637195805348524058995 60287455793708022786088493)
    ·
      refine ⟨22607795922640508544783185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60287455793708022786088493 22607795922640508544783185)
      ·
        refine ⟨16955846941980381408587389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22607795922640508544783185 16955846941980381408587389)
        ·
          refine ⟨6358442603242643028220271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16955846941980381408587389 6358442603242643028220271)
          ·
            refine ⟨9537663904863964542330407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358442603242643028220271 9537663904863964542330407)
            ·
              refine ⟨14306495857295946813495611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537663904863964542330407 14306495857295946813495611)
              ·
                refine ⟨21459743785943920220243417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306495857295946813495611 21459743785943920220243417)
                ·
                  refine ⟨16094807839457940165182563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21459743785943920220243417 16094807839457940165182563)
                  ·
                    refine ⟨24142211759186910247773845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16094807839457940165182563 24142211759186910247773845)
                    ·
                      refine ⟨1131666176211886417864399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24142211759186910247773845 1131666176211886417864399)
                      ·
                        rfl

theorem cell23_2203912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2203912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203912 prefixEnd_2203912 := by exact prefixLift 2203912
  have htrace : WordTrace (prefixWord ++ tailWord_2203912) baseStart_2203912 baseEnd_2203912 := by
    simpa [prefixWord, tailWord_2203912, baseEnd_2203912] using wordTrace_append hprefix tailTrace_2203912
  have hstable : (prefixWord ++ tailWord_2203912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203912).length < 2 ^ (prefixWord ++ tailWord_2203912).sum := by decide
  have hdescent : baseEnd_2203912 < baseStart_2203912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203939 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 6]
def baseStart_2203939 : Nat := 118140960795 + 2203939 * 2 ^ 59
def prefixEnd_2203939 : Nat := 4983230072969 + 3 ^ 40 * 2203939 * 2
def baseEnd_2203939 : Nat := 125742226687728645802975

theorem tailTrace_2203939 : CollatzResearch.WordTrace tailWord_2203939 prefixEnd_2203939 125742226687728645802975 := by
  unfold tailWord_2203939
  simp only [CollatzResearch.WordTrace]
  refine ⟨80384259162512880659350871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53589506108341920439567247 80384259162512880659350871)
  ·
    refine ⟨120576388743769320989026307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80384259162512880659350871 120576388743769320989026307)
    ·
      refine ⟨180864583115653981483539461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120576388743769320989026307 180864583115653981483539461)
      ·
        refine ⟨33912109334185121528163649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180864583115653981483539461 33912109334185121528163649)
        ·
          refine ⟨25434082000638841146122737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33912109334185121528163649 25434082000638841146122737)
          ·
            refine ⟨19075561500479130859592053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25434082000638841146122737 19075561500479130859592053)
            ·
              refine ⟨1788333890669918518086755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19075561500479130859592053 1788333890669918518086755)
              ·
                refine ⟨2682500836004877777130133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788333890669918518086755 2682500836004877777130133)
                ·
                  refine ⟨125742226687728645802975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2682500836004877777130133 125742226687728645802975)
                  ·
                    rfl

theorem cell23_2203939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 6].length) (baseStart_2203939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203939 prefixEnd_2203939 := by exact prefixLift 2203939
  have htrace : WordTrace (prefixWord ++ tailWord_2203939) baseStart_2203939 baseEnd_2203939 := by
    simpa [prefixWord, tailWord_2203939, baseEnd_2203939] using wordTrace_append hprefix tailTrace_2203939
  have hstable : (prefixWord ++ tailWord_2203939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203939).length < 2 ^ (prefixWord ++ tailWord_2203939).sum := by decide
  have hdescent : baseEnd_2203939 < baseStart_2203939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203959 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_2203959 : Nat := 118140960795 + 2203959 * 2 ^ 59
def prefixEnd_2203959 : Nat := 4983230072969 + 3 ^ 40 * 2203959 * 2
def baseEnd_2203959 : Nat := 1131690309802647733976683

theorem tailTrace_2203959 : CollatzResearch.WordTrace tailWord_2203959 prefixEnd_2203959 1131690309802647733976683 := by
  unfold tailWord_2203959
  simp only [CollatzResearch.WordTrace]
  refine ⟨80384988622440424075078931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53589992414960282716719287 80384988622440424075078931)
  ·
    refine ⟨120577482933660636112618397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80384988622440424075078931 120577482933660636112618397)
    ·
      refine ⟨45216556100122738542231899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120577482933660636112618397 45216556100122738542231899)
      ·
        refine ⟨67824834150184107813347849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45216556100122738542231899 67824834150184107813347849)
        ·
          refine ⟨50868625612638080860010887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67824834150184107813347849 50868625612638080860010887)
          ·
            refine ⟨76302938418957121290016331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50868625612638080860010887 76302938418957121290016331)
            ·
              refine ⟨114454407628435681935024497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76302938418957121290016331 114454407628435681935024497)
              ·
                refine ⟨85840805721326761451268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114454407628435681935024497 85840805721326761451268373)
                ·
                  refine ⟨4023787768187191943028205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85840805721326761451268373 4023787768187191943028205)
                  ·
                    refine ⟨1508920413070196978635577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4023787768187191943028205 1508920413070196978635577)
                    ·
                      refine ⟨1131690309802647733976683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508920413070196978635577 1131690309802647733976683)
                      ·
                        rfl

theorem cell23_2203959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_2203959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203959 prefixEnd_2203959 := by exact prefixLift 2203959
  have htrace : WordTrace (prefixWord ++ tailWord_2203959) baseStart_2203959 baseEnd_2203959 := by
    simpa [prefixWord, tailWord_2203959, baseEnd_2203959] using wordTrace_append hprefix tailTrace_2203959
  have hstable : (prefixWord ++ tailWord_2203959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203959).length < 2 ^ (prefixWord ++ tailWord_2203959).sum := by decide
  have hdescent : baseEnd_2203959 < baseStart_2203959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203982 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2203982 : Nat := 118140960795 + 2203982 * 2 ^ 59
def prefixEnd_2203982 : Nat := 4983230072969 + 3 ^ 40 * 2203982 * 2
def baseEnd_2203982 : Nat := 377234039952567047996359

theorem tailTrace_2203982 : CollatzResearch.WordTrace tailWord_2203982 prefixEnd_2203982 377234039952567047996359 := by
  unfold tailWord_2203982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048228437669637375395775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53590551667571399335444133 10048228437669637375395775)
  ·
    refine ⟨15072342656504456063093663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048228437669637375395775 15072342656504456063093663)
    ·
      refine ⟨22608513984756684094640495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15072342656504456063093663 22608513984756684094640495)
      ·
        refine ⟨33912770977135026141960743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22608513984756684094640495 33912770977135026141960743)
        ·
          refine ⟨50869156465702539212941115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33912770977135026141960743 50869156465702539212941115)
          ·
            refine ⟨76303734698553808819411673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50869156465702539212941115 76303734698553808819411673)
            ·
              refine ⟨57227801023915356614558755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76303734698553808819411673 57227801023915356614558755)
              ·
                refine ⟨85841701535873034921838133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57227801023915356614558755 85841701535873034921838133)
                ·
                  refine ⟨8047659518988097023922325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85841701535873034921838133 8047659518988097023922325)
                  ·
                    refine ⟨377234039952567047996359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8047659518988097023922325 377234039952567047996359)
                    ·
                      rfl

theorem cell23_2203982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2203982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203982 prefixEnd_2203982 := by exact prefixLift 2203982
  have htrace : WordTrace (prefixWord ++ tailWord_2203982) baseStart_2203982 baseEnd_2203982 := by
    simpa [prefixWord, tailWord_2203982, baseEnd_2203982] using wordTrace_append hprefix tailTrace_2203982
  have hstable : (prefixWord ++ tailWord_2203982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203982).length < 2 ^ (prefixWord ++ tailWord_2203982).sum := by decide
  have hdescent : baseEnd_2203982 < baseStart_2203982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2203992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2203992 : Nat := 118140960795 + 2203992 * 2 ^ 59
def prefixEnd_2203992 : Nat := 4983230072969 + 3 ^ 40 * 2203992 * 2
def baseEnd_2203992 : Nat := 1131707254664246104864031

theorem tailTrace_2203992 : CollatzResearch.WordTrace tailWord_2203992 prefixEnd_2203992 1131707254664246104864031 := by
  unfold tailWord_2203992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40193096115660435355515115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53590794820880580474020153 40193096115660435355515115)
  ·
    refine ⟨60289644173490653033272673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40193096115660435355515115 60289644173490653033272673)
    ·
      refine ⟨45217233130117989774954505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60289644173490653033272673 45217233130117989774954505)
      ·
        refine ⟨33912924847588492331215879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45217233130117989774954505 33912924847588492331215879)
        ·
          refine ⟨50869387271382738496823819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33912924847588492331215879 50869387271382738496823819)
          ·
            refine ⟨76304080907074107745235729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50869387271382738496823819 76304080907074107745235729)
            ·
              refine ⟨57228060680305580808926797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76304080907074107745235729 57228060680305580808926797)
              ·
                refine ⟨21460522755114592803347549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57228060680305580808926797 21460522755114592803347549)
                ·
                  refine ⟨8047696033167972301255331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21460522755114592803347549 8047696033167972301255331)
                  ·
                    refine ⟨12071544049751958451882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8047696033167972301255331 12071544049751958451882997)
                    ·
                      refine ⟨1131707254664246104864031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12071544049751958451882997 1131707254664246104864031)
                      ·
                        rfl

theorem cell23_2203992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2203992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2203992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2203992 prefixEnd_2203992 := by exact prefixLift 2203992
  have htrace : WordTrace (prefixWord ++ tailWord_2203992) baseStart_2203992 baseEnd_2203992 := by
    simpa [prefixWord, tailWord_2203992, baseEnd_2203992] using wordTrace_append hprefix tailTrace_2203992
  have hstable : (prefixWord ++ tailWord_2203992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2203992).length < 2 ^ (prefixWord ++ tailWord_2203992).sum := by decide
  have hdescent : baseEnd_2203992 < baseStart_2203992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2203992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204009 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_2204009 : Nat := 118140960795 + 2204009 * 2 ^ 59
def prefixEnd_2204009 : Nat := 4983230072969 + 3 ^ 40 * 2204009 * 2
def baseEnd_2204009 : Nat := 1131715983835372538351453

theorem tailTrace_2204009 : CollatzResearch.WordTrace tailWord_2204009 prefixEnd_2204009 1131715983835372538351453 := by
  unfold tailWord_2204009
  simp only [CollatzResearch.WordTrace]
  refine ⟨80386812272259282614399081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53591208181506188409599387 80386812272259282614399081)
  ·
    refine ⟨60290109204194461960799311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80386812272259282614399081 60290109204194461960799311)
    ·
      refine ⟨90435163806291692941198967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60290109204194461960799311 90435163806291692941198967)
      ·
        refine ⟨135652745709437539411798451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90435163806291692941198967 135652745709437539411798451)
        ·
          refine ⟨203479118564156309117697677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135652745709437539411798451 203479118564156309117697677)
          ·
            refine ⟨76304669461558615919136629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203479118564156309117697677 76304669461558615919136629)
            ·
              refine ⟨7153562762021120242419059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76304669461558615919136629 7153562762021120242419059)
              ·
                refine ⟨10730344143031680363628589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7153562762021120242419059 10730344143031680363628589)
                ·
                  refine ⟨4023879053636880136360721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10730344143031680363628589 4023879053636880136360721)
                  ·
                    refine ⟨3017909290227660102270541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023879053636880136360721 3017909290227660102270541)
                    ·
                      refine ⟨1131715983835372538351453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017909290227660102270541 1131715983835372538351453)
                      ·
                        rfl

theorem cell23_2204009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_2204009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204009 prefixEnd_2204009 := by exact prefixLift 2204009
  have htrace : WordTrace (prefixWord ++ tailWord_2204009) baseStart_2204009 baseEnd_2204009 := by
    simpa [prefixWord, tailWord_2204009, baseEnd_2204009] using wordTrace_append hprefix tailTrace_2204009
  have hstable : (prefixWord ++ tailWord_2204009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204009).length < 2 ^ (prefixWord ++ tailWord_2204009).sum := by decide
  have hdescent : baseEnd_2204009 < baseStart_2204009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204033 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2204033 : Nat := 118140960795 + 2204033 * 2 ^ 59
def prefixEnd_2204033 : Nat := 4983230072969 + 3 ^ 40 * 2204033 * 2
def baseEnd_2204033 : Nat := 377242769123693481483781

theorem tailTrace_2204033 : CollatzResearch.WordTrace tailWord_2204033 prefixEnd_2204033 377242769123693481483781 := by
  unfold tailWord_2204033
  simp only [CollatzResearch.WordTrace]
  refine ⟨80387687624172334713272753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53591791749448223142181835 80387687624172334713272753)
  ·
    refine ⟨60290765718129251034954565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80387687624172334713272753 60290765718129251034954565)
    ·
      refine ⟨11304518572149234569053981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60290765718129251034954565 11304518572149234569053981)
      ·
        refine ⟨4239194464555962963395243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11304518572149234569053981 4239194464555962963395243)
        ·
          refine ⟨6358791696833944445092865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239194464555962963395243 6358791696833944445092865)
          ·
            refine ⟨4769093772625458333819649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6358791696833944445092865 4769093772625458333819649)
            ·
              refine ⟨3576820329469093750364737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4769093772625458333819649 3576820329469093750364737)
              ·
                refine ⟨2682615247101820312773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3576820329469093750364737 2682615247101820312773553)
                ·
                  refine ⟨2011961435326365234580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682615247101820312773553 2011961435326365234580165)
                  ·
                    refine ⟨377242769123693481483781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2011961435326365234580165 377242769123693481483781)
                    ·
                      rfl

theorem cell23_2204033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2204033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204033 prefixEnd_2204033 := by exact prefixLift 2204033
  have htrace : WordTrace (prefixWord ++ tailWord_2204033) baseStart_2204033 baseEnd_2204033 := by
    simpa [prefixWord, tailWord_2204033, baseEnd_2204033] using wordTrace_append hprefix tailTrace_2204033
  have hstable : (prefixWord ++ tailWord_2204033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204033).length < 2 ^ (prefixWord ++ tailWord_2204033).sum := by decide
  have hdescent : baseEnd_2204033 < baseStart_2204033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204039 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_2204039 : Nat := 118140960795 + 2204039 * 2 ^ 59
def prefixEnd_2204039 : Nat := 4983230072969 + 3 ^ 40 * 2204039 * 2
def baseEnd_2204039 : Nat := 1131731388255007420976315

theorem tailTrace_2204039 : CollatzResearch.WordTrace tailWord_2204039 prefixEnd_2204039 1131731388255007420976315 := by
  unfold tailWord_2204039
  simp only [CollatzResearch.WordTrace]
  refine ⟨80387906462150597737991171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53591937641433731825327447 80387906462150597737991171)
  ·
    refine ⟨120581859693225896606986757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80387906462150597737991171 120581859693225896606986757)
    ·
      refine ⟨22609098692479855613810017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120581859693225896606986757 22609098692479855613810017)
      ·
        refine ⟨16956824019359891710357513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22609098692479855613810017 16956824019359891710357513)
        ·
          refine ⟨12717618014519918782768135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16956824019359891710357513 12717618014519918782768135)
          ·
            refine ⟨19076427021779878174152203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12717618014519918782768135 19076427021779878174152203)
            ·
              refine ⟨28614640532669817261228305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19076427021779878174152203 28614640532669817261228305)
              ·
                refine ⟨21460980399502362945921229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28614640532669817261228305 21460980399502362945921229)
                ·
                  refine ⟨8047867649813386104720461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21460980399502362945921229 8047867649813386104720461)
                  ·
                    refine ⟨3017950368680019789270173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8047867649813386104720461 3017950368680019789270173)
                    ·
                      refine ⟨1131731388255007420976315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017950368680019789270173 1131731388255007420976315)
                      ·
                        rfl

theorem cell23_2204039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_2204039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204039 prefixEnd_2204039 := by exact prefixLift 2204039
  have htrace : WordTrace (prefixWord ++ tailWord_2204039) baseStart_2204039 baseEnd_2204039 := by
    simpa [prefixWord, tailWord_2204039, baseEnd_2204039] using wordTrace_append hprefix tailTrace_2204039
  have hstable : (prefixWord ++ tailWord_2204039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204039).length < 2 ^ (prefixWord ++ tailWord_2204039).sum := by decide
  have hdescent : baseEnd_2204039 < baseStart_2204039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204040 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_2204040 : Nat := 118140960795 + 2204040 * 2 ^ 59
def prefixEnd_2204040 : Nat := 4983230072969 + 3 ^ 40 * 2204040 * 2
def baseEnd_2204040 : Nat := 1131731901735661917063811

theorem tailTrace_2204040 : CollatzResearch.WordTrace tailWord_2204040 prefixEnd_2204040 1131731901735661917063811 := by
  unfold tailWord_2204040
  simp only [CollatzResearch.WordTrace]
  refine ⟨40193971467573487454388787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53591961956764649939185049 40193971467573487454388787)
  ·
    refine ⟨60290957201360231181583181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40193971467573487454388787 60290957201360231181583181)
    ·
      refine ⟨22609108950510086693093693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60290957201360231181583181 22609108950510086693093693)
      ·
        refine ⟨8478415856441282509910135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22609108950510086693093693 8478415856441282509910135)
        ·
          refine ⟨12717623784661923764865203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8478415856441282509910135 12717623784661923764865203)
          ·
            refine ⟨19076435676992885647297805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12717623784661923764865203 19076435676992885647297805)
            ·
              refine ⟨7153663378872332117736677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19076435676992885647297805 7153663378872332117736677)
              ·
                refine ⟨1341311883538562272075627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7153663378872332117736677 1341311883538562272075627)
                ·
                  refine ⟨2011967825307843408113441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341311883538562272075627 2011967825307843408113441)
                  ·
                    refine ⟨1508975868980882556085081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011967825307843408113441 1508975868980882556085081)
                    ·
                      refine ⟨1131731901735661917063811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508975868980882556085081 1131731901735661917063811)
                      ·
                        rfl

theorem cell23_2204040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_2204040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204040 prefixEnd_2204040 := by exact prefixLift 2204040
  have htrace : WordTrace (prefixWord ++ tailWord_2204040) baseStart_2204040 baseEnd_2204040 := by
    simpa [prefixWord, tailWord_2204040, baseEnd_2204040] using wordTrace_append hprefix tailTrace_2204040
  have hstable : (prefixWord ++ tailWord_2204040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204040).length < 2 ^ (prefixWord ++ tailWord_2204040).sum := by decide
  have hdescent : baseEnd_2204040 < baseStart_2204040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204046 : List Nat := [4, 1, 1, 4, 1, 3, 1, 8]
def baseStart_2204046 : Nat := 118140960795 + 2204046 * 2 ^ 59
def prefixEnd_2204046 : Nat := 4983230072969 + 3 ^ 40 * 2204046 * 2
def baseEnd_2204046 : Nat := 41916110467392181244029

theorem tailTrace_2204046 : CollatzResearch.WordTrace tailWord_2204046 prefixEnd_2204046 41916110467392181244029 := by
  unfold tailWord_2204046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048520221640654741686999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53592107848750158622330661 10048520221640654741686999)
  ·
    refine ⟨15072780332460982112530499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048520221640654741686999 15072780332460982112530499)
    ·
      refine ⟨22609170498691473168795749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15072780332460982112530499 22609170498691473168795749)
      ·
        refine ⟨4239219468504651219149203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22609170498691473168795749 4239219468504651219149203)
        ·
          refine ⟨6358829202756976828723805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239219468504651219149203 6358829202756976828723805)
          ·
            refine ⟨2384560951033866310771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6358829202756976828723805 2384560951033866310771427)
            ·
              refine ⟨3576841426550799466157141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384560951033866310771427 3576841426550799466157141)
              ·
                refine ⟨41916110467392181244029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3576841426550799466157141 41916110467392181244029)
                ·
                  rfl

theorem cell23_2204046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_2204046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204046 prefixEnd_2204046 := by exact prefixLift 2204046
  have htrace : WordTrace (prefixWord ++ tailWord_2204046) baseStart_2204046 baseEnd_2204046 := by
    simpa [prefixWord, tailWord_2204046, baseEnd_2204046] using wordTrace_append hprefix tailTrace_2204046
  have hstable : (prefixWord ++ tailWord_2204046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204046).length < 2 ^ (prefixWord ++ tailWord_2204046).sum := by decide
  have hdescent : baseEnd_2204046 < baseStart_2204046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204049 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_2204049 : Nat := 118140960795 + 2204049 * 2 ^ 59
def prefixEnd_2204049 : Nat := 4983230072969 + 3 ^ 40 * 2204049 * 2
def baseEnd_2204049 : Nat := 1131736523061552381851269

theorem tailTrace_2204049 : CollatzResearch.WordTrace tailWord_2204049 prefixEnd_2204049 1131736523061552381851269 := by
  unfold tailWord_2204049
  simp only [CollatzResearch.WordTrace]
  refine ⟨80388271192114369445855201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53592180794742912963903467 80388271192114369445855201)
  ·
    refine ⟨60291203394085777084391401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80388271192114369445855201 60291203394085777084391401)
    ·
      refine ⟨45218402545564332813293551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60291203394085777084391401 45218402545564332813293551)
      ·
        refine ⟨67827603818346499219940327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45218402545564332813293551 67827603818346499219940327)
        ·
          refine ⟨101741405727519748829910491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67827603818346499219940327 101741405727519748829910491)
          ·
            refine ⟨152612108591279623244865737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101741405727519748829910491 152612108591279623244865737)
            ·
              refine ⟨114459081443459717433649303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152612108591279623244865737 114459081443459717433649303)
              ·
                refine ⟨171688622165189576150473955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114459081443459717433649303 171688622165189576150473955)
                ·
                  refine ⟨257532933247784364225710933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171688622165189576150473955 257532933247784364225710933)
                  ·
                    refine ⟨1508982030748736509135025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 257532933247784364225710933 1508982030748736509135025)
                    ·
                      refine ⟨1131736523061552381851269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1508982030748736509135025 1131736523061552381851269)
                      ·
                        rfl

theorem cell23_2204049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_2204049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204049 prefixEnd_2204049 := by exact prefixLift 2204049
  have htrace : WordTrace (prefixWord ++ tailWord_2204049) baseStart_2204049 baseEnd_2204049 := by
    simpa [prefixWord, tailWord_2204049, baseEnd_2204049] using wordTrace_append hprefix tailTrace_2204049
  have hstable : (prefixWord ++ tailWord_2204049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204049).length < 2 ^ (prefixWord ++ tailWord_2204049).sum := by decide
  have hdescent : baseEnd_2204049 < baseStart_2204049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204056 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2204056 : Nat := 118140960795 + 2204056 * 2 ^ 59
def prefixEnd_2204056 : Nat := 4983230072969 + 3 ^ 40 * 2204056 * 2
def baseEnd_2204056 : Nat := 1131740117426133854463737

theorem tailTrace_2204056 : CollatzResearch.WordTrace tailWord_2204056 prefixEnd_2204056 1131740117426133854463737 := by
  unfold tailWord_2204056
  simp only [CollatzResearch.WordTrace]
  refine ⟨40194263251544504820680011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53592351002059339760906681 40194263251544504820680011)
  ·
    refine ⟨60291394877316757231020017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40194263251544504820680011 60291394877316757231020017)
    ·
      refine ⟨45218546157987567923265013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60291394877316757231020017 45218546157987567923265013)
      ·
        refine ⟨4239238702311334492806095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45218546157987567923265013 4239238702311334492806095)
        ·
          refine ⟨6358858053467001739209143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239238702311334492806095 6358858053467001739209143)
          ·
            refine ⟨9538287080200502608813715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358858053467001739209143 9538287080200502608813715)
            ·
              refine ⟨14307430620300753913220573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9538287080200502608813715 14307430620300753913220573)
              ·
                refine ⟨5365286482612782717457715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14307430620300753913220573 5365286482612782717457715)
                ·
                  refine ⟨8047929723919174076186573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365286482612782717457715 8047929723919174076186573)
                  ·
                    refine ⟨3017973646469690278569965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8047929723919174076186573 3017973646469690278569965)
                    ·
                      refine ⟨1131740117426133854463737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3017973646469690278569965 1131740117426133854463737)
                      ·
                        rfl

theorem cell23_2204056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2204056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204056 prefixEnd_2204056 := by exact prefixLift 2204056
  have htrace : WordTrace (prefixWord ++ tailWord_2204056) baseStart_2204056 baseEnd_2204056 := by
    simpa [prefixWord, tailWord_2204056, baseEnd_2204056] using wordTrace_append hprefix tailTrace_2204056
  have hstable : (prefixWord ++ tailWord_2204056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204056).length < 2 ^ (prefixWord ++ tailWord_2204056).sum := by decide
  have hdescent : baseEnd_2204056 < baseStart_2204056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204074 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2204074 : Nat := 118140960795 + 2204074 * 2 ^ 59
def prefixEnd_2204074 : Nat := 4983230072969 + 3 ^ 40 * 2204074 * 2
def baseEnd_2204074 : Nat := 1131749360077914784038655

theorem tailTrace_2204074 : CollatzResearch.WordTrace tailWord_2204074 prefixEnd_2204074 1131749360077914784038655 := by
  unfold tailWord_2204074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20097295754255949678878819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53592788678015865810343517 20097295754255949678878819)
  ·
    refine ⟨30145943631383924518318229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20097295754255949678878819 30145943631383924518318229)
    ·
      refine ⟨1413091107721121461796167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30145943631383924518318229 1413091107721121461796167)
      ·
        refine ⟨2119636661581682192694251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413091107721121461796167 2119636661581682192694251)
        ·
          refine ⟨3179454992372523289041377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119636661581682192694251 3179454992372523289041377)
          ·
            refine ⟨2384591244279392466781033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179454992372523289041377 2384591244279392466781033)
            ·
              refine ⟨1788443433209544350085775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384591244279392466781033 1788443433209544350085775)
              ·
                refine ⟨2682665149814316525128663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788443433209544350085775 2682665149814316525128663)
                ·
                  refine ⟨4023997724721474787692995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682665149814316525128663 4023997724721474787692995)
                  ·
                    refine ⟨6035996587082212181539493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023997724721474787692995 6035996587082212181539493)
                    ·
                      refine ⟨1131749360077914784038655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6035996587082212181539493 1131749360077914784038655)
                      ·
                        rfl

theorem cell23_2204074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2204074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204074 prefixEnd_2204074 := by exact prefixLift 2204074
  have htrace : WordTrace (prefixWord ++ tailWord_2204074) baseStart_2204074 baseEnd_2204074 := by
    simpa [prefixWord, tailWord_2204074, baseEnd_2204074] using wordTrace_append hprefix tailTrace_2204074
  have hstable : (prefixWord ++ tailWord_2204074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204074).length < 2 ^ (prefixWord ++ tailWord_2204074).sum := by decide
  have hdescent : baseEnd_2204074 < baseStart_2204074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204077 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2204077 : Nat := 118140960795 + 2204077 * 2 ^ 59
def prefixEnd_2204077 : Nat := 4983230072969 + 3 ^ 40 * 2204077 * 2
def baseEnd_2204077 : Nat := 1131750900519878272301141

theorem tailTrace_2204077 : CollatzResearch.WordTrace tailWord_2204077 prefixEnd_2204077 1131750900519878272301141 := by
  unfold tailWord_2204077
  simp only [CollatzResearch.WordTrace]
  refine ⟨80389292436012930227874485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53592861624008620151916323 80389292436012930227874485)
  ·
    refine ⟨7536496165876212208863233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80389292436012930227874485 7536496165876212208863233)
    ·
      refine ⟨5652372124407159156647425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7536496165876212208863233 5652372124407159156647425)
      ·
        refine ⟨4239279093305369367485569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5652372124407159156647425 4239279093305369367485569)
        ·
          refine ⟨3179459319979027025614177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4239279093305369367485569 3179459319979027025614177)
          ·
            refine ⟨2384594489984270269210633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179459319979027025614177 2384594489984270269210633)
            ·
              refine ⟨1788445867488202701907975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384594489984270269210633 1788445867488202701907975)
              ·
                refine ⟨2682668801232304052861963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788445867488202701907975 2682668801232304052861963)
                ·
                  refine ⟨4024003201848456079292945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682668801232304052861963 4024003201848456079292945)
                  ·
                    refine ⟨3018002401386342059469709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4024003201848456079292945 3018002401386342059469709)
                    ·
                      refine ⟨1131750900519878272301141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018002401386342059469709 1131750900519878272301141)
                      ·
                        rfl

theorem cell23_2204077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2204077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204077 prefixEnd_2204077 := by exact prefixLift 2204077
  have htrace : WordTrace (prefixWord ++ tailWord_2204077) baseStart_2204077 baseEnd_2204077 := by
    simpa [prefixWord, tailWord_2204077, baseEnd_2204077] using wordTrace_append hprefix tailTrace_2204077
  have hstable : (prefixWord ++ tailWord_2204077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204077).length < 2 ^ (prefixWord ++ tailWord_2204077).sum := by decide
  have hdescent : baseEnd_2204077 < baseStart_2204077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204084 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2204084 : Nat := 118140960795 + 2204084 * 2 ^ 59
def prefixEnd_2204084 : Nat := 4983230072969 + 3 ^ 40 * 2204084 * 2
def baseEnd_2204084 : Nat := 377251498294819914971203

theorem tailTrace_2204084 : CollatzResearch.WordTrace tailWord_2204084 prefixEnd_2204084 377251498294819914971203 := by
  unfold tailWord_2204084
  simp only [CollatzResearch.WordTrace]
  refine ⟨40194773873493785211689653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53593031831325046948919537 40194773873493785211689653)
  ·
    refine ⟨3768260050640042363595905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40194773873493785211689653 3768260050640042363595905)
    ·
      refine ⟨2826195037980031772696929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3768260050640042363595905 2826195037980031772696929)
      ·
        refine ⟨2119646278485023829522697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2826195037980031772696929 2119646278485023829522697)
        ·
          refine ⟨1589734708863767872142023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2119646278485023829522697 1589734708863767872142023)
          ·
            refine ⟨2384602063295651808213035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589734708863767872142023 2384602063295651808213035)
            ·
              refine ⟨3576903094943477712319553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384602063295651808213035 3576903094943477712319553)
              ·
                refine ⟨2682677321207608284239665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3576903094943477712319553 2682677321207608284239665)
                ·
                  refine ⟨2012007990905706213179749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682677321207608284239665 2012007990905706213179749)
                  ·
                    refine ⟨377251498294819914971203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012007990905706213179749 377251498294819914971203)
                    ·
                      rfl

theorem cell23_2204084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2204084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204084 prefixEnd_2204084 := by exact prefixLift 2204084
  have htrace : WordTrace (prefixWord ++ tailWord_2204084) baseStart_2204084 baseEnd_2204084 := by
    simpa [prefixWord, tailWord_2204084, baseEnd_2204084] using wordTrace_append hprefix tailTrace_2204084
  have hstable : (prefixWord ++ tailWord_2204084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204084).length < 2 ^ (prefixWord ++ tailWord_2204084).sum := by decide
  have hdescent : baseEnd_2204084 < baseStart_2204084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204089 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_2204089 : Nat := 118140960795 + 2204089 * 2 ^ 59
def prefixEnd_2204089 : Nat := 4983230072969 + 3 ^ 40 * 2204089 * 2
def baseEnd_2204089 : Nat := 377252354095910741783695

theorem tailTrace_2204089 : CollatzResearch.WordTrace tailWord_2204089 prefixEnd_2204089 377252354095910741783695 := by
  unfold tailWord_2204089
  simp only [CollatzResearch.WordTrace]
  refine ⟨80389730111969456277311321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53593153407979637518207547 80389730111969456277311321)
  ·
    refine ⟨60292297583977092207983491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80389730111969456277311321 60292297583977092207983491)
    ·
      refine ⟨90438446375965638311975237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60292297583977092207983491 90438446375965638311975237)
      ·
        refine ⟨16957208695493557183495357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90438446375965638311975237 16957208695493557183495357)
        ·
          refine ⟨6358953260810083943810759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16957208695493557183495357 6358953260810083943810759)
          ·
            refine ⟨9538429891215125915716139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358953260810083943810759 9538429891215125915716139)
            ·
              refine ⟨14307644836822688873574209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9538429891215125915716139 14307644836822688873574209)
              ·
                refine ⟨10730733627617016655180657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14307644836822688873574209 10730733627617016655180657)
                ·
                  refine ⟨8048050220712762491385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10730733627617016655180657 8048050220712762491385493)
                  ·
                    refine ⟨377252354095910741783695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8048050220712762491385493 377252354095910741783695)
                    ·
                      rfl

theorem cell23_2204089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_2204089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204089 prefixEnd_2204089 := by exact prefixLift 2204089
  have htrace : WordTrace (prefixWord ++ tailWord_2204089) baseStart_2204089 baseEnd_2204089 := by
    simpa [prefixWord, tailWord_2204089, baseEnd_2204089] using wordTrace_append hprefix tailTrace_2204089
  have hstable : (prefixWord ++ tailWord_2204089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204089).length < 2 ^ (prefixWord ++ tailWord_2204089).sum := by decide
  have hdescent : baseEnd_2204089 < baseStart_2204089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204113 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_2204113 : Nat := 118140960795 + 2204113 * 2 ^ 59
def prefixEnd_2204113 : Nat := 4983230072969 + 3 ^ 40 * 2204113 * 2
def baseEnd_2204113 : Nat := 1131769385823440131450975

theorem tailTrace_2204113 : CollatzResearch.WordTrace tailWord_2204113 prefixEnd_2204113 1131769385823440131450975 := by
  unfold tailWord_2204113
  simp only [CollatzResearch.WordTrace]
  refine ⟨80390605463882508376184993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53593736975921672250789995 80390605463882508376184993)
  ·
    refine ⟨60292954097911881282138745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80390605463882508376184993 60292954097911881282138745)
    ·
      refine ⟨45219715573433910961604059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60292954097911881282138745 45219715573433910961604059)
      ·
        refine ⟨67829573360150866442406089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45219715573433910961604059 67829573360150866442406089)
        ·
          refine ⟨50872180020113149831804567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67829573360150866442406089 50872180020113149831804567)
          ·
            refine ⟨76308270030169724747706851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50872180020113149831804567 76308270030169724747706851)
            ·
              refine ⟨114462405045254587121560277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76308270030169724747706851 114462405045254587121560277)
              ·
                refine ⟨2682712618248154385661569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114462405045254587121560277 2682712618248154385661569)
                ·
                  refine ⟨2012034463686115789246177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682712618248154385661569 2012034463686115789246177)
                  ·
                    refine ⟨1509025847764586841934633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012034463686115789246177 1509025847764586841934633)
                    ·
                      refine ⟨1131769385823440131450975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509025847764586841934633 1131769385823440131450975)
                      ·
                        rfl

theorem cell23_2204113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_2204113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204113 prefixEnd_2204113 := by exact prefixLift 2204113
  have htrace : WordTrace (prefixWord ++ tailWord_2204113) baseStart_2204113 baseEnd_2204113 := by
    simpa [prefixWord, tailWord_2204113, baseEnd_2204113] using wordTrace_append hprefix tailTrace_2204113
  have hstable : (prefixWord ++ tailWord_2204113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204113).length < 2 ^ (prefixWord ++ tailWord_2204113).sum := by decide
  have hdescent : baseEnd_2204113 < baseStart_2204113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204156 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_2204156 : Nat := 118140960795 + 2204156 * 2 ^ 59
def prefixEnd_2204156 : Nat := 4983230072969 + 3 ^ 40 * 2204156 * 2
def baseEnd_2204156 : Nat := 1131791465491583463213277

theorem tailTrace_2204156 : CollatzResearch.WordTrace tailWord_2204156 prefixEnd_2204156 1131791465491583463213277 := by
  unfold tailWord_2204156
  simp only [CollatzResearch.WordTrace]
  refine ⟨40196086901363363360000161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53594782535151151146666881 40196086901363363360000161)
  ·
    refine ⟨30147065176022522520000121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40196086901363363360000161 30147065176022522520000121)
    ·
      refine ⟨22610298882016891890000091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30147065176022522520000121 22610298882016891890000091)
      ·
        refine ⟨33915448323025337835000137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22610298882016891890000091 33915448323025337835000137)
        ·
          refine ⟨25436586242269003376250103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33915448323025337835000137 25436586242269003376250103)
          ·
            refine ⟨38154879363403505064375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25436586242269003376250103 38154879363403505064375155)
            ·
              refine ⟨57232319045105257596562733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38154879363403505064375155 57232319045105257596562733)
              ·
                refine ⟨21462119641914471598711025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57232319045105257596562733 21462119641914471598711025)
                ·
                  refine ⟨16096589731435853699033269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21462119641914471598711025 16096589731435853699033269)
                  ·
                    refine ⟨1509055287322111284284369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16096589731435853699033269 1509055287322111284284369)
                    ·
                      refine ⟨1131791465491583463213277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509055287322111284284369 1131791465491583463213277)
                      ·
                        rfl

theorem cell23_2204156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_2204156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204156 prefixEnd_2204156 := by exact prefixLift 2204156
  have htrace : WordTrace (prefixWord ++ tailWord_2204156) baseStart_2204156 baseEnd_2204156 := by
    simpa [prefixWord, tailWord_2204156, baseEnd_2204156] using wordTrace_append hprefix tailTrace_2204156
  have hstable : (prefixWord ++ tailWord_2204156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204156).length < 2 ^ (prefixWord ++ tailWord_2204156).sum := by decide
  have hdescent : baseEnd_2204156 < baseStart_2204156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204159 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_2204159 : Nat := 118140960795 + 2204159 * 2 ^ 59
def prefixEnd_2204159 : Nat := 4983230072969 + 3 ^ 40 * 2204159 * 2
def baseEnd_2204159 : Nat := 1131793005933546951475763

theorem tailTrace_2204159 : CollatzResearch.WordTrace tailWord_2204159 prefixEnd_2204159 1131793005933546951475763 := by
  unfold tailWord_2204159
  simp only [CollatzResearch.WordTrace]
  refine ⟨80392283221715858232359531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53594855481143905488239687 80392283221715858232359531)
  ·
    refine ⟨120588424832573787348539297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80392283221715858232359531 120588424832573787348539297)
    ·
      refine ⟨90441318624430340511404473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120588424832573787348539297 90441318624430340511404473)
      ·
        refine ⟨67830988968322755383553355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90441318624430340511404473 67830988968322755383553355)
        ·
          refine ⟨101746483452484133075330033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67830988968322755383553355 101746483452484133075330033)
          ·
            refine ⟨76309862589363099806497525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101746483452484133075330033 76309862589363099806497525)
            ·
              refine ⟨7154049617752790606859143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76309862589363099806497525 7154049617752790606859143)
              ·
                refine ⟨10731074426629185910288715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154049617752790606859143 10731074426629185910288715)
                ·
                  refine ⟨16096611639943778865433073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731074426629185910288715 16096611639943778865433073)
                  ·
                    refine ⟨12072458729957834149074805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16096611639943778865433073 12072458729957834149074805)
                    ·
                      refine ⟨1131793005933546951475763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12072458729957834149074805 1131793005933546951475763)
                      ·
                        rfl

theorem cell23_2204159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_2204159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204159 prefixEnd_2204159 := by exact prefixLift 2204159
  have htrace : WordTrace (prefixWord ++ tailWord_2204159) baseStart_2204159 baseEnd_2204159 := by
    simpa [prefixWord, tailWord_2204159, baseEnd_2204159] using wordTrace_append hprefix tailTrace_2204159
  have hstable : (prefixWord ++ tailWord_2204159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204159).length < 2 ^ (prefixWord ++ tailWord_2204159).sum := by decide
  have hdescent : baseEnd_2204159 < baseStart_2204159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204164 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2204164 : Nat := 118140960795 + 2204164 * 2 ^ 59
def prefixEnd_2204164 : Nat := 4983230072969 + 3 ^ 40 * 2204164 * 2
def baseEnd_2204164 : Nat := 1131795573336819431913241

theorem tailTrace_2204164 : CollatzResearch.WordTrace tailWord_2204164 prefixEnd_2204164 1131795573336819431913241 := by
  unfold tailWord_2204164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40196232793348872043145773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53594977057798496057527697 40196232793348872043145773)
  ·
    refine ⟨15073587297505827016179665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40196232793348872043145773 15073587297505827016179665)
    ·
      refine ⟨11305190473129370262134749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15073587297505827016179665 11305190473129370262134749)
      ·
        refine ⟨4239446427423513848300531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11305190473129370262134749 4239446427423513848300531)
        ·
          refine ⟨6359169641135270772450797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239446427423513848300531 6359169641135270772450797)
          ·
            refine ⟨2384688615425726539669049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6359169641135270772450797 2384688615425726539669049)
            ·
              refine ⟨1788516461569294904751787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384688615425726539669049 1788516461569294904751787)
              ·
                refine ⟨2682774692353942357127681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788516461569294904751787 2682774692353942357127681)
                ·
                  refine ⟨2012081019265456767845761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682774692353942357127681 2012081019265456767845761)
                  ·
                    refine ⟨1509060764449092575884321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012081019265456767845761 1509060764449092575884321)
                    ·
                      refine ⟨1131795573336819431913241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509060764449092575884321 1131795573336819431913241)
                      ·
                        rfl

theorem cell23_2204164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2204164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204164 prefixEnd_2204164 := by exact prefixLift 2204164
  have htrace : WordTrace (prefixWord ++ tailWord_2204164) baseStart_2204164 baseEnd_2204164 := by
    simpa [prefixWord, tailWord_2204164, baseEnd_2204164] using wordTrace_append hprefix tailTrace_2204164
  have hstable : (prefixWord ++ tailWord_2204164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204164).length < 2 ^ (prefixWord ++ tailWord_2204164).sum := by decide
  have hdescent : baseEnd_2204164 < baseStart_2204164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204169 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_2204169 : Nat := 118140960795 + 2204169 * 2 ^ 59
def prefixEnd_2204169 : Nat := 4983230072969 + 3 ^ 40 * 2204169 * 2
def baseEnd_2204169 : Nat := 1131798140740091912350717

theorem tailTrace_2204169 : CollatzResearch.WordTrace tailWord_2204169 prefixEnd_2204169 1131798140740091912350717 := by
  unfold tailWord_2204169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80392647951679629940223561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53595098634453086626815707 80392647951679629940223561)
  ·
    refine ⟨60294485963759722455167671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80392647951679629940223561 60294485963759722455167671)
    ·
      refine ⟨90441728945639583682751507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60294485963759722455167671 90441728945639583682751507)
      ·
        refine ⟨135662593418459375524127261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90441728945639583682751507 135662593418459375524127261)
        ·
          refine ⟨50873472531922265821547723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135662593418459375524127261 50873472531922265821547723)
          ·
            refine ⟨76310208797883398732321585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50873472531922265821547723 76310208797883398732321585)
            ·
              refine ⟨57232656598412549049241189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76310208797883398732321585 57232656598412549049241189)
              ·
                refine ⟨10731123112202352946732723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57232656598412549049241189 10731123112202352946732723)
                ·
                  refine ⟨16096684668303529420099085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731123112202352946732723 16096684668303529420099085)
                  ·
                    refine ⟨6036256750613823532537157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16096684668303529420099085 6036256750613823532537157)
                    ·
                      refine ⟨1131798140740091912350717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6036256750613823532537157 1131798140740091912350717)
                      ·
                        rfl

theorem cell23_2204169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_2204169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204169 prefixEnd_2204169 := by exact prefixLift 2204169
  have htrace : WordTrace (prefixWord ++ tailWord_2204169) baseStart_2204169 baseEnd_2204169 := by
    simpa [prefixWord, tailWord_2204169, baseEnd_2204169] using wordTrace_append hprefix tailTrace_2204169
  have hstable : (prefixWord ++ tailWord_2204169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204169).length < 2 ^ (prefixWord ++ tailWord_2204169).sum := by decide
  have hdescent : baseEnd_2204169 < baseStart_2204169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204186 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2204186 : Nat := 118140960795 + 2204186 * 2 ^ 59
def prefixEnd_2204186 : Nat := 4983230072969 + 3 ^ 40 * 2204186 * 2
def baseEnd_2204186 : Nat := 1131806869911218345838139

theorem tailTrace_2204186 : CollatzResearch.WordTrace tailWord_2204186 prefixEnd_2204186 1131806869911218345838139 := by
  unfold tailWord_2204186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20098316998154510460898103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53595511995078694562394941 20098316998154510460898103)
  ·
    refine ⟨30147475497231765691347155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20098316998154510460898103 30147475497231765691347155)
    ·
      refine ⟨45221213245847648537020733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30147475497231765691347155 45221213245847648537020733)
      ·
        refine ⟨16957954967192868201382775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45221213245847648537020733 16957954967192868201382775)
        ·
          refine ⟨25436932450789302302074163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16957954967192868201382775 25436932450789302302074163)
          ·
            refine ⟨38155398676183953453111245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25436932450789302302074163 38155398676183953453111245)
            ·
              refine ⟨14308274503568982544916717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38155398676183953453111245 14308274503568982544916717)
              ·
                refine ⟨5365602938838368454343769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14308274503568982544916717 5365602938838368454343769)
                ·
                  refine ⟨4024202204128776340757827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5365602938838368454343769 4024202204128776340757827)
                  ·
                    refine ⟨6036303306193164511136741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024202204128776340757827 6036303306193164511136741)
                    ·
                      refine ⟨1131806869911218345838139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6036303306193164511136741 1131806869911218345838139)
                      ·
                        rfl

theorem cell23_2204186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2204186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204186 prefixEnd_2204186 := by exact prefixLift 2204186
  have htrace : WordTrace (prefixWord ++ tailWord_2204186) baseStart_2204186 baseEnd_2204186 := by
    simpa [prefixWord, tailWord_2204186, baseEnd_2204186] using wordTrace_append hprefix tailTrace_2204186
  have hstable : (prefixWord ++ tailWord_2204186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204186).length < 2 ^ (prefixWord ++ tailWord_2204186).sum := by decide
  have hdescent : baseEnd_2204186 < baseStart_2204186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204209 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 8]
def baseStart_2204209 : Nat := 118140960795 + 2204209 * 2 ^ 59
def prefixEnd_2204209 : Nat := 4983230072969 + 3 ^ 40 * 2204209 * 2
def baseEnd_2204209 : Nat := 125757631107363528427837

theorem tailTrace_2204209 : CollatzResearch.WordTrace tailWord_2204209 prefixEnd_2204209 125757631107363528427837 := by
  unfold tailWord_2204209
  simp only [CollatzResearch.WordTrace]
  refine ⟨80394106871534716771679681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53596071247689811181119787 80394106871534716771679681)
  ·
    refine ⟨60295580153651037578759761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80394106871534716771679681 60295580153651037578759761)
    ·
      refine ⟨45221685115238278184069821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60295580153651037578759761 45221685115238278184069821)
      ·
        refine ⟨16958131918214354319026183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45221685115238278184069821 16958131918214354319026183)
        ·
          refine ⟨25437197877321531478539275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16958131918214354319026183 25437197877321531478539275)
          ·
            refine ⟨38155796815982297217808913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25437197877321531478539275 38155796815982297217808913)
            ·
              refine ⟨28616847611986722913356685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38155796815982297217808913 28616847611986722913356685)
              ·
                refine ⟨10731317854495021092508757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28616847611986722913356685 10731317854495021092508757)
                ·
                  refine ⟨125757631107363528427837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10731317854495021092508757 125757631107363528427837)
                  ·
                    rfl

theorem cell23_2204209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_2204209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204209 prefixEnd_2204209 := by exact prefixLift 2204209
  have htrace : WordTrace (prefixWord ++ tailWord_2204209) baseStart_2204209 baseEnd_2204209 := by
    simpa [prefixWord, tailWord_2204209, baseEnd_2204209] using wordTrace_append hprefix tailTrace_2204209
  have hstable : (prefixWord ++ tailWord_2204209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204209).length < 2 ^ (prefixWord ++ tailWord_2204209).sum := by decide
  have hdescent : baseEnd_2204209 < baseStart_2204209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204230 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_2204230 : Nat := 118140960795 + 2204230 * 2 ^ 59
def prefixEnd_2204230 : Nat := 4983230072969 + 3 ^ 40 * 2204230 * 2
def baseEnd_2204230 : Nat := 377276487686672057895979

theorem tailTrace_2204230 : CollatzResearch.WordTrace tailWord_2204230 prefixEnd_2204230 377276487686672057895979 := by
  unfold tailWord_2204230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512339775139332417443567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53596581869639091572129429 2512339775139332417443567)
  ·
    refine ⟨3768509662708998626165351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512339775139332417443567 3768509662708998626165351)
    ·
      refine ⟨5652764494063497939248027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3768509662708998626165351 5652764494063497939248027)
      ·
        refine ⟨8479146741095246908872041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652764494063497939248027 8479146741095246908872041)
        ·
          refine ⟨6359360055821435181654031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479146741095246908872041 6359360055821435181654031)
          ·
            refine ⟨9539040083732152772481047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359360055821435181654031 9539040083732152772481047)
            ·
              refine ⟨14308560125598229158721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9539040083732152772481047 14308560125598229158721571)
              ·
                refine ⟨21462840188397343738082357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14308560125598229158721571 21462840188397343738082357)
                ·
                  refine ⟨2012141267662250975445221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21462840188397343738082357 2012141267662250975445221)
                  ·
                    refine ⟨377276487686672057895979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012141267662250975445221 377276487686672057895979)
                    ·
                      rfl

theorem cell23_2204230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_2204230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204230 prefixEnd_2204230 := by exact prefixLift 2204230
  have htrace : WordTrace (prefixWord ++ tailWord_2204230) baseStart_2204230 baseEnd_2204230 := by
    simpa [prefixWord, tailWord_2204230, baseEnd_2204230] using wordTrace_append hprefix tailTrace_2204230
  have hstable : (prefixWord ++ tailWord_2204230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204230).length < 2 ^ (prefixWord ++ tailWord_2204230).sum := by decide
  have hdescent : baseEnd_2204230 < baseStart_2204230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204249 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_2204249 : Nat := 118140960795 + 2204249 * 2 ^ 59
def prefixEnd_2204249 : Nat := 4983230072969 + 3 ^ 40 * 2204249 * 2
def baseEnd_2204249 : Nat := 1131839219192451599350349

theorem tailTrace_2204249 : CollatzResearch.WordTrace tailWord_2204249 prefixEnd_2204249 1131839219192451599350349 := by
  unfold tailWord_2204249
  simp only [CollatzResearch.WordTrace]
  refine ⟨80395565791389803603135801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53597043860926535735423867 80395565791389803603135801)
  ·
    refine ⟨60296674343542352702351851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80395565791389803603135801 60296674343542352702351851)
    ·
      refine ⟨90445011515313529053527777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60296674343542352702351851 90445011515313529053527777)
      ·
        refine ⟨67833758636485146790145833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90445011515313529053527777 67833758636485146790145833)
        ·
          refine ⟨50875318977363860092609375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67833758636485146790145833 50875318977363860092609375)
          ·
            refine ⟨76312978466045790138914063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50875318977363860092609375 76312978466045790138914063)
            ·
              refine ⟨114469467699068685208371095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76312978466045790138914063 114469467699068685208371095)
              ·
                refine ⟨171704201548603027812556643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114469467699068685208371095 171704201548603027812556643)
                ·
                  refine ⟨257556302322904541718834965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171704201548603027812556643 257556302322904541718834965)
                  ·
                    refine ⟨12072951671386150393070389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 257556302322904541718834965 12072951671386150393070389)
                    ·
                      refine ⟨1131839219192451599350349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12072951671386150393070389 1131839219192451599350349)
                      ·
                        rfl

theorem cell23_2204249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_2204249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204249 prefixEnd_2204249 := by exact prefixLift 2204249
  have htrace : WordTrace (prefixWord ++ tailWord_2204249) baseStart_2204249 baseEnd_2204249 := by
    simpa [prefixWord, tailWord_2204249, baseEnd_2204249] using wordTrace_append hprefix tailTrace_2204249
  have hstable : (prefixWord ++ tailWord_2204249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204249).length < 2 ^ (prefixWord ++ tailWord_2204249).sum := by decide
  have hdescent : baseEnd_2204249 < baseStart_2204249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204263 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_2204263 : Nat := 118140960795 + 2204263 * 2 ^ 59
def prefixEnd_2204263 : Nat := 4983230072969 + 3 ^ 40 * 2204263 * 2
def baseEnd_2204263 : Nat := 1131846407921614544575285

theorem tailTrace_2204263 : CollatzResearch.WordTrace tailWord_2204263 prefixEnd_2204263 1131846407921614544575285 := by
  unfold tailWord_2204263
  simp only [CollatzResearch.WordTrace]
  refine ⟨80396076413339083994145443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53597384275559389329430295 80396076413339083994145443)
  ·
    refine ⟨120594114620008625991218165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80396076413339083994145443 120594114620008625991218165)
    ·
      refine ⟨11305698245625808686676703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120594114620008625991218165 11305698245625808686676703)
      ·
        refine ⟨16958547368438713030015055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11305698245625808686676703 16958547368438713030015055)
        ·
          refine ⟨25437821052658069545022583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16958547368438713030015055 25437821052658069545022583)
          ·
            refine ⟨38156731578987104317533875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25437821052658069545022583 38156731578987104317533875)
            ·
              refine ⟨57235097368480656476300813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38156731578987104317533875 57235097368480656476300813)
              ·
                refine ⟨21463161513180246178612805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57235097368480656476300813 21463161513180246178612805)
                ·
                  refine ⟨4024342783721296158489901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21463161513180246178612805 4024342783721296158489901)
                  ·
                    refine ⟨1509128543895486059433713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4024342783721296158489901 1509128543895486059433713)
                    ·
                      refine ⟨1131846407921614544575285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509128543895486059433713 1131846407921614544575285)
                      ·
                        rfl

theorem cell23_2204263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_2204263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204263 prefixEnd_2204263 := by exact prefixLift 2204263
  have htrace : WordTrace (prefixWord ++ tailWord_2204263) baseStart_2204263 baseEnd_2204263 := by
    simpa [prefixWord, tailWord_2204263, baseEnd_2204263] using wordTrace_append hprefix tailTrace_2204263
  have hstable : (prefixWord ++ tailWord_2204263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204263).length < 2 ^ (prefixWord ++ tailWord_2204263).sum := by decide
  have hdescent : baseEnd_2204263 < baseStart_2204263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204270 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2204270 : Nat := 118140960795 + 2204270 * 2 ^ 59
def prefixEnd_2204270 : Nat := 4983230072969 + 3 ^ 40 * 2204270 * 2
def baseEnd_2204270 : Nat := 1131850002286196017187753

theorem tailTrace_2204270 : CollatzResearch.WordTrace tailWord_2204270 prefixEnd_2204270 1131850002286196017187753 := by
  unfold tailWord_2204270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049541465539215523706283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53597554482875816126433509 10049541465539215523706283)
  ·
    refine ⟨15074312198308823285559425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10049541465539215523706283 15074312198308823285559425)
    ·
      refine ⟨11305734148731617464169569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15074312198308823285559425 11305734148731617464169569)
      ·
        refine ⟨8479300611548713098127177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11305734148731617464169569 8479300611548713098127177)
        ·
          refine ⟨6359475458661534823595383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479300611548713098127177 6359475458661534823595383)
          ·
            refine ⟨9539213187992302235393075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359475458661534823595383 9539213187992302235393075)
            ·
              refine ⟨14308819781988453353089613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9539213187992302235393075 14308819781988453353089613)
              ·
                refine ⟨5365807418245670007408605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14308819781988453353089613 5365807418245670007408605)
                ·
                  refine ⟨2012177781842126252778227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5365807418245670007408605 2012177781842126252778227)
                  ·
                    refine ⟨3018266672763189379167341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012177781842126252778227 3018266672763189379167341)
                    ·
                      refine ⟨1131850002286196017187753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018266672763189379167341 1131850002286196017187753)
                      ·
                        rfl

theorem cell23_2204270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2204270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204270 prefixEnd_2204270 := by exact prefixLift 2204270
  have htrace : WordTrace (prefixWord ++ tailWord_2204270) baseStart_2204270 baseEnd_2204270 := by
    simpa [prefixWord, tailWord_2204270, baseEnd_2204270] using wordTrace_append hprefix tailTrace_2204270
  have hstable : (prefixWord ++ tailWord_2204270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204270).length < 2 ^ (prefixWord ++ tailWord_2204270).sum := by decide
  have hdescent : baseEnd_2204270 < baseStart_2204270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204293 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_2204293 : Nat := 118140960795 + 2204293 * 2 ^ 59
def prefixEnd_2204293 : Nat := 4983230072969 + 3 ^ 40 * 2204293 * 2
def baseEnd_2204293 : Nat := 1131861812341249427200147

theorem tailTrace_2204293 : CollatzResearch.WordTrace tailWord_2204293 prefixEnd_2204293 1131861812341249427200147 := by
  unfold tailWord_2204293
  simp only [CollatzResearch.WordTrace]
  refine ⟨80397170603230399117737533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53598113735486932745158355 80397170603230399117737533)
  ·
    refine ⟨30148938976211399669151575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80397170603230399117737533 30148938976211399669151575)
    ·
      refine ⟨45223408464317099503727363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30148938976211399669151575 45223408464317099503727363)
      ·
        refine ⟨67835112696475649255591045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45223408464317099503727363 67835112696475649255591045)
        ·
          refine ⟨12719083630589184235423321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67835112696475649255591045 12719083630589184235423321)
          ·
            refine ⟨9539312722941888176567491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12719083630589184235423321 9539312722941888176567491)
            ·
              refine ⟨14308969084412832264851237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9539312722941888176567491 14308969084412832264851237)
              ·
                refine ⟨2682931703327406049659607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14308969084412832264851237 2682931703327406049659607)
                ·
                  refine ⟨4024397554991109074489411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682931703327406049659607 4024397554991109074489411)
                  ·
                    refine ⟨6036596332486663611734117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024397554991109074489411 6036596332486663611734117)
                    ·
                      refine ⟨1131861812341249427200147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6036596332486663611734117 1131861812341249427200147)
                      ·
                        rfl

theorem cell23_2204293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_2204293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204293 prefixEnd_2204293 := by exact prefixLift 2204293
  have htrace : WordTrace (prefixWord ++ tailWord_2204293) baseStart_2204293 baseEnd_2204293 := by
    simpa [prefixWord, tailWord_2204293, baseEnd_2204293] using wordTrace_append hprefix tailTrace_2204293
  have hstable : (prefixWord ++ tailWord_2204293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204293).length < 2 ^ (prefixWord ++ tailWord_2204293).sum := by decide
  have hdescent : baseEnd_2204293 < baseStart_2204293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204313 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_2204313 : Nat := 118140960795 + 2204313 * 2 ^ 59
def prefixEnd_2204313 : Nat := 4983230072969 + 3 ^ 40 * 2204313 * 2
def baseEnd_2204313 : Nat := 1131872081954339348950055

theorem tailTrace_2204313 : CollatzResearch.WordTrace tailWord_2204313 prefixEnd_2204313 1131872081954339348950055 := by
  unfold tailWord_2204313
  simp only [CollatzResearch.WordTrace]
  refine ⟨80397900063157942533465593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53598600042105295022310395 80397900063157942533465593)
  ·
    refine ⟨60298425047368456900099195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80397900063157942533465593 60298425047368456900099195)
    ·
      refine ⟨90447637571052685350148793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60298425047368456900099195 90447637571052685350148793)
      ·
        refine ⟨67835728178289514012611595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90447637571052685350148793 67835728178289514012611595)
        ·
          refine ⟨101753592267434271018917393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67835728178289514012611595 101753592267434271018917393)
          ·
            refine ⟨76315194200575703264188045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101753592267434271018917393 76315194200575703264188045)
            ·
              refine ⟨28618197825215888724070517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76315194200575703264188045 28618197825215888724070517)
              ·
                refine ⟨2682956046113989567881611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28618197825215888724070517 2682956046113989567881611)
                ·
                  refine ⟨4024434069170984351822417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682956046113989567881611 4024434069170984351822417)
                  ·
                    refine ⟨3018325551878238263866813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4024434069170984351822417 3018325551878238263866813)
                    ·
                      refine ⟨1131872081954339348950055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018325551878238263866813 1131872081954339348950055)
                      ·
                        rfl

theorem cell23_2204313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_2204313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204313 prefixEnd_2204313 := by exact prefixLift 2204313
  have htrace : WordTrace (prefixWord ++ tailWord_2204313) baseStart_2204313 baseEnd_2204313 := by
    simpa [prefixWord, tailWord_2204313, baseEnd_2204313] using wordTrace_append hprefix tailTrace_2204313
  have hstable : (prefixWord ++ tailWord_2204313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204313).length < 2 ^ (prefixWord ++ tailWord_2204313).sum := by decide
  have hdescent : baseEnd_2204313 < baseStart_2204313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204316 : List Nat := [2, 2, 3, 2, 2, 1, 11]
def baseStart_2204316 : Nat := 118140960795 + 2204316 * 2 ^ 59
def prefixEnd_2204316 : Nat := 4983230072969 + 3 ^ 40 * 2204316 * 2
def baseEnd_2204316 : Nat := 13973748424645714039661

theorem tailTrace_2204316 : CollatzResearch.WordTrace tailWord_2204316 prefixEnd_2204316 13973748424645714039661 := by
  unfold tailWord_2204316
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199004741073537022912401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53598672988098049363883201 40199004741073537022912401)
  ·
    refine ⟨30149253555805152767184301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40199004741073537022912401 30149253555805152767184301)
    ·
      refine ⟨11305970083426932287694113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30149253555805152767184301 11305970083426932287694113)
      ·
        refine ⟨8479477562570199215770585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11305970083426932287694113 8479477562570199215770585)
        ·
          refine ⟨6359608171927649411827939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8479477562570199215770585 6359608171927649411827939)
          ·
            refine ⟨9539412257891474117741909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359608171927649411827939 9539412257891474117741909)
            ·
              refine ⟨13973748424645714039661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9539412257891474117741909 13973748424645714039661)
              ·
                rfl

theorem cell23_2204316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 11].length) (baseStart_2204316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204316 prefixEnd_2204316 := by exact prefixLift 2204316
  have htrace : WordTrace (prefixWord ++ tailWord_2204316) baseStart_2204316 baseEnd_2204316 := by
    simpa [prefixWord, tailWord_2204316, baseEnd_2204316] using wordTrace_append hprefix tailTrace_2204316
  have hstable : (prefixWord ++ tailWord_2204316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204316).length < 2 ^ (prefixWord ++ tailWord_2204316).sum := by decide
  have hdescent : baseEnd_2204316 < baseStart_2204316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204333 : List Nat := [1, 5, 2, 1, 1, 3, 2, 8]
def baseStart_2204333 : Nat := 118140960795 + 2204333 * 2 ^ 59
def prefixEnd_2204333 : Nat := 4983230072969 + 3 ^ 40 * 2204333 * 2
def baseEnd_2204333 : Nat := 41921568576571454470369

theorem tailTrace_2204333 : CollatzResearch.WordTrace tailWord_2204333 prefixEnd_2204333 41921568576571454470369 := by
  unfold tailWord_2204333
  simp only [CollatzResearch.WordTrace]
  refine ⟨80398629523085485949193653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53599086348723657299462435 80398629523085485949193653)
  ·
    refine ⟨7537371517789264307736905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80398629523085485949193653 7537371517789264307736905)
    ·
      refine ⟨5653028638341948230802679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7537371517789264307736905 5653028638341948230802679)
      ·
        refine ⟨8479542957512922346204019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653028638341948230802679 8479542957512922346204019)
        ·
          refine ⟨12719314436269383519306029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479542957512922346204019 12719314436269383519306029)
          ·
            refine ⟨4769742913601018819739761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12719314436269383519306029 4769742913601018819739761)
            ·
              refine ⟨3577307185200764114804821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4769742913601018819739761 3577307185200764114804821)
              ·
                refine ⟨41921568576571454470369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3577307185200764114804821 41921568576571454470369)
                ·
                  rfl

theorem cell23_2204333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 8].length) (baseStart_2204333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204333 prefixEnd_2204333 := by exact prefixLift 2204333
  have htrace : WordTrace (prefixWord ++ tailWord_2204333) baseStart_2204333 baseEnd_2204333 := by
    simpa [prefixWord, tailWord_2204333, baseEnd_2204333] using wordTrace_append hprefix tailTrace_2204333
  have hstable : (prefixWord ++ tailWord_2204333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204333).length < 2 ^ (prefixWord ++ tailWord_2204333).sum := by decide
  have hdescent : baseEnd_2204333 < baseStart_2204333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204337 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_2204337 : Nat := 118140960795 + 2204337 * 2 ^ 59
def prefixEnd_2204337 : Nat := 4983230072969 + 3 ^ 40 * 2204337 * 2
def baseEnd_2204337 : Nat := 377294801830015751683315

theorem tailTrace_2204337 : CollatzResearch.WordTrace tailWord_2204337 prefixEnd_2204337 377294801830015751683315 := by
  unfold tailWord_2204337
  simp only [CollatzResearch.WordTrace]
  refine ⟨80398775415070994632339265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53599183610047329754892843 80398775415070994632339265)
  ·
    refine ⟨60299081561303245974254449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80398775415070994632339265 60299081561303245974254449)
    ·
      refine ⟨45224311170977434480690837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60299081561303245974254449 45224311170977434480690837)
      ·
        refine ⟨2119889586139567241282383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45224311170977434480690837 2119889586139567241282383)
        ·
          refine ⟨3179834379209350861923575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119889586139567241282383 3179834379209350861923575)
          ·
            refine ⟨4769751568814026292885363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179834379209350861923575 4769751568814026292885363)
            ·
              refine ⟨7154627353221039439328045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4769751568814026292885363 7154627353221039439328045)
              ·
                refine ⟨2682985257457889789748017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7154627353221039439328045 2682985257457889789748017)
                ·
                  refine ⟨2012238943093417342311013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682985257457889789748017 2012238943093417342311013)
                  ·
                    refine ⟨377294801830015751683315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012238943093417342311013 377294801830015751683315)
                    ·
                      rfl

theorem cell23_2204337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_2204337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204337 prefixEnd_2204337 := by exact prefixLift 2204337
  have htrace : WordTrace (prefixWord ++ tailWord_2204337) baseStart_2204337 baseEnd_2204337 := by
    simpa [prefixWord, tailWord_2204337, baseEnd_2204337] using wordTrace_append hprefix tailTrace_2204337
  have hstable : (prefixWord ++ tailWord_2204337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204337).length < 2 ^ (prefixWord ++ tailWord_2204337).sum := by decide
  have hdescent : baseEnd_2204337 < baseStart_2204337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204400 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2]
def baseStart_2204400 : Nat := 118140960795 + 2204400 * 2 ^ 59
def prefixEnd_2204400 : Nat := 4983230072969 + 3 ^ 40 * 2204400 * 2
def baseEnd_2204400 : Nat := 1131916754771280508562155

theorem tailTrace_2204400 : CollatzResearch.WordTrace tailWord_2204400 prefixEnd_2204400 1131916754771280508562155 := by
  unfold tailWord_2204400
  simp only [CollatzResearch.WordTrace]
  refine ⟨40200536606921378195941327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53600715475895170927921769 40200536606921378195941327)
  ·
    refine ⟨60300804910382067293911991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40200536606921378195941327 60300804910382067293911991)
    ·
      refine ⟨90451207365573100940867987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60300804910382067293911991 90451207365573100940867987)
      ·
        refine ⟨135676811048359651411301981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90451207365573100940867987 135676811048359651411301981)
        ·
          refine ⟨50878804143134869279238243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135676811048359651411301981 50878804143134869279238243)
          ·
            refine ⟨76318206214702303918857365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50878804143134869279238243 76318206214702303918857365)
            ·
              refine ⟨3577415916314170496196439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76318206214702303918857365 3577415916314170496196439)
              ·
                refine ⟨5366123874471255744294659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577415916314170496196439 5366123874471255744294659)
                ·
                  refine ⟨8049185811706883616441989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5366123874471255744294659 8049185811706883616441989)
                  ·
                    refine ⟨1509222339695040678082873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8049185811706883616441989 1509222339695040678082873)
                    ·
                      refine ⟨1131916754771280508562155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509222339695040678082873 1131916754771280508562155)
                      ·
                        rfl

theorem cell23_2204400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2].length) (baseStart_2204400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204400 prefixEnd_2204400 := by exact prefixLift 2204400
  have htrace : WordTrace (prefixWord ++ tailWord_2204400) baseStart_2204400 baseEnd_2204400 := by
    simpa [prefixWord, tailWord_2204400, baseEnd_2204400] using wordTrace_append hprefix tailTrace_2204400
  have hstable : (prefixWord ++ tailWord_2204400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204400).length < 2 ^ (prefixWord ++ tailWord_2204400).sum := by decide
  have hdescent : baseEnd_2204400 < baseStart_2204400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204433 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_2204433 : Nat := 118140960795 + 2204433 * 2 ^ 59
def prefixEnd_2204433 : Nat := 4983230072969 + 3 ^ 40 * 2204433 * 2
def baseEnd_2204433 : Nat := 1131933699632878879449503

theorem tailTrace_2204433 : CollatzResearch.WordTrace tailWord_2204433 prefixEnd_2204433 1131933699632878879449503 := by
  unfold tailWord_2204433
  simp only [CollatzResearch.WordTrace]
  refine ⟨80402276822723203027833953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53601517881815468685222635 80402276822723203027833953)
  ·
    refine ⟨60301707617042402270875465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80402276822723203027833953 60301707617042402270875465)
    ·
      refine ⟨45226280712781801703156599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60301707617042402270875465 45226280712781801703156599)
      ·
        refine ⟨67839421069172702554734899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45226280712781801703156599 67839421069172702554734899)
        ·
          refine ⟨101759131603759053832102349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67839421069172702554734899 101759131603759053832102349)
          ·
            refine ⟨38159674351409645187038381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101759131603759053832102349 38159674351409645187038381)
            ·
              refine ⟨14309877881778616945139393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38159674351409645187038381 14309877881778616945139393)
              ·
                refine ⟨10732408411333962708854545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14309877881778616945139393 10732408411333962708854545)
                ·
                  refine ⟨8049306308500472031640909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10732408411333962708854545 8049306308500472031640909)
                  ·
                    refine ⟨3018489865687677011865341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8049306308500472031640909 3018489865687677011865341)
                    ·
                      refine ⟨1131933699632878879449503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018489865687677011865341 1131933699632878879449503)
                      ·
                        rfl

theorem cell23_2204433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_2204433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204433 prefixEnd_2204433 := by exact prefixLift 2204433
  have htrace : WordTrace (prefixWord ++ tailWord_2204433) baseStart_2204433 baseEnd_2204433 := by
    simpa [prefixWord, tailWord_2204433, baseEnd_2204433] using wordTrace_append hprefix tailTrace_2204433
  have hstable : (prefixWord ++ tailWord_2204433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204433).length < 2 ^ (prefixWord ++ tailWord_2204433).sum := by decide
  have hdescent : baseEnd_2204433 < baseStart_2204433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204450 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2204450 : Nat := 118140960795 + 2204450 * 2 ^ 59
def prefixEnd_2204450 : Nat := 4983230072969 + 3 ^ 40 * 2204450 * 2
def baseEnd_2204450 : Nat := 1131942428804005312936925

theorem tailTrace_2204450 : CollatzResearch.WordTrace tailWord_2204450 prefixEnd_2204450 1131942428804005312936925 := by
  unfold tailWord_2204450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20100724215915403732800701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53601931242441076620801869 20100724215915403732800701)
  ·
    refine ⟨7537771580968276399800263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20100724215915403732800701 7537771580968276399800263)
    ·
      refine ⟨11306657371452414599700395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7537771580968276399800263 11306657371452414599700395)
      ·
        refine ⟨16959986057178621899550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11306657371452414599700395 16959986057178621899550593)
        ·
          refine ⟨12719989542883966424662945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16959986057178621899550593 12719989542883966424662945)
          ·
            refine ⟨9539992157162974818497209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12719989542883966424662945 9539992157162974818497209)
            ·
              refine ⟨7154994117872231113872907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9539992157162974818497209 7154994117872231113872907)
              ·
                refine ⟨10732491176808346670809361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7154994117872231113872907 10732491176808346670809361)
                ·
                  refine ⟨8049368382606260003107021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10732491176808346670809361 8049368382606260003107021)
                  ·
                    refine ⟨3018513143477347501165133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8049368382606260003107021 3018513143477347501165133)
                    ·
                      refine ⟨1131942428804005312936925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018513143477347501165133 1131942428804005312936925)
                      ·
                        rfl

theorem cell23_2204450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2204450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204450 prefixEnd_2204450 := by exact prefixLift 2204450
  have htrace : WordTrace (prefixWord ++ tailWord_2204450) baseStart_2204450 baseEnd_2204450 := by
    simpa [prefixWord, tailWord_2204450, baseEnd_2204450] using wordTrace_append hprefix tailTrace_2204450
  have hstable : (prefixWord ++ tailWord_2204450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204450).length < 2 ^ (prefixWord ++ tailWord_2204450).sum := by decide
  have hdescent : baseEnd_2204450 < baseStart_2204450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204474 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_2204474 : Nat := 118140960795 + 2204474 * 2 ^ 59
def prefixEnd_2204474 : Nat := 4983230072969 + 3 ^ 40 * 2204474 * 2
def baseEnd_2204474 : Nat := 125772750259968135448535

theorem tailTrace_2204474 : CollatzResearch.WordTrace tailWord_2204474 prefixEnd_2204474 125772750259968135448535 := by
  unfold tailWord_2204474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20100943053893666757519119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53602514810383111353384317 20100943053893666757519119)
  ·
    refine ⟨30151414580840500136278679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20100943053893666757519119 30151414580840500136278679)
    ·
      refine ⟨45227121871260750204418019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30151414580840500136278679 45227121871260750204418019)
      ·
        refine ⟨67840682806891125306627029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45227121871260750204418019 67840682806891125306627029)
        ·
          refine ⟨1590016003286510749374071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67840682806891125306627029 1590016003286510749374071)
          ·
            refine ⟨2385024004929766124061107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590016003286510749374071 2385024004929766124061107)
            ·
              refine ⟨3577536007394649186091661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385024004929766124061107 3577536007394649186091661)
              ·
                refine ⟨1341576002772993444784373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3577536007394649186091661 1341576002772993444784373)
                ·
                  refine ⟨125772750259968135448535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341576002772993444784373 125772750259968135448535)
                  ·
                    rfl

theorem cell23_2204474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_2204474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204474 prefixEnd_2204474 := by exact prefixLift 2204474
  have htrace : WordTrace (prefixWord ++ tailWord_2204474) baseStart_2204474 baseEnd_2204474 := by
    simpa [prefixWord, tailWord_2204474, baseEnd_2204474] using wordTrace_append hprefix tailTrace_2204474
  have hstable : (prefixWord ++ tailWord_2204474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204474).length < 2 ^ (prefixWord ++ tailWord_2204474).sum := by decide
  have hdescent : baseEnd_2204474 < baseStart_2204474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204490 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_2204490 : Nat := 118140960795 + 2204490 * 2 ^ 59
def prefixEnd_2204490 : Nat := 4983230072969 + 3 ^ 40 * 2204490 * 2
def baseEnd_2204490 : Nat := 1131962968030185156436741

theorem tailTrace_2204490 : CollatzResearch.WordTrace tailWord_2204490 prefixEnd_2204490 1131962968030185156436741 := by
  unfold tailWord_2204490
  simp only [CollatzResearch.WordTrace]
  refine ⟨20101088945879175440664731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53602903855677801175105949 20101088945879175440664731)
  ·
    refine ⟨30151633418818763160997097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20101088945879175440664731 30151633418818763160997097)
    ·
      refine ⟨22613725064114072370747823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30151633418818763160997097 22613725064114072370747823)
      ·
        refine ⟨33920587596171108556121735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22613725064114072370747823 33920587596171108556121735)
        ·
          refine ⟨50880881394256662834182603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33920587596171108556121735 50880881394256662834182603)
          ·
            refine ⟨76321322091384994251273905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50880881394256662834182603 76321322091384994251273905)
            ·
              refine ⟨57240991568538745688455429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76321322091384994251273905 57240991568538745688455429)
              ·
                refine ⟨10732685919101014816585393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57240991568538745688455429 10732685919101014816585393)
                ·
                  refine ⟨8049514439325761112439045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10732685919101014816585393 8049514439325761112439045)
                  ·
                    refine ⟨1509283957373580208582321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8049514439325761112439045 1509283957373580208582321)
                    ·
                      refine ⟨1131962968030185156436741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509283957373580208582321 1131962968030185156436741)
                      ·
                        rfl

theorem cell23_2204490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_2204490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204490 prefixEnd_2204490 := by exact prefixLift 2204490
  have htrace : WordTrace (prefixWord ++ tailWord_2204490) baseStart_2204490 baseEnd_2204490 := by
    simpa [prefixWord, tailWord_2204490, baseEnd_2204490] using wordTrace_append hprefix tailTrace_2204490
  have hstable : (prefixWord ++ tailWord_2204490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204490).length < 2 ^ (prefixWord ++ tailWord_2204490).sum := by decide
  have hdescent : baseEnd_2204490 < baseStart_2204490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204523 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3]
def baseStart_2204523 : Nat := 118140960795 + 2204523 * 2 ^ 59
def prefixEnd_2204523 : Nat := 4983230072969 + 3 ^ 40 * 2204523 * 2
def baseEnd_2204523 : Nat := 1131979912891783527324089

theorem tailTrace_2204523 : CollatzResearch.WordTrace tailWord_2204523 prefixEnd_2204523 1131979912891783527324089 := by
  unfold tailWord_2204523
  simp only [CollatzResearch.WordTrace]
  refine ⟨80405559392397148398610223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53603706261598098932406815 80405559392397148398610223)
  ·
    refine ⟨120608339088595722597915335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80405559392397148398610223 120608339088595722597915335)
    ·
      refine ⟨180912508632893583896873003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120608339088595722597915335 180912508632893583896873003)
      ·
        refine ⟨271368762949340375845309505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180912508632893583896873003 271368762949340375845309505)
        ·
          refine ⟨203526572212005281883982129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271368762949340375845309505 203526572212005281883982129)
          ·
            refine ⟨152644929159003961412986597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203526572212005281883982129 152644929159003961412986597)
            ·
              refine ⟨28620924217313242764934987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152644929159003961412986597 28620924217313242764934987)
              ·
                refine ⟨42931386325969864147402481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28620924217313242764934987 42931386325969864147402481)
                ·
                  refine ⟨32198539744477398110551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42931386325969864147402481 32198539744477398110551861)
                  ·
                    refine ⟨3018613101044756072864237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32198539744477398110551861 3018613101044756072864237)
                    ·
                      refine ⟨1131979912891783527324089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018613101044756072864237 1131979912891783527324089)
                      ·
                        rfl

theorem cell23_2204523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].length) (baseStart_2204523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204523 prefixEnd_2204523 := by exact prefixLift 2204523
  have htrace : WordTrace (prefixWord ++ tailWord_2204523) baseStart_2204523 baseEnd_2204523 := by
    simpa [prefixWord, tailWord_2204523, baseEnd_2204523] using wordTrace_append hprefix tailTrace_2204523
  have hstable : (prefixWord ++ tailWord_2204523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204523).length < 2 ^ (prefixWord ++ tailWord_2204523).sum := by decide
  have hdescent : baseEnd_2204523 < baseStart_2204523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204551 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 1, 4]
def baseStart_2204551 : Nat := 118140960795 + 2204551 * 2 ^ 59
def prefixEnd_2204551 : Nat := 4983230072969 + 3 ^ 40 * 2204551 * 2
def baseEnd_2204551 : Nat := 377331430116703139257987

theorem tailTrace_2204551 : CollatzResearch.WordTrace tailWord_2204551 prefixEnd_2204551 377331430116703139257987 := by
  unfold tailWord_2204551
  simp only [CollatzResearch.WordTrace]
  refine ⟨80406580636295709180629507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53604387090863806120419671 80406580636295709180629507)
  ·
    refine ⟨120609870954443563770944261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80406580636295709180629507 120609870954443563770944261)
    ·
      refine ⟨22614350803958168207052049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120609870954443563770944261 22614350803958168207052049)
      ·
        refine ⟨16960763102968626155289037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22614350803958168207052049 16960763102968626155289037)
        ·
          refine ⟨6360286163613234808233389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16960763102968626155289037 6360286163613234808233389)
          ·
            refine ⟨2385107311354963053087521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6360286163613234808233389 2385107311354963053087521)
            ·
              refine ⟨1788830483516222289815641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385107311354963053087521 1788830483516222289815641)
              ·
                refine ⟨1341622862637166717361731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788830483516222289815641 1341622862637166717361731)
                ·
                  refine ⟨2012434293955750076042597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341622862637166717361731 2012434293955750076042597)
                  ·
                    refine ⟨377331430116703139257987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012434293955750076042597 377331430116703139257987)
                    ·
                      rfl

theorem cell23_2204551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_2204551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204551 prefixEnd_2204551 := by exact prefixLift 2204551
  have htrace : WordTrace (prefixWord ++ tailWord_2204551) baseStart_2204551 baseEnd_2204551 := by
    simpa [prefixWord, tailWord_2204551, baseEnd_2204551] using wordTrace_append hprefix tailTrace_2204551
  have hstable : (prefixWord ++ tailWord_2204551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204551).length < 2 ^ (prefixWord ++ tailWord_2204551).sum := by decide
  have hdescent : baseEnd_2204551 < baseStart_2204551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204580 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2204580 : Nat := 118140960795 + 2204580 * 2 ^ 59
def prefixEnd_2204580 : Nat := 4983230072969 + 3 ^ 40 * 2204580 * 2
def baseEnd_2204580 : Nat := 1132009181289089804311327

theorem tailTrace_2204580 : CollatzResearch.WordTrace tailWord_2204580 prefixEnd_2204580 1132009181289089804311327 := by
  unfold tailWord_2204580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40203819176595323566717597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53605092235460431422290129 40203819176595323566717597)
  ·
    refine ⟨15076432191223246337519099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40203819176595323566717597 15076432191223246337519099)
    ·
      refine ⟨22614648286834869506278649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15076432191223246337519099 22614648286834869506278649)
      ·
        refine ⟨16960986215126152129708987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22614648286834869506278649 16960986215126152129708987)
        ·
          refine ⟨25441479322689228194563481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16960986215126152129708987 25441479322689228194563481)
          ·
            refine ⟨19081109492016921145922611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25441479322689228194563481 19081109492016921145922611)
            ·
              refine ⟨28621664238025381718883917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19081109492016921145922611 28621664238025381718883917)
              ·
                refine ⟨10733124089259518144581469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28621664238025381718883917 10733124089259518144581469)
                ·
                  refine ⟨4024921533472319304218051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10733124089259518144581469 4024921533472319304218051)
                  ·
                    refine ⟨6037382300208478956327077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024921533472319304218051 6037382300208478956327077)
                    ·
                      refine ⟨1132009181289089804311327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6037382300208478956327077 1132009181289089804311327)
                      ·
                        rfl

theorem cell23_2204580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2204580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204580 prefixEnd_2204580 := by exact prefixLift 2204580
  have htrace : WordTrace (prefixWord ++ tailWord_2204580) baseStart_2204580 baseEnd_2204580 := by
    simpa [prefixWord, tailWord_2204580, baseEnd_2204580] using wordTrace_append hprefix tailTrace_2204580
  have hstable : (prefixWord ++ tailWord_2204580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204580).length < 2 ^ (prefixWord ++ tailWord_2204580).sum := by decide
  have hdescent : baseEnd_2204580 < baseStart_2204580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204597 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2204597 : Nat := 118140960795 + 2204597 * 2 ^ 59
def prefixEnd_2204597 : Nat := 4983230072969 + 3 ^ 40 * 2204597 * 2
def baseEnd_2204597 : Nat := 1132017910460216237798749

theorem tailTrace_2204597 : CollatzResearch.WordTrace tailWord_2204597 prefixEnd_2204597 1132017910460216237798749 := by
  unfold tailWord_2204597
  simp only [CollatzResearch.WordTrace]
  refine ⟨80408258394129059036804045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53605505596086039357869363 80408258394129059036804045)
  ·
    refine ⟨30153096897798397138801517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80408258394129059036804045 30153096897798397138801517)
    ·
      refine ⟨11307411336674398927050569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30153096897798397138801517 11307411336674398927050569)
      ·
        refine ⟨8480558502505799195287927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11307411336674398927050569 8480558502505799195287927)
        ·
          refine ⟨12720837753758698792931891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8480558502505799195287927 12720837753758698792931891)
          ·
            refine ⟨19081256630638048189397837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12720837753758698792931891 19081256630638048189397837)
            ·
              refine ⟨7155471236489268071024189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19081256630638048189397837 7155471236489268071024189)
              ·
                refine ⟨2683301713683475526634071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7155471236489268071024189 2683301713683475526634071)
                ·
                  refine ⟨4024952570525213289951107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683301713683475526634071 4024952570525213289951107)
                  ·
                    refine ⟨6037428855787819934926661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024952570525213289951107 6037428855787819934926661)
                    ·
                      refine ⟨1132017910460216237798749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6037428855787819934926661 1132017910460216237798749)
                      ·
                        rfl

theorem cell23_2204597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2204597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204597 prefixEnd_2204597 := by exact prefixLift 2204597
  have htrace : WordTrace (prefixWord ++ tailWord_2204597) baseStart_2204597 baseEnd_2204597 := by
    simpa [prefixWord, tailWord_2204597, baseEnd_2204597] using wordTrace_append hprefix tailTrace_2204597
  have hstable : (prefixWord ++ tailWord_2204597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204597).length < 2 ^ (prefixWord ++ tailWord_2204597).sum := by decide
  have hdescent : baseEnd_2204597 < baseStart_2204597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204598 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_2204598 : Nat := 118140960795 + 2204598 * 2 ^ 59
def prefixEnd_2204598 : Nat := 4983230072969 + 3 ^ 40 * 2204598 * 2
def baseEnd_2204598 : Nat := 125779824882318970431805

theorem tailTrace_2204598 : CollatzResearch.WordTrace tailWord_2204598 prefixEnd_2204598 125779824882318970431805 := by
  unfold tailWord_2204598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025518429195339762974403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53605529911416957471726965 5025518429195339762974403)
  ·
    refine ⟨7538277643793009644461605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025518429195339762974403 7538277643793009644461605)
    ·
      refine ⟨1413427058211189308336551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7538277643793009644461605 1413427058211189308336551)
      ·
        refine ⟨2120140587316783962504827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413427058211189308336551 2120140587316783962504827)
        ·
          refine ⟨3180210880975175943757241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120140587316783962504827 3180210880975175943757241)
          ·
            refine ⟨2385158160731381957817931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180210880975175943757241 2385158160731381957817931)
            ·
              refine ⟨3577737241097072936726897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385158160731381957817931 3577737241097072936726897)
              ·
                refine ⟨2683302930822804702545173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577737241097072936726897 2683302930822804702545173)
                ·
                  refine ⟨125779824882318970431805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2683302930822804702545173 125779824882318970431805)
                  ·
                    rfl

theorem cell23_2204598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_2204598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204598 prefixEnd_2204598 := by exact prefixLift 2204598
  have htrace : WordTrace (prefixWord ++ tailWord_2204598) baseStart_2204598 baseEnd_2204598 := by
    simpa [prefixWord, tailWord_2204598, baseEnd_2204598] using wordTrace_append hprefix tailTrace_2204598
  have hstable : (prefixWord ++ tailWord_2204598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204598).length < 2 ^ (prefixWord ++ tailWord_2204598).sum := by decide
  have hdescent : baseEnd_2204598 < baseStart_2204598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204634 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_2204634 : Nat := 118140960795 + 2204634 * 2 ^ 59
def prefixEnd_2204634 : Nat := 4983230072969 + 3 ^ 40 * 2204634 * 2
def baseEnd_2204634 : Nat := 1132036909244432593036079

theorem tailTrace_2204634 : CollatzResearch.WordTrace tailWord_2204634 prefixEnd_2204634 1132036909244432593036079 := by
  unfold tailWord_2204634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20102401973748753588975239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53606405263330009570600637 20102401973748753588975239)
  ·
    refine ⟨30153602960623130383462859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20102401973748753588975239 30153602960623130383462859)
    ·
      refine ⟨45230404440934695575194289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30153602960623130383462859 45230404440934695575194289)
      ·
        refine ⟨33922803330701021681395717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45230404440934695575194289 33922803330701021681395717)
        ·
          refine ⟨6360525624506441565261697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33922803330701021681395717 6360525624506441565261697)
          ·
            refine ⟨4770394218379831173946273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360525624506441565261697 4770394218379831173946273)
            ·
              refine ⟨3577795663784873380459705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4770394218379831173946273 3577795663784873380459705)
              ·
                refine ⟨2683346747838655035344779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577795663784873380459705 2683346747838655035344779)
                ·
                  refine ⟨4025020121757982553017169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683346747838655035344779 4025020121757982553017169)
                  ·
                    refine ⟨3018765091318486914762877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025020121757982553017169 3018765091318486914762877)
                    ·
                      refine ⟨1132036909244432593036079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018765091318486914762877 1132036909244432593036079)
                      ·
                        rfl

theorem cell23_2204634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_2204634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204634 prefixEnd_2204634 := by exact prefixLift 2204634
  have htrace : WordTrace (prefixWord ++ tailWord_2204634) baseStart_2204634 baseEnd_2204634 := by
    simpa [prefixWord, tailWord_2204634, baseEnd_2204634] using wordTrace_append hprefix tailTrace_2204634
  have hstable : (prefixWord ++ tailWord_2204634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204634).length < 2 ^ (prefixWord ++ tailWord_2204634).sum := by decide
  have hdescent : baseEnd_2204634 < baseStart_2204634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204637 : List Nat := [1, 4, 3, 1, 2, 1, 4, 7]
def baseStart_2204637 : Nat := 118140960795 + 2204637 * 2 ^ 59
def prefixEnd_2204637 : Nat := 4983230072969 + 3 ^ 40 * 2204637 * 2
def baseEnd_2204637 : Nat := 41927349988385040048095

theorem tailTrace_2204637 : CollatzResearch.WordTrace tailWord_2204637 prefixEnd_2204637 41927349988385040048095 := by
  unfold tailWord_2204637
  simp only [CollatzResearch.WordTrace]
  refine ⟨80409717313984145868260165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53606478209322763912173443 80409717313984145868260165)
  ·
    refine ⟨15076821996372027350298781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80409717313984145868260165 15076821996372027350298781)
    ·
      refine ⟨5653808248639510256362043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15076821996372027350298781 5653808248639510256362043)
      ·
        refine ⟨8480712372959265384543065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653808248639510256362043 8480712372959265384543065)
        ·
          refine ⟨6360534279719449038407299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8480712372959265384543065 6360534279719449038407299)
          ·
            refine ⟨9540801419579173557610949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360534279719449038407299 9540801419579173557610949)
            ·
              refine ⟨1788900266171095042052053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9540801419579173557610949 1788900266171095042052053)
              ·
                refine ⟨41927349988385040048095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1788900266171095042052053 41927349988385040048095)
                ·
                  rfl

theorem cell23_2204637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 7].length) (baseStart_2204637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204637 prefixEnd_2204637 := by exact prefixLift 2204637
  have htrace : WordTrace (prefixWord ++ tailWord_2204637) baseStart_2204637 baseEnd_2204637 := by
    simpa [prefixWord, tailWord_2204637, baseEnd_2204637] using wordTrace_append hprefix tailTrace_2204637
  have hstable : (prefixWord ++ tailWord_2204637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204637).length < 2 ^ (prefixWord ++ tailWord_2204637).sum := by decide
  have hdescent : baseEnd_2204637 < baseStart_2204637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204708 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2204708 : Nat := 118140960795 + 2204708 * 2 ^ 59
def prefixEnd_2204708 : Nat := 4983230072969 + 3 ^ 40 * 2204708 * 2
def baseEnd_2204708 : Nat := 1132074906812865303510739

theorem tailTrace_2204708 : CollatzResearch.WordTrace tailWord_2204708 prefixEnd_2204708 1132074906812865303510739 := by
  unfold tailWord_2204708
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206153448363462497047389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53608204597817949996063185 40206153448363462497047389)
  ·
    refine ⟨15077307543136298436392771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40206153448363462497047389 15077307543136298436392771)
    ·
      refine ⟨22615961314704447654589157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15077307543136298436392771 22615961314704447654589157)
      ·
        refine ⟨4240492746507083935235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22615961314704447654589157 4240492746507083935235467)
        ·
          refine ⟨6360739119760625902853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240492746507083935235467 6360739119760625902853201)
          ·
            refine ⟨4770554339820469427139901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360739119760625902853201 4770554339820469427139901)
            ·
              refine ⟨1788957877432676035177463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4770554339820469427139901 1788957877432676035177463)
              ·
                refine ⟨2683436816149014052766195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788957877432676035177463 2683436816149014052766195)
                ·
                  refine ⟨4025155224223521079149293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683436816149014052766195 4025155224223521079149293)
                  ·
                    refine ⟨1509433209083820404680985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4025155224223521079149293 1509433209083820404680985)
                    ·
                      refine ⟨1132074906812865303510739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509433209083820404680985 1132074906812865303510739)
                      ·
                        rfl

theorem cell23_2204708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2204708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204708 prefixEnd_2204708 := by exact prefixLift 2204708
  have htrace : WordTrace (prefixWord ++ tailWord_2204708) baseStart_2204708 baseEnd_2204708 := by
    simpa [prefixWord, tailWord_2204708, baseEnd_2204708] using wordTrace_append hprefix tailTrace_2204708
  have hstable : (prefixWord ++ tailWord_2204708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204708).length < 2 ^ (prefixWord ++ tailWord_2204708).sum := by decide
  have hdescent : baseEnd_2204708 < baseStart_2204708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204721 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_2204721 : Nat := 118140960795 + 2204721 * 2 ^ 59
def prefixEnd_2204721 : Nat := 4983230072969 + 3 ^ 40 * 2204721 * 2
def baseEnd_2204721 : Nat := 1132081582061373752648179

theorem tailTrace_2204721 : CollatzResearch.WordTrace tailWord_2204721 prefixEnd_2204721 1132081582061373752648179 := by
  unfold tailWord_2204721
  simp only [CollatzResearch.WordTrace]
  refine ⟨80412781045679828214318017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53608520697119885476212011 80412781045679828214318017)
  ·
    refine ⟨60309585784259871160738513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80412781045679828214318017 60309585784259871160738513)
    ·
      refine ⟨45232189338194903370553885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60309585784259871160738513 45232189338194903370553885)
      ·
        refine ⟨16962071001823088763957707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45232189338194903370553885 16962071001823088763957707)
        ·
          refine ⟨25443106502734633145936561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16962071001823088763957707 25443106502734633145936561)
          ·
            refine ⟨19082329877050974859452421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25443106502734633145936561 19082329877050974859452421)
            ·
              refine ⟨3577936851947057786147329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19082329877050974859452421 3577936851947057786147329)
              ·
                refine ⟨2683452638960293339610497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577936851947057786147329 2683452638960293339610497)
                ·
                  refine ⟨2012589479220220004707873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683452638960293339610497 2012589479220220004707873)
                  ·
                    refine ⟨1509442109415165003530905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012589479220220004707873 1509442109415165003530905)
                    ·
                      refine ⟨1132081582061373752648179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509442109415165003530905 1132081582061373752648179)
                      ·
                        rfl

theorem cell23_2204721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_2204721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204721 prefixEnd_2204721 := by exact prefixLift 2204721
  have htrace : WordTrace (prefixWord ++ tailWord_2204721) baseStart_2204721 baseEnd_2204721 := by
    simpa [prefixWord, tailWord_2204721, baseEnd_2204721] using wordTrace_append hprefix tailTrace_2204721
  have hstable : (prefixWord ++ tailWord_2204721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204721).length < 2 ^ (prefixWord ++ tailWord_2204721).sum := by decide
  have hdescent : baseEnd_2204721 < baseStart_2204721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204724 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2204724 : Nat := 118140960795 + 2204724 * 2 ^ 59
def prefixEnd_2204724 : Nat := 4983230072969 + 3 ^ 40 * 2204724 * 2
def baseEnd_2204724 : Nat := 1132083122503337240910665

theorem tailTrace_2204724 : CollatzResearch.WordTrace tailWord_2204724 prefixEnd_2204724 1132083122503337240910665 := by
  unfold tailWord_2204724
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206445232334479863338613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53608593643112639817784817 40206445232334479863338613)
  ·
    refine ⟨3769354240531357487187995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40206445232334479863338613 3769354240531357487187995)
    ·
      refine ⟨5654031360797036230781993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3769354240531357487187995 5654031360797036230781993)
      ·
        refine ⟨4240523520597777173086495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5654031360797036230781993 4240523520597777173086495)
        ·
          refine ⟨6360785280896665759629743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240523520597777173086495 6360785280896665759629743)
          ·
            refine ⟨9541177921344998639444615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360785280896665759629743 9541177921344998639444615)
            ·
              refine ⟨14311766882017497959166923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541177921344998639444615 14311766882017497959166923)
              ·
                refine ⟨21467650323026246938750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14311766882017497959166923 21467650323026246938750385)
                ·
                  refine ⟨16100737742269685204062789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21467650323026246938750385 16100737742269685204062789)
                  ·
                    refine ⟨3018888326675565975761773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16100737742269685204062789 3018888326675565975761773)
                    ·
                      refine ⟨1132083122503337240910665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018888326675565975761773 1132083122503337240910665)
                      ·
                        rfl

theorem cell23_2204724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2204724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204724 prefixEnd_2204724 := by exact prefixLift 2204724
  have htrace : WordTrace (prefixWord ++ tailWord_2204724) baseStart_2204724 baseEnd_2204724 := by
    simpa [prefixWord, tailWord_2204724, baseEnd_2204724] using wordTrace_append hprefix tailTrace_2204724
  have hstable : (prefixWord ++ tailWord_2204724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204724).length < 2 ^ (prefixWord ++ tailWord_2204724).sum := by decide
  have hdescent : baseEnd_2204724 < baseStart_2204724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204734 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2204734 : Nat := 118140960795 + 2204734 * 2 ^ 59
def prefixEnd_2204734 : Nat := 4983230072969 + 3 ^ 40 * 2204734 * 2
def baseEnd_2204734 : Nat := 1132088257309882201785619

theorem tailTrace_2204734 : CollatzResearch.WordTrace tailWord_2204734 prefixEnd_2204734 1132088257309882201785619 := by
  unfold tailWord_2204734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051656899329091429317657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53608836796421820956360837 10051656899329091429317657)
  ·
    refine ⟨7538742674496818571988243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10051656899329091429317657 7538742674496818571988243)
    ·
      refine ⟨11308114011745227857982365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538742674496818571988243 11308114011745227857982365)
      ·
        refine ⟨4240542754404460446743387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11308114011745227857982365 4240542754404460446743387)
        ·
          refine ⟨6360814131606690670115081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240542754404460446743387 6360814131606690670115081)
          ·
            refine ⟨4770610598705018002586311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360814131606690670115081 4770610598705018002586311)
            ·
              refine ⟨7155915898057527003879467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770610598705018002586311 7155915898057527003879467)
              ·
                refine ⟨10733873847086290505819201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7155915898057527003879467 10733873847086290505819201)
                ·
                  refine ⟨8050405385314717879364401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10733873847086290505819201 8050405385314717879364401)
                  ·
                    refine ⟨6037804038986038409523301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8050405385314717879364401 6037804038986038409523301)
                    ·
                      refine ⟨1132088257309882201785619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6037804038986038409523301 1132088257309882201785619)
                      ·
                        rfl

theorem cell23_2204734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2204734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204734 prefixEnd_2204734 := by exact prefixLift 2204734
  have htrace : WordTrace (prefixWord ++ tailWord_2204734) baseStart_2204734 baseEnd_2204734 := by
    simpa [prefixWord, tailWord_2204734, baseEnd_2204734] using wordTrace_append hprefix tailTrace_2204734
  have hstable : (prefixWord ++ tailWord_2204734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204734).length < 2 ^ (prefixWord ++ tailWord_2204734).sum := by decide
  have hdescent : baseEnd_2204734 < baseStart_2204734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204797 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2204797 : Nat := 118140960795 + 2204797 * 2 ^ 59
def prefixEnd_2204797 : Nat := 4983230072969 + 3 ^ 40 * 2204797 * 2
def baseEnd_2204797 : Nat := 1132120606591115455297829

theorem tailTrace_2204797 : CollatzResearch.WordTrace tailWord_2204797 prefixEnd_2204797 1132120606591115455297829 := by
  unfold tailWord_2204797
  simp only [CollatzResearch.WordTrace]
  refine ⟨80415552993404493194084645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53610368662269662129389763 80415552993404493194084645)
  ·
    refine ⟨15077916186263342473890871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80415552993404493194084645 15077916186263342473890871)
    ·
      refine ⟨22616874279395013710836307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15077916186263342473890871 22616874279395013710836307)
      ·
        refine ⟨33925311419092520566254461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22616874279395013710836307 33925311419092520566254461)
        ·
          refine ⟨12721991782159695212345423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33925311419092520566254461 12721991782159695212345423)
          ·
            refine ⟨19082987673239542818518135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721991782159695212345423 19082987673239542818518135)
            ·
              refine ⟨28624481509859314227777203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19082987673239542818518135 28624481509859314227777203)
              ·
                refine ⟨42936722264788971341665805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28624481509859314227777203 42936722264788971341665805)
                ·
                  refine ⟨16101270849295864253124677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42936722264788971341665805 16101270849295864253124677)
                  ·
                    refine ⟨3018988284242974547460877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16101270849295864253124677 3018988284242974547460877)
                    ·
                      refine ⟨1132120606591115455297829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3018988284242974547460877 1132120606591115455297829)
                      ·
                        rfl

theorem cell23_2204797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2204797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204797 prefixEnd_2204797 := by exact prefixLift 2204797
  have htrace : WordTrace (prefixWord ++ tailWord_2204797) baseStart_2204797 baseEnd_2204797 := by
    simpa [prefixWord, tailWord_2204797, baseEnd_2204797] using wordTrace_append hprefix tailTrace_2204797
  have hstable : (prefixWord ++ tailWord_2204797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204797).length < 2 ^ (prefixWord ++ tailWord_2204797).sum := by decide
  have hdescent : baseEnd_2204797 < baseStart_2204797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204804 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_2204804 : Nat := 118140960795 + 2204804 * 2 ^ 59
def prefixEnd_2204804 : Nat := 4983230072969 + 3 ^ 40 * 2204804 * 2
def baseEnd_2204804 : Nat := 377374733651898975970099

theorem tailTrace_2204804 : CollatzResearch.WordTrace tailWord_2204804 prefixEnd_2204804 377374733651898975970099 := by
  unfold tailWord_2204804
  simp only [CollatzResearch.WordTrace]
  refine ⟨40207904152189566694794733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53610538869586088926392977 40207904152189566694794733)
  ·
    refine ⟨15077964057071087510548025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40207904152189566694794733 15077964057071087510548025)
    ·
      refine ⟨11308473042803315632911019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15077964057071087510548025 11308473042803315632911019)
      ·
        refine ⟨16962709564204973449366529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308473042803315632911019 16962709564204973449366529)
        ·
          refine ⟨12722032173153730087024897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16962709564204973449366529 12722032173153730087024897)
          ·
            refine ⟨9541524129865297565268673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722032173153730087024897 9541524129865297565268673)
            ·
              refine ⟨7156143097398973173951505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9541524129865297565268673 7156143097398973173951505)
              ·
                refine ⟨5367107323049229880463629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156143097398973173951505 5367107323049229880463629)
                ·
                  refine ⟨2012665246143461205173861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367107323049229880463629 2012665246143461205173861)
                  ·
                    refine ⟨377374733651898975970099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012665246143461205173861 377374733651898975970099)
                    ·
                      rfl

theorem cell23_2204804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_2204804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204804 prefixEnd_2204804 := by exact prefixLift 2204804
  have htrace : WordTrace (prefixWord ++ tailWord_2204804) baseStart_2204804 baseEnd_2204804 := by
    simpa [prefixWord, tailWord_2204804, baseEnd_2204804] using wordTrace_append hprefix tailTrace_2204804
  have hstable : (prefixWord ++ tailWord_2204804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204804).length < 2 ^ (prefixWord ++ tailWord_2204804).sum := by decide
  have hdescent : baseEnd_2204804 < baseStart_2204804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204814 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2204814 : Nat := 118140960795 + 2204814 * 2 ^ 59
def prefixEnd_2204814 : Nat := 4983230072969 + 3 ^ 40 * 2204814 * 2
def baseEnd_2204814 : Nat := 1132129335762241888785251

theorem tailTrace_2204814 : CollatzResearch.WordTrace tailWord_2204814 prefixEnd_2204814 1132129335762241888785251 := by
  unfold tailWord_2204814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052021629292863137181687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53610782022895270064968997 10052021629292863137181687)
  ·
    refine ⟨15078032443939294705772531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10052021629292863137181687 15078032443939294705772531)
    ·
      refine ⟨22617048665908942058658797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15078032443939294705772531 22617048665908942058658797)
      ·
        refine ⟨8481393249715853271997049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22617048665908942058658797 8481393249715853271997049)
        ·
          refine ⟨6361044937286889953997787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8481393249715853271997049 6361044937286889953997787)
          ·
            refine ⟨9541567405930334930996681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361044937286889953997787 9541567405930334930996681)
            ·
              refine ⟨7156175554447751198247511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9541567405930334930996681 7156175554447751198247511)
              ·
                refine ⟨10734263331671626797371267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156175554447751198247511 10734263331671626797371267)
                ·
                  refine ⟨16101394997507440196056901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10734263331671626797371267 16101394997507440196056901)
                  ·
                    refine ⟨3019011562032645036760669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16101394997507440196056901 3019011562032645036760669)
                    ·
                      refine ⟨1132129335762241888785251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019011562032645036760669 1132129335762241888785251)
                      ·
                        rfl

theorem cell23_2204814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2204814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204814 prefixEnd_2204814 := by exact prefixLift 2204814
  have htrace : WordTrace (prefixWord ++ tailWord_2204814) baseStart_2204814 baseEnd_2204814 := by
    simpa [prefixWord, tailWord_2204814, baseEnd_2204814] using wordTrace_append hprefix tailTrace_2204814
  have hstable : (prefixWord ++ tailWord_2204814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204814).length < 2 ^ (prefixWord ++ tailWord_2204814).sum := by decide
  have hdescent : baseEnd_2204814 < baseStart_2204814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204831 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2204831 : Nat := 118140960795 + 2204831 * 2 ^ 59
def prefixEnd_2204831 : Nat := 4983230072969 + 3 ^ 40 * 2204831 * 2
def baseEnd_2204831 : Nat := 1132138064933368322272673

theorem tailTrace_2204831 : CollatzResearch.WordTrace tailWord_2204831 prefixEnd_2204831 1132138064933368322272673 := by
  unfold tailWord_2204831
  simp only [CollatzResearch.WordTrace]
  refine ⟨80416793075281317000822347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53611195383520878000548231 80416793075281317000822347)
  ·
    refine ⟨120625189612921975501233521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80416793075281317000822347 120625189612921975501233521)
    ·
      refine ⟨90468892209691481625925141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120625189612921975501233521 90468892209691481625925141)
      ·
        refine ⟨4240729322329288201215241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90468892209691481625925141 4240729322329288201215241)
        ·
          refine ⟨3180546991746966150911431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4240729322329288201215241 3180546991746966150911431)
          ·
            refine ⟨4770820487620449226367147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180546991746966150911431 4770820487620449226367147)
            ·
              refine ⟨7156230731430673839550721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770820487620449226367147 7156230731430673839550721)
              ·
                refine ⟨5367173048573005379663041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156230731430673839550721 5367173048573005379663041)
                ·
                  refine ⟨4025379786429754034747281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367173048573005379663041 4025379786429754034747281)
                  ·
                    refine ⟨3019034839822315526060461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025379786429754034747281 3019034839822315526060461)
                    ·
                      refine ⟨1132138064933368322272673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019034839822315526060461 1132138064933368322272673)
                      ·
                        rfl

theorem cell23_2204831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2204831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204831 prefixEnd_2204831 := by exact prefixLift 2204831
  have htrace : WordTrace (prefixWord ++ tailWord_2204831) baseStart_2204831 baseEnd_2204831 := by
    simpa [prefixWord, tailWord_2204831, baseEnd_2204831] using wordTrace_append hprefix tailTrace_2204831
  have hstable : (prefixWord ++ tailWord_2204831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204831).length < 2 ^ (prefixWord ++ tailWord_2204831).sum := by decide
  have hdescent : baseEnd_2204831 < baseStart_2204831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204844 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_2204844 : Nat := 118140960795 + 2204844 * 2 ^ 59
def prefixEnd_2204844 : Nat := 4983230072969 + 3 ^ 40 * 2204844 * 2
def baseEnd_2204844 : Nat := 1132144740181876771410113

theorem tailTrace_2204844 : CollatzResearch.WordTrace tailWord_2204844 prefixEnd_2204844 1132144740181876771410113 := by
  unfold tailWord_2204844
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208633612117110110522793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53611511482822813480697057 40208633612117110110522793)
  ·
    refine ⟨30156475209087832582892095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40208633612117110110522793 30156475209087832582892095)
    ·
      refine ⟨45234712813631748874338143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30156475209087832582892095 45234712813631748874338143)
      ·
        refine ⟨67852069220447623311507215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45234712813631748874338143 67852069220447623311507215)
        ·
          refine ⟨101778103830671434967260823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67852069220447623311507215 101778103830671434967260823)
          ·
            refine ⟨152667155746007152450891235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101778103830671434967260823 152667155746007152450891235)
            ·
              refine ⟨229000733619010728676336853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152667155746007152450891235 229000733619010728676336853)
              ·
                refine ⟨5367204694195563953351645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 229000733619010728676336853 5367204694195563953351645)
                ·
                  refine ⟨2012701760323336482506867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367204694195563953351645 2012701760323336482506867)
                  ·
                    refine ⟨3019052640485004723760301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012701760323336482506867 3019052640485004723760301)
                    ·
                      refine ⟨1132144740181876771410113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019052640485004723760301 1132144740181876771410113)
                      ·
                        rfl

theorem cell23_2204844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_2204844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204844 prefixEnd_2204844 := by exact prefixLift 2204844
  have htrace : WordTrace (prefixWord ++ tailWord_2204844) baseStart_2204844 baseEnd_2204844 := by
    simpa [prefixWord, tailWord_2204844, baseEnd_2204844] using wordTrace_append hprefix tailTrace_2204844
  have hstable : (prefixWord ++ tailWord_2204844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204844).length < 2 ^ (prefixWord ++ tailWord_2204844).sum := by decide
  have hdescent : baseEnd_2204844 < baseStart_2204844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204864 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_2204864 : Nat := 118140960795 + 2204864 * 2 ^ 59
def prefixEnd_2204864 : Nat := 4983230072969 + 3 ^ 40 * 2204864 * 2
def baseEnd_2204864 : Nat := 377385003264988897720007

theorem tailTrace_2204864 : CollatzResearch.WordTrace tailWord_2204864 prefixEnd_2204864 377385003264988897720007 := by
  unfold tailWord_2204864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208998342080881818386823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53611997789441175757849097 40208998342080881818386823)
  ·
    refine ⟨60313497513121322727580235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40208998342080881818386823 60313497513121322727580235)
    ·
      refine ⟨90470246269681984091370353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60313497513121322727580235 90470246269681984091370353)
      ·
        refine ⟨67852684702261488068527765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90470246269681984091370353 67852684702261488068527765)
        ·
          refine ⟨3180594595418507253212239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67852684702261488068527765 3180594595418507253212239)
          ·
            refine ⟨4770891893127760879818359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180594595418507253212239 4770891893127760879818359)
            ·
              refine ⟨7156337839691641319727539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770891893127760879818359 7156337839691641319727539)
              ·
                refine ⟨10734506759537461979591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156337839691641319727539 10734506759537461979591309)
                ·
                  refine ⟨4025440034826548242346741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10734506759537461979591309 4025440034826548242346741)
                  ·
                    refine ⟨377385003264988897720007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4025440034826548242346741 377385003264988897720007)
                    ·
                      rfl

theorem cell23_2204864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_2204864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204864 prefixEnd_2204864 := by exact prefixLift 2204864
  have htrace : WordTrace (prefixWord ++ tailWord_2204864) baseStart_2204864 baseEnd_2204864 := by
    simpa [prefixWord, tailWord_2204864, baseEnd_2204864] using wordTrace_append hprefix tailTrace_2204864
  have hstable : (prefixWord ++ tailWord_2204864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204864).length < 2 ^ (prefixWord ++ tailWord_2204864).sum := by decide
  have hdescent : baseEnd_2204864 < baseStart_2204864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204904 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2204904 : Nat := 118140960795 + 2204904 * 2 ^ 59
def prefixEnd_2204904 : Nat := 4983230072969 + 3 ^ 40 * 2204904 * 2
def baseEnd_2204904 : Nat := 1132175549021146536659837

theorem tailTrace_2204904 : CollatzResearch.WordTrace tailWord_2204904 prefixEnd_2204904 1132175549021146536659837 := by
  unfold tailWord_2204904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40209727802008425234114883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53612970402677900312153177 40209727802008425234114883)
  ·
    refine ⟨60314591703012637851172325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40209727802008425234114883 60314591703012637851172325)
    ·
      refine ⟨11308985944314869597094811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60314591703012637851172325 11308985944314869597094811)
      ·
        refine ⟨16963478916472304395642217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308985944314869597094811 16963478916472304395642217)
        ·
          refine ⟨12722609187354228296731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963478916472304395642217 12722609187354228296731663)
          ·
            refine ⟨19083913781031342445097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722609187354228296731663 19083913781031342445097495)
            ·
              refine ⟨28625870671547013667646243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19083913781031342445097495 28625870671547013667646243)
              ·
                refine ⟨42938806007320520501469365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28625870671547013667646243 42938806007320520501469365)
                ·
                  refine ⟨4025513063186298797012753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42938806007320520501469365 4025513063186298797012753)
                  ·
                    refine ⟨3019134797389724097759565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4025513063186298797012753 3019134797389724097759565)
                    ·
                      refine ⟨1132175549021146536659837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019134797389724097759565 1132175549021146536659837)
                      ·
                        rfl

theorem cell23_2204904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2204904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204904 prefixEnd_2204904 := by exact prefixLift 2204904
  have htrace : WordTrace (prefixWord ++ tailWord_2204904) baseStart_2204904 baseEnd_2204904 := by
    simpa [prefixWord, tailWord_2204904, baseEnd_2204904] using wordTrace_append hprefix tailTrace_2204904
  have hstable : (prefixWord ++ tailWord_2204904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204904).length < 2 ^ (prefixWord ++ tailWord_2204904).sum := by decide
  have hdescent : baseEnd_2204904 < baseStart_2204904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204907 : List Nat := [1, 1, 1, 1, 2, 6, 3, 8]
def baseStart_2204907 : Nat := 118140960795 + 2204907 * 2 ^ 59
def prefixEnd_2204907 : Nat := 4983230072969 + 3 ^ 40 * 2204907 * 2
def baseEnd_2204907 : Nat := 41932484794930000923049

theorem tailTrace_2204907 : CollatzResearch.WordTrace tailWord_2204907 prefixEnd_2204907 41932484794930000923049 := by
  unfold tailWord_2204907
  simp only [CollatzResearch.WordTrace]
  refine ⟨80419565023005981980588975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53613043348670654653725983 80419565023005981980588975)
  ·
    refine ⟨120629347534508972970883463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80419565023005981980588975 120629347534508972970883463)
    ·
      refine ⟨180944021301763459456325195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120629347534508972970883463 180944021301763459456325195)
      ·
        refine ⟨271416031952645189184487793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180944021301763459456325195 271416031952645189184487793)
        ·
          refine ⟨203562023964483891888365845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271416031952645189184487793 203562023964483891888365845)
          ·
            refine ⟨9541969873335182432267149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203562023964483891888365845 9541969873335182432267149)
            ·
              refine ⟨3578238702500693412100181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9541969873335182432267149 3578238702500693412100181)
              ·
                refine ⟨41932484794930000923049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3578238702500693412100181 41932484794930000923049)
                ·
                  rfl

theorem cell23_2204907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 8].length) (baseStart_2204907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204907 prefixEnd_2204907 := by exact prefixLift 2204907
  have htrace : WordTrace (prefixWord ++ tailWord_2204907) baseStart_2204907 baseEnd_2204907 := by
    simpa [prefixWord, tailWord_2204907, baseEnd_2204907] using wordTrace_append hprefix tailTrace_2204907
  have hstable : (prefixWord ++ tailWord_2204907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204907).length < 2 ^ (prefixWord ++ tailWord_2204907).sum := by decide
  have hdescent : baseEnd_2204907 < baseStart_2204907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204951 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2204951 : Nat := 118140960795 + 2204951 * 2 ^ 59
def prefixEnd_2204951 : Nat := 4983230072969 + 3 ^ 40 * 2204951 * 2
def baseEnd_2204951 : Nat := 1132199682611907852772121

theorem tailTrace_2204951 : CollatzResearch.WordTrace tailWord_2204951 prefixEnd_2204951 1132199682611907852772121 := by
  unfold tailWord_2204951
  simp only [CollatzResearch.WordTrace]
  refine ⟨80421169834846577495190707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53614113223231051663460471 80421169834846577495190707)
  ·
    refine ⟨120631754752269866242786061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80421169834846577495190707 120631754752269866242786061)
    ·
      refine ⟨45236908032101199841044773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120631754752269866242786061 45236908032101199841044773)
      ·
        refine ⟨8481920256018974970195895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45236908032101199841044773 8481920256018974970195895)
        ·
          refine ⟨12722880384028462455293843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481920256018974970195895 12722880384028462455293843)
          ·
            refine ⟨19084320576042693682940765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12722880384028462455293843 19084320576042693682940765)
            ·
              refine ⟨7156620216016010131102787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19084320576042693682940765 7156620216016010131102787)
              ·
                refine ⟨10734930324024015196654181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7156620216016010131102787 10734930324024015196654181)
                ·
                  refine ⟨2012799435754502849372659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10734930324024015196654181 2012799435754502849372659)
                  ·
                    refine ⟨3019199153631754274058989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012799435754502849372659 3019199153631754274058989)
                    ·
                      refine ⟨1132199682611907852772121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019199153631754274058989 1132199682611907852772121)
                      ·
                        rfl

theorem cell23_2204951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2204951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204951 prefixEnd_2204951 := by exact prefixLift 2204951
  have htrace : WordTrace (prefixWord ++ tailWord_2204951) baseStart_2204951 baseEnd_2204951 := by
    simpa [prefixWord, tailWord_2204951, baseEnd_2204951] using wordTrace_append hprefix tailTrace_2204951
  have hstable : (prefixWord ++ tailWord_2204951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204951).length < 2 ^ (prefixWord ++ tailWord_2204951).sum := by decide
  have hdescent : baseEnd_2204951 < baseStart_2204951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204968 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2204968 : Nat := 118140960795 + 2204968 * 2 ^ 59
def prefixEnd_2204968 : Nat := 4983230072969 + 3 ^ 40 * 2204968 * 2
def baseEnd_2204968 : Nat := 1132208411783034286259543

theorem tailTrace_2204968 : CollatzResearch.WordTrace tailWord_2204968 prefixEnd_2204968 1132208411783034286259543 := by
  unfold tailWord_2204968
  simp only [CollatzResearch.WordTrace]
  refine ⟨40210894937892494699279779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53614526583856659599039705 40210894937892494699279779)
  ·
    refine ⟨60316342406838742048919669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40210894937892494699279779 60316342406838742048919669)
    ·
      refine ⟨5654657100641132067086219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60316342406838742048919669 5654657100641132067086219)
      ·
        refine ⟨8481985650961698100629329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5654657100641132067086219 8481985650961698100629329)
        ·
          refine ⟨6361489238221273575471997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8481985650961698100629329 6361489238221273575471997)
          ·
            refine ⟨2385558464332977590801999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6361489238221273575471997 2385558464332977590801999)
            ·
              refine ⟨3578337696499466386202999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385558464332977590801999 3578337696499466386202999)
              ·
                refine ⟨5367506544749199579304499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3578337696499466386202999 5367506544749199579304499)
                ·
                  refine ⟨8051259817123799368956749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5367506544749199579304499 8051259817123799368956749)
                  ·
                    refine ⟨3019222431421424763358781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8051259817123799368956749 3019222431421424763358781)
                    ·
                      refine ⟨1132208411783034286259543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3019222431421424763358781 1132208411783034286259543)
                      ·
                        rfl

theorem cell23_2204968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2204968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204968 prefixEnd_2204968 := by exact prefixLift 2204968
  have htrace : WordTrace (prefixWord ++ tailWord_2204968) baseStart_2204968 baseEnd_2204968 := by
    simpa [prefixWord, tailWord_2204968, baseEnd_2204968] using wordTrace_append hprefix tailTrace_2204968
  have hstable : (prefixWord ++ tailWord_2204968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204968).length < 2 ^ (prefixWord ++ tailWord_2204968).sum := by decide
  have hdescent : baseEnd_2204968 < baseStart_2204968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204978 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_2204978 : Nat := 118140960795 + 2204978 * 2 ^ 59
def prefixEnd_2204978 : Nat := 4983230072969 + 3 ^ 40 * 2204978 * 2
def baseEnd_2204978 : Nat := 1132213546589579247134497

theorem tailTrace_2204978 : CollatzResearch.WordTrace tailWord_2204978 prefixEnd_2204978 1132213546589579247134497 := by
  unfold tailWord_2204978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20105538651437190276605897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53614769737165840737615725 20105538651437190276605897)
  ·
    refine ⟨15079153988577892707454423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20105538651437190276605897 15079153988577892707454423)
    ·
      refine ⟨22618730982866839061181635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15079153988577892707454423 22618730982866839061181635)
      ·
        refine ⟨33928096474300258591772453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22618730982866839061181635 33928096474300258591772453)
        ·
          refine ⟨6361518088931298485957335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33928096474300258591772453 6361518088931298485957335)
          ·
            refine ⟨9542277133396947728936003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361518088931298485957335 9542277133396947728936003)
            ·
              refine ⟨14313415700095421593404005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542277133396947728936003 14313415700095421593404005)
              ·
                refine ⟨2683765443767891548763251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14313415700095421593404005 2683765443767891548763251)
                ·
                  refine ⟨4025648165651837323144877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683765443767891548763251 4025648165651837323144877)
                  ·
                    refine ⟨1509618062119438996179329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4025648165651837323144877 1509618062119438996179329)
                    ·
                      refine ⟨1132213546589579247134497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509618062119438996179329 1132213546589579247134497)
                      ·
                        rfl

theorem cell23_2204978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_2204978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204978 prefixEnd_2204978 := by exact prefixLift 2204978
  have htrace : WordTrace (prefixWord ++ tailWord_2204978) baseStart_2204978 baseEnd_2204978 := by
    simpa [prefixWord, tailWord_2204978, baseEnd_2204978] using wordTrace_append hprefix tailTrace_2204978
  have hstable : (prefixWord ++ tailWord_2204978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204978).length < 2 ^ (prefixWord ++ tailWord_2204978).sum := by decide
  have hdescent : baseEnd_2204978 < baseStart_2204978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2204997 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 9]
def baseStart_2204997 : Nat := 118140960795 + 2204997 * 2 ^ 59
def prefixEnd_2204997 : Nat := 4983230072969 + 3 ^ 40 * 2204997 * 2
def baseEnd_2204997 : Nat := 125802589191334963644101

theorem tailTrace_2204997 : CollatzResearch.WordTrace tailWord_2204997 prefixEnd_2204997 125802589191334963644101 := by
  unfold tailWord_2204997
  simp only [CollatzResearch.WordTrace]
  refine ⟨80422847592679927351365245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53615231728453284900910163 80422847592679927351365245)
  ·
    refine ⟨30158567847254972756761967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80422847592679927351365245 30158567847254972756761967)
    ·
      refine ⟨45237851770882459135142951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30158567847254972756761967 45237851770882459135142951)
      ·
        refine ⟨67856777656323688702714427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45237851770882459135142951 67856777656323688702714427)
        ·
          refine ⟨101785166484485533054071641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67856777656323688702714427 101785166484485533054071641)
          ·
            refine ⟨76338874863364149790553731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101785166484485533054071641 76338874863364149790553731)
            ·
              refine ⟨114508312295046224685830597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76338874863364149790553731 114508312295046224685830597)
              ·
                refine ⟨21470308555321167128593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114508312295046224685830597 21470308555321167128593237)
                ·
                  refine ⟨125802589191334963644101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21470308555321167128593237 125802589191334963644101)
                  ·
                    rfl

theorem cell23_2204997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_2204997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2204997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2204997 prefixEnd_2204997 := by exact prefixLift 2204997
  have htrace : WordTrace (prefixWord ++ tailWord_2204997) baseStart_2204997 baseEnd_2204997 := by
    simpa [prefixWord, tailWord_2204997, baseEnd_2204997] using wordTrace_append hprefix tailTrace_2204997
  have hstable : (prefixWord ++ tailWord_2204997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2204997).length < 2 ^ (prefixWord ++ tailWord_2204997).sum := by decide
  have hdescent : baseEnd_2204997 < baseStart_2204997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2204997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205008 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2]
def baseStart_2205008 : Nat := 118140960795 + 2205008 * 2 ^ 59
def prefixEnd_2205008 : Nat := 4983230072969 + 3 ^ 40 * 2205008 * 2
def baseEnd_2205008 : Nat := 1132228951009214129759359

theorem tailTrace_2205008 : CollatzResearch.WordTrace tailWord_2205008 prefixEnd_2205008 1132228951009214129759359 := by
  unfold tailWord_2205008
  simp only [CollatzResearch.WordTrace]
  refine ⟨40211624397820038115007839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53615499197093384153343785 40211624397820038115007839)
  ·
    refine ⟨60317436596730057172511759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40211624397820038115007839 60317436596730057172511759)
    ·
      refine ⟨90476154895095085758767639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60317436596730057172511759 90476154895095085758767639)
      ·
        refine ⟨135714232342642628638151459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90476154895095085758767639 135714232342642628638151459)
        ·
          refine ⟨203571348513963942957227189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135714232342642628638151459 203571348513963942957227189)
          ·
            refine ⟨19084813923184119652240049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203571348513963942957227189 19084813923184119652240049)
            ·
              refine ⟨14313610442388089739180037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19084813923184119652240049 14313610442388089739180037)
              ·
                refine ⟨2683801957947766826096257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14313610442388089739180037 2683801957947766826096257)
                ·
                  refine ⟨2012851468460825119572193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683801957947766826096257 2012851468460825119572193)
                  ·
                    refine ⟨1509638601345618839679145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012851468460825119572193 1509638601345618839679145)
                    ·
                      refine ⟨1132228951009214129759359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509638601345618839679145 1132228951009214129759359)
                      ·
                        rfl

theorem cell23_2205008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2].length) (baseStart_2205008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205008 prefixEnd_2205008 := by exact prefixLift 2205008
  have htrace : WordTrace (prefixWord ++ tailWord_2205008) baseStart_2205008 baseEnd_2205008 := by
    simpa [prefixWord, tailWord_2205008, baseEnd_2205008] using wordTrace_append hprefix tailTrace_2205008
  have hstable : (prefixWord ++ tailWord_2205008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205008).length < 2 ^ (prefixWord ++ tailWord_2205008).sum := by decide
  have hdescent : baseEnd_2205008 < baseStart_2205008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205065 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 5]
def baseStart_2205065 : Nat := 118140960795 + 2205065 * 2 ^ 59
def prefixEnd_2205065 : Nat := 4983230072969 + 3 ^ 40 * 2205065 * 2
def baseEnd_2205065 : Nat := 125806468822946711860733

theorem tailTrace_2205065 : CollatzResearch.WordTrace tailWord_2205065 prefixEnd_2205065 125806468822946711860733 := by
  unfold tailWord_2205065
  simp only [CollatzResearch.WordTrace]
  refine ⟨80425327756433574964840649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53616885170955716643227099 80425327756433574964840649)
  ·
    refine ⟨60318995817325181223630487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80425327756433574964840649 60318995817325181223630487)
    ·
      refine ⟨90478493725987771835445731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60318995817325181223630487 90478493725987771835445731)
      ·
        refine ⟨135717740588981657753168597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90478493725987771835445731 135717740588981657753168597)
        ·
          refine ⟨3180884545054257603589889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 135717740588981657753168597 3180884545054257603589889)
          ·
            refine ⟨2385663408790693202692417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180884545054257603589889 2385663408790693202692417)
            ·
              refine ⟨1789247556593019902019313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385663408790693202692417 1789247556593019902019313)
              ·
                refine ⟨1341935667444764926514485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789247556593019902019313 1341935667444764926514485)
                ·
                  refine ⟨125806468822946711860733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341935667444764926514485 125806468822946711860733)
                  ·
                    rfl

theorem cell23_2205065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 5].length) (baseStart_2205065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205065 prefixEnd_2205065 := by exact prefixLift 2205065
  have htrace : WordTrace (prefixWord ++ tailWord_2205065) baseStart_2205065 baseEnd_2205065 := by
    simpa [prefixWord, tailWord_2205065, baseEnd_2205065] using wordTrace_append hprefix tailTrace_2205065
  have hstable : (prefixWord ++ tailWord_2205065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205065).length < 2 ^ (prefixWord ++ tailWord_2205065).sum := by decide
  have hdescent : baseEnd_2205065 < baseStart_2205065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205081 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 6, 2]
def baseStart_2205081 : Nat := 118140960795 + 2205081 * 2 ^ 59
def prefixEnd_2205081 : Nat := 4983230072969 + 3 ^ 40 * 2205081 * 2
def baseEnd_2205081 : Nat := 1132266435096992344146523

theorem tailTrace_2205081 : CollatzResearch.WordTrace tailWord_2205081 prefixEnd_2205081 1132266435096992344146523 := by
  unfold tailWord_2205081
  simp only [CollatzResearch.WordTrace]
  refine ⟨80425911324375609697423097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53617274216250406464948731 80425911324375609697423097)
  ·
    refine ⟨60319433493281707273067323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80425911324375609697423097 60319433493281707273067323)
    ·
      refine ⟨90479150239922560909600985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60319433493281707273067323 90479150239922560909600985)
      ·
        refine ⟨67859362679941920682200739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90479150239922560909600985 67859362679941920682200739)
        ·
          refine ⟨101789044019912881023301109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67859362679941920682200739 101789044019912881023301109)
          ·
            refine ⟨9542722876866832595934479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101789044019912881023301109 9542722876866832595934479)
            ·
              refine ⟨14314084315300248893901719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542722876866832595934479 14314084315300248893901719)
              ·
                refine ⟨21471126472950373340852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14314084315300248893901719 21471126472950373340852579)
                ·
                  refine ⟨32206689709425560011278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21471126472950373340852579 32206689709425560011278869)
                  ·
                    refine ⟨1509688580129323125528697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32206689709425560011278869 1509688580129323125528697)
                    ·
                      refine ⟨1132266435096992344146523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509688580129323125528697 1132266435096992344146523)
                      ·
                        rfl

theorem cell23_2205081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_2205081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205081 prefixEnd_2205081 := by exact prefixLift 2205081
  have htrace : WordTrace (prefixWord ++ tailWord_2205081) baseStart_2205081 baseEnd_2205081 := by
    simpa [prefixWord, tailWord_2205081, baseEnd_2205081] using wordTrace_append hprefix tailTrace_2205081
  have hstable : (prefixWord ++ tailWord_2205081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205081).length < 2 ^ (prefixWord ++ tailWord_2205081).sum := by decide
  have hdescent : baseEnd_2205081 < baseStart_2205081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205091 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 3, 4]
def baseStart_2205091 : Nat := 118140960795 + 2205091 * 2 ^ 59
def prefixEnd_2205091 : Nat := 4983230072969 + 3 ^ 40 * 2205091 * 2
def baseEnd_2205091 : Nat := 377423856634512435007159

theorem tailTrace_2205091 : CollatzResearch.WordTrace tailWord_2205091 prefixEnd_2205091 377423856634512435007159 := by
  unfold tailWord_2205091
  simp only [CollatzResearch.WordTrace]
  refine ⟨80426276054339381405287127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53617517369559587603524751 80426276054339381405287127)
  ·
    refine ⟨120639414081509072107930691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80426276054339381405287127 120639414081509072107930691)
    ·
      refine ⟨180959121122263608161896037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120639414081509072107930691 180959121122263608161896037)
      ·
        refine ⟨33929835210424426530355507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180959121122263608161896037 33929835210424426530355507)
        ·
          refine ⟨50894752815636639795533261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33929835210424426530355507 50894752815636639795533261)
          ·
            refine ⟨19085532305863739923324973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50894752815636639795533261 19085532305863739923324973)
            ·
              refine ⟨7157074614698902471246865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19085532305863739923324973 7157074614698902471246865)
              ·
                refine ⟨5367805961024176853435149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7157074614698902471246865 5367805961024176853435149)
                ·
                  refine ⟨2012927235384066320038181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367805961024176853435149 2012927235384066320038181)
                  ·
                    refine ⟨377423856634512435007159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2012927235384066320038181 377423856634512435007159)
                    ·
                      rfl

theorem cell23_2205091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 4].length) (baseStart_2205091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205091 prefixEnd_2205091 := by exact prefixLift 2205091
  have htrace : WordTrace (prefixWord ++ tailWord_2205091) baseStart_2205091 baseEnd_2205091 := by
    simpa [prefixWord, tailWord_2205091, baseEnd_2205091] using wordTrace_append hprefix tailTrace_2205091
  have hstable : (prefixWord ++ tailWord_2205091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205091).length < 2 ^ (prefixWord ++ tailWord_2205091).sum := by decide
  have hdescent : baseEnd_2205091 < baseStart_2205091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205144 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2205144 : Nat := 118140960795 + 2205144 * 2 ^ 59
def prefixEnd_2205144 : Nat := 4983230072969 + 3 ^ 40 * 2205144 * 2
def baseEnd_2205144 : Nat := 1132298784378225597658733

theorem tailTrace_2205144 : CollatzResearch.WordTrace tailWord_2205144 prefixEnd_2205144 1132298784378225597658733 := by
  unfold tailWord_2205144
  simp only [CollatzResearch.WordTrace]
  refine ⟨40214104561573685728483243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53618806082098247637977657 40214104561573685728483243)
  ·
    refine ⟨60321156842360528592724865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40214104561573685728483243 60321156842360528592724865)
    ·
      refine ⟨45240867631770396444543649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60321156842360528592724865 45240867631770396444543649)
      ·
        refine ⟨33930650723827797333407737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45240867631770396444543649 33930650723827797333407737)
        ·
          refine ⟨25447988042870848000055803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33930650723827797333407737 25447988042870848000055803)
          ·
            refine ⟨38171982064306272000083705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25447988042870848000055803 38171982064306272000083705)
            ·
              refine ⟨28628986548229704000062779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38171982064306272000083705 28628986548229704000062779)
              ·
                refine ⟨42943479822344556000094169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28628986548229704000062779 42943479822344556000094169)
                ·
                  refine ⟨32207609866758417000070627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42943479822344556000094169 32207609866758417000070627)
                  ·
                    refine ⟨48311414800137625500105941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32207609866758417000070627 48311414800137625500105941)
                    ·
                      refine ⟨1132298784378225597658733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48311414800137625500105941 1132298784378225597658733)
                      ·
                        rfl

theorem cell23_2205144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2205144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205144 prefixEnd_2205144 := by exact prefixLift 2205144
  have htrace : WordTrace (prefixWord ++ tailWord_2205144) baseStart_2205144 baseEnd_2205144 := by
    simpa [prefixWord, tailWord_2205144, baseEnd_2205144] using wordTrace_append hprefix tailTrace_2205144
  have hstable : (prefixWord ++ tailWord_2205144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205144).length < 2 ^ (prefixWord ++ tailWord_2205144).sum := by decide
  have hdescent : baseEnd_2205144 < baseStart_2205144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205201 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_2205201 : Nat := 118140960795 + 2205201 * 2 ^ 59
def prefixEnd_2205201 : Nat := 4983230072969 + 3 ^ 40 * 2205201 * 2
def baseEnd_2205201 : Nat := 1132328052775531874645971

theorem tailTrace_2205201 : CollatzResearch.WordTrace tailWord_2205201 prefixEnd_2205201 1132328052775531874645971 := by
  unfold tailWord_2205201
  simp only [CollatzResearch.WordTrace]
  refine ⟨80430288083940870191791457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53620192055960580127860971 80430288083940870191791457)
  ·
    refine ⟨60322716062955652643843593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80430288083940870191791457 60322716062955652643843593)
    ·
      refine ⟨45242037047216739482882695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60322716062955652643843593 45242037047216739482882695)
      ·
        refine ⟨67863055570825109224324043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45242037047216739482882695 67863055570825109224324043)
        ·
          refine ⟨101794583356237663836486065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67863055570825109224324043 101794583356237663836486065)
          ·
            refine ⟨76345937517178247877364549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101794583356237663836486065 76345937517178247877364549)
            ·
              refine ⟨14314863284470921477005853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76345937517178247877364549 14314863284470921477005853)
              ·
                refine ⟨5368073731676595553877195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14314863284470921477005853 5368073731676595553877195)
                ·
                  refine ⟨8052110597514893330815793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5368073731676595553877195 8052110597514893330815793)
                  ·
                    refine ⟨6039082948136169998111845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8052110597514893330815793 6039082948136169998111845)
                    ·
                      refine ⟨1132328052775531874645971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6039082948136169998111845 1132328052775531874645971)
                      ·
                        rfl

theorem cell23_2205201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_2205201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205201 prefixEnd_2205201 := by exact prefixLift 2205201
  have htrace : WordTrace (prefixWord ++ tailWord_2205201) baseStart_2205201 baseEnd_2205201 := by
    simpa [prefixWord, tailWord_2205201, baseEnd_2205201] using wordTrace_append hprefix tailTrace_2205201
  have hstable : (prefixWord ++ tailWord_2205201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205201).length < 2 ^ (prefixWord ++ tailWord_2205201).sum := by decide
  have hdescent : baseEnd_2205201 < baseStart_2205201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205205 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_2205205 : Nat := 118140960795 + 2205205 * 2 ^ 59
def prefixEnd_2205205 : Nat := 4983230072969 + 3 ^ 40 * 2205205 * 2
def baseEnd_2205205 : Nat := 1132330106698149858995953

theorem tailTrace_2205205 : CollatzResearch.WordTrace tailWord_2205205 prefixEnd_2205205 1132330106698149858995953 := by
  unfold tailWord_2205205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80430433975926378874937069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53620289317284252583291379 80430433975926378874937069)
  ·
    refine ⟨30161412740972392078101401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80430433975926378874937069 30161412740972392078101401)
    ·
      refine ⟨22621059555729294058576051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30161412740972392078101401 22621059555729294058576051)
      ·
        refine ⟨33931589333593941087864077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22621059555729294058576051 33931589333593941087864077)
        ·
          refine ⟨12724346000097727907949029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33931589333593941087864077 12724346000097727907949029)
          ·
            refine ⟨2385814875018323982740443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12724346000097727907949029 2385814875018323982740443)
            ·
              refine ⟨3578722312527485974110665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385814875018323982740443 3578722312527485974110665)
              ·
                refine ⟨2684041734395614480582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3578722312527485974110665 2684041734395614480582999)
                ·
                  refine ⟨4026062601593421720874499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684041734395614480582999 4026062601593421720874499)
                  ·
                    refine ⟨6039093902390132581311749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026062601593421720874499 6039093902390132581311749)
                    ·
                      refine ⟨1132330106698149858995953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6039093902390132581311749 1132330106698149858995953)
                      ·
                        rfl

theorem cell23_2205205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_2205205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205205 prefixEnd_2205205 := by exact prefixLift 2205205
  have htrace : WordTrace (prefixWord ++ tailWord_2205205) baseStart_2205205 baseEnd_2205205 := by
    simpa [prefixWord, tailWord_2205205, baseEnd_2205205] using wordTrace_append hprefix tailTrace_2205205
  have hstable : (prefixWord ++ tailWord_2205205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205205).length < 2 ^ (prefixWord ++ tailWord_2205205).sum := by decide
  have hdescent : baseEnd_2205205 < baseStart_2205205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2205239 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_2205239 : Nat := 118140960795 + 2205239 * 2 ^ 59
def prefixEnd_2205239 : Nat := 4983230072969 + 3 ^ 40 * 2205239 * 2
def baseEnd_2205239 : Nat := 1132347565040402725970797

theorem tailTrace_2205239 : CollatzResearch.WordTrace tailWord_2205239 prefixEnd_2205239 1132347565040402725970797 := by
  unfold tailWord_2205239
  simp only [CollatzResearch.WordTrace]
  refine ⟨80431674057803202681674771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53621116038535468454449847 80431674057803202681674771)
  ·
    refine ⟨120647511086704804022512157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80431674057803202681674771 120647511086704804022512157)
    ·
      refine ⟨45242816657514301508442059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120647511086704804022512157 45242816657514301508442059)
      ·
        refine ⟨67864224986271452262663089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45242816657514301508442059 67864224986271452262663089)
        ·
          refine ⟨50898168739703589196997317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67864224986271452262663089 50898168739703589196997317)
          ·
            refine ⟨9543406638694422974436997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50898168739703589196997317 9543406638694422974436997)
            ·
              refine ⟨1789388744755204307706937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9543406638694422974436997 1789388744755204307706937)
              ·
                refine ⟨1342041558566403230780203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789388744755204307706937 1342041558566403230780203)
                ·
                  refine ⟨2013062337849604846170305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342041558566403230780203 2013062337849604846170305)
                  ·
                    refine ⟨1509796753387203634627729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2013062337849604846170305 1509796753387203634627729)
                    ·
                      refine ⟨1132347565040402725970797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1509796753387203634627729 1132347565040402725970797)
                      ·
                        rfl

theorem cell23_2205239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_2205239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2205239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2205239 prefixEnd_2205239 := by exact prefixLift 2205239
  have htrace : WordTrace (prefixWord ++ tailWord_2205239) baseStart_2205239 baseEnd_2205239 := by
    simpa [prefixWord, tailWord_2205239, baseEnd_2205239] using wordTrace_append hprefix tailTrace_2205239
  have hstable : (prefixWord ++ tailWord_2205239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2205239).length < 2 ^ (prefixWord ++ tailWord_2205239).sum := by decide
  have hdescent : baseEnd_2205239 < baseStart_2205239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2205239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
