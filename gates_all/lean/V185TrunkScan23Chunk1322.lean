import V185TrunkScan23Chunk1321

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7830992 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_7830992 : Nat := 118140960795 + 7830992 * 2 ^ 59
def prefixEnd_7830992 : Nat := 4983230072969 + 3 ^ 40 * 7830992 * 2
def baseEnd_7830992 : Nat := 4021062897513730441485929

theorem tailTrace_7830992 : CollatzResearch.WordTrace tailWord_7830992 prefixEnd_7830992 4021062897513730441485929 := by
  unfold tailWord_7830992
  simp only [CollatzResearch.WordTrace]
  refine ⟨142809871422830442900355615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190413161897107257200474153 142809871422830442900355615)
  ·
    refine ⟨214214807134245664350533423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142809871422830442900355615 214214807134245664350533423)
    ·
      refine ⟨321322210701368496525800135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214214807134245664350533423 321322210701368496525800135)
      ·
        refine ⟨481983316052052744788700203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321322210701368496525800135 481983316052052744788700203)
        ·
          refine ⟨722974974078079117183050305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481983316052052744788700203 722974974078079117183050305)
          ·
            refine ⟨542231230558559337887287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722974974078079117183050305 542231230558559337887287729)
            ·
              refine ⟨406673422918919503415465797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542231230558559337887287729 406673422918919503415465797)
              ·
                refine ⟨76251266797297406890399837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406673422918919503415465797 76251266797297406890399837)
                ·
                  refine ⟨28594225048986527583899939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76251266797297406890399837 28594225048986527583899939)
                  ·
                    refine ⟨42891337573479791375849909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28594225048986527583899939 42891337573479791375849909)
                    ·
                      refine ⟨4021062897513730441485929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42891337573479791375849909 4021062897513730441485929)
                      ·
                        rfl

theorem cell23_7830992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_7830992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7830992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7830992 prefixEnd_7830992 := by exact prefixLift 7830992
  have htrace : WordTrace (prefixWord ++ tailWord_7830992) baseStart_7830992 baseEnd_7830992 := by
    simpa [prefixWord, tailWord_7830992, baseEnd_7830992] using wordTrace_append hprefix tailTrace_7830992
  have hstable : (prefixWord ++ tailWord_7830992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7830992).length < 2 ^ (prefixWord ++ tailWord_7830992).sum := by decide
  have hdescent : baseEnd_7830992 < baseStart_7830992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7830992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831026 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7831026 : Nat := 118140960795 + 7831026 * 2 ^ 59
def prefixEnd_7831026 : Nat := 4983230072969 + 3 ^ 40 * 7831026 * 2
def baseEnd_7831026 : Nat := 4021080355855983308460773

theorem tailTrace_7831026 : CollatzResearch.WordTrace tailWord_7831026 prefixEnd_7831026 4021080355855983308460773 := by
  unfold tailWord_7831026
  simp only [CollatzResearch.WordTrace]
  refine ⟨71405245731884427401862233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190413988618358473071632621 71405245731884427401862233)
  ·
    refine ⟨53553934298913320551396675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71405245731884427401862233 53553934298913320551396675)
    ·
      refine ⟨80330901448369980827095013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53553934298913320551396675 80330901448369980827095013)
      ·
        refine ⟨15062044021569371405080315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80330901448369980827095013 15062044021569371405080315)
        ·
          refine ⟨22593066032354057107620473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15062044021569371405080315 22593066032354057107620473)
          ·
            refine ⟨16944799524265542830715355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22593066032354057107620473 16944799524265542830715355)
            ·
              refine ⟨25417199286398314246073033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16944799524265542830715355 25417199286398314246073033)
              ·
                refine ⟨19062899464798735684554775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25417199286398314246073033 19062899464798735684554775)
                ·
                  refine ⟨28594349197198103526832163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19062899464798735684554775 28594349197198103526832163)
                  ·
                    refine ⟨42891523795797155290248245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28594349197198103526832163 42891523795797155290248245)
                    ·
                      refine ⟨4021080355855983308460773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42891523795797155290248245 4021080355855983308460773)
                      ·
                        rfl

theorem cell23_7831026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7831026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831026 prefixEnd_7831026 := by exact prefixLift 7831026
  have htrace : WordTrace (prefixWord ++ tailWord_7831026) baseStart_7831026 baseEnd_7831026 := by
    simpa [prefixWord, tailWord_7831026, baseEnd_7831026] using wordTrace_append hprefix tailTrace_7831026
  have hstable : (prefixWord ++ tailWord_7831026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831026).length < 2 ^ (prefixWord ++ tailWord_7831026).sum := by decide
  have hdescent : baseEnd_7831026 < baseStart_7831026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831039 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_7831039 : Nat := 118140960795 + 7831039 * 2 ^ 59
def prefixEnd_7831039 : Nat := 4983230072969 + 3 ^ 40 * 7831039 * 2
def baseEnd_7831039 : Nat := 4021087031104491757598213

theorem tailTrace_7831039 : CollatzResearch.WordTrace tailWord_7831039 prefixEnd_7831039 4021087031104491757598213 := by
  unfold tailWord_7831039
  simp only [CollatzResearch.WordTrace]
  refine ⟨285621457076490612827672171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190414304717660408551781447 285621457076490612827672171)
  ·
    refine ⟨428432185614735919241508257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285621457076490612827672171 428432185614735919241508257)
    ·
      refine ⟨321324139211051939431131193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428432185614735919241508257 321324139211051939431131193)
      ·
        refine ⟨240993104408288954573348395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321324139211051939431131193 240993104408288954573348395)
        ·
          refine ⟨361489656612433431860022593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240993104408288954573348395 361489656612433431860022593)
          ·
            refine ⟨271117242459325073895016945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361489656612433431860022593 271117242459325073895016945)
            ·
              refine ⟨203337931844493805421262709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271117242459325073895016945 203337931844493805421262709)
              ·
                refine ⟨19062931110421294258243379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203337931844493805421262709 19062931110421294258243379)
                ·
                  refine ⟨28594396665631941387365069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19062931110421294258243379 28594396665631941387365069)
                  ·
                    refine ⟨10722898749611978020261901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28594396665631941387365069 10722898749611978020261901)
                    ·
                      refine ⟨4021087031104491757598213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10722898749611978020261901 4021087031104491757598213)
                      ·
                        rfl

theorem cell23_7831039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_7831039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831039 prefixEnd_7831039 := by exact prefixLift 7831039
  have htrace : WordTrace (prefixWord ++ tailWord_7831039) baseStart_7831039 baseEnd_7831039 := by
    simpa [prefixWord, tailWord_7831039, baseEnd_7831039] using wordTrace_append hprefix tailTrace_7831039
  have hstable : (prefixWord ++ tailWord_7831039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831039).length < 2 ^ (prefixWord ++ tailWord_7831039).sum := by decide
  have hdescent : baseEnd_7831039 < baseStart_7831039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831066 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2]
def baseStart_7831066 : Nat := 118140960795 + 7831066 * 2 ^ 59
def prefixEnd_7831066 : Nat := 4983230072969 + 3 ^ 40 * 7831066 * 2
def baseEnd_7831066 : Nat := 4021100895082163151960589

theorem tailTrace_7831066 : CollatzResearch.WordTrace tailWord_7831066 prefixEnd_7831066 4021100895082163151960589 := by
  unfold tailWord_7831066
  simp only [CollatzResearch.WordTrace]
  refine ⟨71405610461848199109726263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190414961231595197625936701 71405610461848199109726263)
  ·
    refine ⟨107108415692772298664589395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71405610461848199109726263 107108415692772298664589395)
    ·
      refine ⟨160662623539158447996884093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107108415692772298664589395 160662623539158447996884093)
      ·
        refine ⟨60248483827184417998831535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160662623539158447996884093 60248483827184417998831535)
        ·
          refine ⟨90372725740776626998247303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60248483827184417998831535 90372725740776626998247303)
          ·
            refine ⟨135559088611164940497370955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90372725740776626998247303 135559088611164940497370955)
            ·
              refine ⟨203338632916747410746056433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135559088611164940497370955 203338632916747410746056433)
              ·
                refine ⟨152503974687560558059542325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203338632916747410746056433 152503974687560558059542325)
                ·
                  refine ⟨14297247626958802318082093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152503974687560558059542325 14297247626958802318082093)
                  ·
                    refine ⟨5361467860109550869280785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14297247626958802318082093 5361467860109550869280785)
                    ·
                      refine ⟨4021100895082163151960589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361467860109550869280785 4021100895082163151960589)
                      ·
                        rfl

theorem cell23_7831066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_7831066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831066 prefixEnd_7831066 := by exact prefixLift 7831066
  have htrace : WordTrace (prefixWord ++ tailWord_7831066) baseStart_7831066 baseEnd_7831066 := by
    simpa [prefixWord, tailWord_7831066, baseEnd_7831066] using wordTrace_append hprefix tailTrace_7831066
  have hstable : (prefixWord ++ tailWord_7831066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831066).length < 2 ^ (prefixWord ++ tailWord_7831066).sum := by decide
  have hdescent : baseEnd_7831066 < baseStart_7831066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831069 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7831069 : Nat := 118140960795 + 7831069 * 2 ^ 59
def prefixEnd_7831069 : Nat := 4983230072969 + 3 ^ 40 * 7831069 * 2
def baseEnd_7831069 : Nat := 4021102435524126640223075

theorem tailTrace_7831069 : CollatzResearch.WordTrace tailWord_7831069 prefixEnd_7831069 4021102435524126640223075 := by
  unfold tailWord_7831069
  simp only [CollatzResearch.WordTrace]
  refine ⟨285622551266381927951264261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190415034177587951967509507 285622551266381927951264261)
  ·
    refine ⟨53554228362446611490862049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285622551266381927951264261 53554228362446611490862049)
    ·
      refine ⟨40165671271834958618146537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53554228362446611490862049 40165671271834958618146537)
      ·
        refine ⟨30124253453876218963609903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40165671271834958618146537 30124253453876218963609903)
        ·
          refine ⟨45186380180814328445414855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124253453876218963609903 45186380180814328445414855)
          ·
            refine ⟨67779570271221492668122283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45186380180814328445414855 67779570271221492668122283)
            ·
              refine ⟨101669355406832239002183425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67779570271221492668122283 101669355406832239002183425)
              ·
                refine ⟨76252016555124179251637569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101669355406832239002183425 76252016555124179251637569)
                ·
                  refine ⟨57189012416343134438728177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76252016555124179251637569 57189012416343134438728177)
                  ·
                    refine ⟨42891759312257350829046133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57189012416343134438728177 42891759312257350829046133)
                    ·
                      refine ⟨4021102435524126640223075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42891759312257350829046133 4021102435524126640223075)
                      ·
                        rfl

theorem cell23_7831069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7831069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831069 prefixEnd_7831069 := by exact prefixLift 7831069
  have htrace : WordTrace (prefixWord ++ tailWord_7831069) baseStart_7831069 baseEnd_7831069 := by
    simpa [prefixWord, tailWord_7831069, baseEnd_7831069] using wordTrace_append hprefix tailTrace_7831069
  have hstable : (prefixWord ++ tailWord_7831069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831069).length < 2 ^ (prefixWord ++ tailWord_7831069).sum := by decide
  have hdescent : baseEnd_7831069 < baseStart_7831069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831129 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_7831129 : Nat := 118140960795 + 7831129 * 2 ^ 59
def prefixEnd_7831129 : Nat := 4983230072969 + 3 ^ 40 * 7831129 * 2
def baseEnd_7831129 : Nat := 4021133244363396405472799

theorem tailTrace_7831129 : CollatzResearch.WordTrace tailWord_7831129 prefixEnd_7831129 4021133244363396405472799 := by
  unfold tailWord_7831129
  simp only [CollatzResearch.WordTrace]
  refine ⟨285624739646164558198448441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190416493097443038798965627 285624739646164558198448441)
  ·
    refine ⟨214218554734623418648836331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285624739646164558198448441 214218554734623418648836331)
    ·
      refine ⟨321327832101935127973254497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214218554734623418648836331 321327832101935127973254497)
      ·
        refine ⟨240995874076451345979940873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321327832101935127973254497 240995874076451345979940873)
        ·
          refine ⟨180746905557338509484955655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240995874076451345979940873 180746905557338509484955655)
          ·
            refine ⟨271120358336007764227433483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180746905557338509484955655 271120358336007764227433483)
            ·
              refine ⟨406680537504011646341150225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271120358336007764227433483 406680537504011646341150225)
              ·
                refine ⟨305010403128008734755862669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406680537504011646341150225 305010403128008734755862669)
                ·
                  refine ⟨114378901173003275533448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305010403128008734755862669 114378901173003275533448501)
                  ·
                    refine ⟨10723021984969057081260797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114378901173003275533448501 10723021984969057081260797)
                    ·
                      refine ⟨4021133244363396405472799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723021984969057081260797 4021133244363396405472799)
                      ·
                        rfl

theorem cell23_7831129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_7831129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831129 prefixEnd_7831129 := by exact prefixLift 7831129
  have htrace : WordTrace (prefixWord ++ tailWord_7831129) baseStart_7831129 baseEnd_7831129 := by
    simpa [prefixWord, tailWord_7831129, baseEnd_7831129] using wordTrace_append hprefix tailTrace_7831129
  have hstable : (prefixWord ++ tailWord_7831129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831129).length < 2 ^ (prefixWord ++ tailWord_7831129).sum := by decide
  have hdescent : baseEnd_7831129 < baseStart_7831129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831146 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7831146 : Nat := 118140960795 + 7831146 * 2 ^ 59
def prefixEnd_7831146 : Nat := 4983230072969 + 3 ^ 40 * 7831146 * 2
def baseEnd_7831146 : Nat := 4021141973534522838960221

theorem tailTrace_7831146 : CollatzResearch.WordTrace tailWord_7831146 prefixEnd_7831146 4021141973534522838960221 := by
  unfold tailWord_7831146
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406339921775742525454323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190416906458068646734544861 71406339921775742525454323)
  ·
    refine ⟨107109509882663613788181485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71406339921775742525454323 107109509882663613788181485)
    ·
      refine ⟨40166066205998855170568057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107109509882663613788181485 40166066205998855170568057)
      ·
        refine ⟨30124549654499141377926043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40166066205998855170568057 30124549654499141377926043)
        ·
          refine ⟨45186824481748712066889065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124549654499141377926043 45186824481748712066889065)
          ·
            refine ⟨33890118361311534050166799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45186824481748712066889065 33890118361311534050166799)
            ·
              refine ⟨50835177541967301075250199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33890118361311534050166799 50835177541967301075250199)
              ·
                refine ⟨76252766312950951612875299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50835177541967301075250199 76252766312950951612875299)
                ·
                  refine ⟨114379149469426427419312949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76252766312950951612875299 114379149469426427419312949)
                  ·
                    refine ⟨10723045262758727570560589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114379149469426427419312949 10723045262758727570560589)
                    ·
                      refine ⟨4021141973534522838960221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723045262758727570560589 4021141973534522838960221)
                      ·
                        rfl

theorem cell23_7831146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7831146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831146 prefixEnd_7831146 := by exact prefixLift 7831146
  have htrace : WordTrace (prefixWord ++ tailWord_7831146) baseStart_7831146 baseEnd_7831146 := by
    simpa [prefixWord, tailWord_7831146, baseEnd_7831146] using wordTrace_append hprefix tailTrace_7831146
  have hstable : (prefixWord ++ tailWord_7831146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831146).length < 2 ^ (prefixWord ++ tailWord_7831146).sum := by decide
  have hdescent : baseEnd_7831146 < baseStart_7831146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831189 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7831189 : Nat := 118140960795 + 7831189 * 2 ^ 59
def prefixEnd_7831189 : Nat := 4983230072969 + 3 ^ 40 * 7831189 * 2
def baseEnd_7831189 : Nat := 4021164053202666170722523

theorem tailTrace_7831189 : CollatzResearch.WordTrace tailWord_7831189 prefixEnd_7831189 4021164053202666170722523 := by
  unfold tailWord_7831189
  simp only [CollatzResearch.WordTrace]
  refine ⟨285626928025947188445632621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190417952017298125630421747 285626928025947188445632621)
  ·
    refine ⟨107110098009730195667112233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285626928025947188445632621 107110098009730195667112233)
    ·
      refine ⟨80332573507297646750334175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107110098009730195667112233 80332573507297646750334175)
      ·
        refine ⟨120498860260946470125501263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80332573507297646750334175 120498860260946470125501263)
        ·
          refine ⟨180748290391419705188251895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120498860260946470125501263 180748290391419705188251895)
          ·
            refine ⟨271122435587129557782377843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180748290391419705188251895 271122435587129557782377843)
            ·
              refine ⟨406683653380694336673566765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271122435587129557782377843 406683653380694336673566765)
              ·
                refine ⟨152506370017760376252587537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406683653380694336673566765 152506370017760376252587537)
                ·
                  refine ⟨114379777513320282189440653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152506370017760376252587537 114379777513320282189440653)
                  ·
                    refine ⟨42892416567495105821040245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114379777513320282189440653 42892416567495105821040245)
                    ·
                      refine ⟨4021164053202666170722523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42892416567495105821040245 4021164053202666170722523)
                      ·
                        rfl

theorem cell23_7831189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7831189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831189 prefixEnd_7831189 := by exact prefixLift 7831189
  have htrace : WordTrace (prefixWord ++ tailWord_7831189) baseStart_7831189 baseEnd_7831189 := by
    simpa [prefixWord, tailWord_7831189, baseEnd_7831189] using wordTrace_append hprefix tailTrace_7831189
  have hstable : (prefixWord ++ tailWord_7831189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831189).length < 2 ^ (prefixWord ++ tailWord_7831189).sum := by decide
  have hdescent : baseEnd_7831189 < baseStart_7831189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831213 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7831213 : Nat := 118140960795 + 7831213 * 2 ^ 59
def prefixEnd_7831213 : Nat := 4983230072969 + 3 ^ 40 * 7831213 * 2
def baseEnd_7831213 : Nat := 1340392125579458025607471

theorem tailTrace_7831213 : CollatzResearch.WordTrace tailWord_7831213 prefixEnd_7831213 1340392125579458025607471 := by
  unfold tailWord_7831213
  simp only [CollatzResearch.WordTrace]
  refine ⟨285627803377860240544506293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190418535585240160363004195 285627803377860240544506293)
  ·
    refine ⟨26777606566674397551047465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285627803377860240544506293 26777606566674397551047465)
    ·
      refine ⟨20083204925005798163285599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26777606566674397551047465 20083204925005798163285599)
      ·
        refine ⟨30124807387508697244928399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20083204925005798163285599 30124807387508697244928399)
        ·
          refine ⟨45187211081263045867392599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124807387508697244928399 45187211081263045867392599)
          ·
            refine ⟨67780816621894568801088899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45187211081263045867392599 67780816621894568801088899)
            ·
              refine ⟨101671224932841853201633349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67780816621894568801088899 101671224932841853201633349)
              ·
                refine ⟨19063354674907847475306253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101671224932841853201633349 19063354674907847475306253)
                ·
                  refine ⟨7148758003090442803239845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19063354674907847475306253 7148758003090442803239845)
                  ·
                    refine ⟨1340392125579458025607471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7148758003090442803239845 1340392125579458025607471)
                    ·
                      rfl

theorem cell23_7831213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7831213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831213 prefixEnd_7831213 := by exact prefixLift 7831213
  have htrace : WordTrace (prefixWord ++ tailWord_7831213) baseStart_7831213 baseEnd_7831213 := by
    simpa [prefixWord, tailWord_7831213, baseEnd_7831213] using wordTrace_append hprefix tailTrace_7831213
  have hstable : (prefixWord ++ tailWord_7831213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831213).length < 2 ^ (prefixWord ++ tailWord_7831213).sum := by decide
  have hdescent : baseEnd_7831213 < baseStart_7831213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831256 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_7831256 : Nat := 118140960795 + 7831256 * 2 ^ 59
def prefixEnd_7831256 : Nat := 4983230072969 + 3 ^ 40 * 7831256 * 2
def baseEnd_7831256 : Nat := 1340399485468839136194905

theorem tailTrace_7831256 : CollatzResearch.WordTrace tailWord_7831256 prefixEnd_7831256 1340399485468839136194905 := by
  unfold tailWord_7831256
  simp only [CollatzResearch.WordTrace]
  refine ⟨142814685858352229444160811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190419581144469639258881081 142814685858352229444160811)
  ·
    refine ⟨214222028787528344166241217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142814685858352229444160811 214222028787528344166241217)
    ·
      refine ⟨160666521590646258124680913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214222028787528344166241217 160666521590646258124680913)
      ·
        refine ⟨120499891192984693593510685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160666521590646258124680913 120499891192984693593510685)
        ·
          refine ⟨45187459197369260097566507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120499891192984693593510685 45187459197369260097566507)
          ·
            refine ⟨67781188796053890146349761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45187459197369260097566507 67781188796053890146349761)
            ·
              refine ⟨50835891597040417609762321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67781188796053890146349761 50835891597040417609762321)
              ·
                refine ⟨38126918697780313207321741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50835891597040417609762321 38126918697780313207321741)
                ·
                  refine ⟨14297594511667617452745653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38126918697780313207321741 14297594511667617452745653)
                  ·
                    refine ⟨1340399485468839136194905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14297594511667617452745653 1340399485468839136194905)
                    ·
                      rfl

theorem cell23_7831256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_7831256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831256 prefixEnd_7831256 := by exact prefixLift 7831256
  have htrace : WordTrace (prefixWord ++ tailWord_7831256) baseStart_7831256 baseEnd_7831256 := by
    simpa [prefixWord, tailWord_7831256, baseEnd_7831256] using wordTrace_append hprefix tailTrace_7831256
  have hstable : (prefixWord ++ tailWord_7831256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831256).length < 2 ^ (prefixWord ++ tailWord_7831256).sum := by decide
  have hdescent : baseEnd_7831256 < baseStart_7831256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831260 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 6]
def baseStart_7831260 : Nat := 118140960795 + 7831260 * 2 ^ 59
def prefixEnd_7831260 : Nat := 4983230072969 + 3 ^ 40 * 7831260 * 2
def baseEnd_7831260 : Nat := 446800056703237265881633

theorem tailTrace_7831260 : CollatzResearch.WordTrace tailWord_7831260 prefixEnd_7831260 446800056703237265881633 := by
  unfold tailWord_7831260
  simp only [CollatzResearch.WordTrace]
  refine ⟨142814758804344983785733617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190419678405793311714311489 142814758804344983785733617)
  ·
    refine ⟨107111069103258737839300213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142814758804344983785733617 107111069103258737839300213)
    ·
      refine ⟨10041662728430506672434395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107111069103258737839300213 10041662728430506672434395)
      ·
        refine ⟨15062494092645760008651593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10041662728430506672434395 15062494092645760008651593)
        ·
          refine ⟨11296870569484320006488695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15062494092645760008651593 11296870569484320006488695)
          ·
            refine ⟨16945305854226480009733043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11296870569484320006488695 16945305854226480009733043)
            ·
              refine ⟨25417958781339720014599565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16945305854226480009733043 25417958781339720014599565)
              ·
                refine ⟨9531734543002395005474837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25417958781339720014599565 9531734543002395005474837)
                ·
                  refine ⟨446800056703237265881633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9531734543002395005474837 446800056703237265881633)
                  ·
                    rfl

theorem cell23_7831260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_7831260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831260 prefixEnd_7831260 := by exact prefixLift 7831260
  have htrace : WordTrace (prefixWord ++ tailWord_7831260) baseStart_7831260 baseEnd_7831260 := by
    simpa [prefixWord, tailWord_7831260, baseEnd_7831260] using wordTrace_append hprefix tailTrace_7831260
  have hstable : (prefixWord ++ tailWord_7831260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831260).length < 2 ^ (prefixWord ++ tailWord_7831260).sum := by decide
  have hdescent : baseEnd_7831260 < baseStart_7831260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831263 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 4, 3, 2]
def baseStart_7831263 : Nat := 118140960795 + 7831263 * 2 ^ 59
def prefixEnd_7831263 : Nat := 4983230072969 + 3 ^ 40 * 7831263 * 2
def baseEnd_7831263 : Nat := 4021202050771098881197183

theorem tailTrace_7831263 : CollatzResearch.WordTrace tailWord_7831263 prefixEnd_7831263 4021202050771098881197183 := by
  unfold tailWord_7831263
  simp only [CollatzResearch.WordTrace]
  refine ⟨285629627027679099083826443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190419751351786066055884295 285629627027679099083826443)
  ·
    refine ⟨428444440541518648625739665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285629627027679099083826443 428444440541518648625739665)
    ·
      refine ⟨321333330406138986469304749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428444440541518648625739665 321333330406138986469304749)
      ·
        refine ⟨120499998902302119925989281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321333330406138986469304749 120499998902302119925989281)
        ·
          refine ⟨90374999176726589944491961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120499998902302119925989281 90374999176726589944491961)
          ·
            refine ⟨67781249382544942458368971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90374999176726589944491961 67781249382544942458368971)
            ·
              refine ⟨101671874073817413687553457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67781249382544942458368971 101671874073817413687553457)
              ·
                refine ⟨76253905555363060265665093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101671874073817413687553457 76253905555363060265665093)
                ·
                  refine ⟨14297607291630573799812205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76253905555363060265665093 14297607291630573799812205)
                  ·
                    refine ⟨5361602734361465174929577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14297607291630573799812205 5361602734361465174929577)
                    ·
                      refine ⟨4021202050771098881197183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361602734361465174929577 4021202050771098881197183)
                      ·
                        rfl

theorem cell23_7831263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_7831263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831263 prefixEnd_7831263 := by exact prefixLift 7831263
  have htrace : WordTrace (prefixWord ++ tailWord_7831263) baseStart_7831263 baseEnd_7831263 := by
    simpa [prefixWord, tailWord_7831263, baseEnd_7831263] using wordTrace_append hprefix tailTrace_7831263
  have hstable : (prefixWord ++ tailWord_7831263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831263).length < 2 ^ (prefixWord ++ tailWord_7831263).sum := by decide
  have hdescent : baseEnd_7831263 < baseStart_7831263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831330 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_7831330 : Nat := 118140960795 + 7831330 * 2 ^ 59
def prefixEnd_7831330 : Nat := 4983230072969 + 3 ^ 40 * 7831330 * 2
def baseEnd_7831330 : Nat := 4021236453974950119059375

theorem tailTrace_7831330 : CollatzResearch.WordTrace tailWord_7831330 prefixEnd_7831330 4021236453974950119059375 := by
  unfold tailWord_7831330
  simp only [CollatzResearch.WordTrace]
  refine ⟨71408017679609092381628861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190421380478957579684343629 71408017679609092381628861)
  ·
    refine ⟨26778006629853409643110823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71408017679609092381628861 26778006629853409643110823)
    ·
      refine ⟨40167009944780114464666235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26778006629853409643110823 40167009944780114464666235)
      ·
        refine ⟨60250514917170171696999353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40167009944780114464666235 60250514917170171696999353)
        ·
          refine ⟨45187886187877628772749515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60250514917170171696999353 45187886187877628772749515)
          ·
            refine ⟨67781829281816443159124273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45187886187877628772749515 67781829281816443159124273)
            ·
              refine ⟨50836371961362332369343205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67781829281816443159124273 50836371961362332369343205)
              ·
                refine ⟨9531819742755437319251851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50836371961362332369343205 9531819742755437319251851)
                ·
                  refine ⟨14297729614133155978877777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9531819742755437319251851 14297729614133155978877777)
                  ·
                    refine ⟨10723297210599866984158333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14297729614133155978877777 10723297210599866984158333)
                    ·
                      refine ⟨4021236453974950119059375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723297210599866984158333 4021236453974950119059375)
                      ·
                        rfl

theorem cell23_7831330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_7831330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831330 prefixEnd_7831330 := by exact prefixLift 7831330
  have htrace : WordTrace (prefixWord ++ tailWord_7831330) baseStart_7831330 baseEnd_7831330 := by
    simpa [prefixWord, tailWord_7831330, baseEnd_7831330] using wordTrace_append hprefix tailTrace_7831330
  have hstable : (prefixWord ++ tailWord_7831330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831330).length < 2 ^ (prefixWord ++ tailWord_7831330).sum := by decide
  have hdescent : baseEnd_7831330 < baseStart_7831330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831333 : List Nat := [1, 3, 1, 2, 3, 3, 3, 7]
def baseStart_7831333 : Nat := 118140960795 + 7831333 * 2 ^ 59
def prefixEnd_7831333 : Nat := 4983230072969 + 3 ^ 40 * 7831333 * 2
def baseEnd_7831333 : Nat := 148934740533959763234143

theorem tailTrace_7831333 : CollatzResearch.WordTrace tailWord_7831333 prefixEnd_7831333 148934740533959763234143 := by
  unfold tailWord_7831333
  simp only [CollatzResearch.WordTrace]
  refine ⟨285632180137425501038874653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190421453424950334025916435 285632180137425501038874653)
  ·
    refine ⟨107112067551534562889577995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285632180137425501038874653 107112067551534562889577995)
    ·
      refine ⟨160668101327301844334366993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107112067551534562889577995 160668101327301844334366993)
      ·
        refine ⟨120501075995476383250775245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160668101327301844334366993 120501075995476383250775245)
        ·
          refine ⟨45187903498303643719040717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120501075995476383250775245 45187903498303643719040717)
          ·
            refine ⟨16945463811863866394640269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45187903498303643719040717 16945463811863866394640269)
            ·
              refine ⟨6354548929448949897990101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16945463811863866394640269 6354548929448949897990101)
              ·
                refine ⟨148934740533959763234143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6354548929448949897990101 148934740533959763234143)
                ·
                  rfl

theorem cell23_7831333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 7].length) (baseStart_7831333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831333 prefixEnd_7831333 := by exact prefixLift 7831333
  have htrace : WordTrace (prefixWord ++ tailWord_7831333) baseStart_7831333 baseEnd_7831333 := by
    simpa [prefixWord, tailWord_7831333, baseEnd_7831333] using wordTrace_append hprefix tailTrace_7831333
  have hstable : (prefixWord ++ tailWord_7831333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831333).length < 2 ^ (prefixWord ++ tailWord_7831333).sum := by decide
  have hdescent : baseEnd_7831333 < baseStart_7831333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831343 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_7831343 : Nat := 118140960795 + 7831343 * 2 ^ 59
def prefixEnd_7831343 : Nat := 4983230072969 + 3 ^ 40 * 7831343 * 2
def baseEnd_7831343 : Nat := 4021243129223458568196815

theorem tailTrace_7831343 : CollatzResearch.WordTrace tailWord_7831343 prefixEnd_7831343 4021243129223458568196815 := by
  unfold tailWord_7831343
  simp only [CollatzResearch.WordTrace]
  refine ⟨285632544867389272746738683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190421696578259515164492455 285632544867389272746738683)
  ·
    refine ⟨428448817301083909120108025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285632544867389272746738683 428448817301083909120108025)
    ·
      refine ⟨321336612975812931840081019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428448817301083909120108025 321336612975812931840081019)
      ·
        refine ⟨482004919463719397760121529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321336612975812931840081019 482004919463719397760121529)
        ·
          refine ⟨361503689597789548320091147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482004919463719397760121529 361503689597789548320091147)
          ·
            refine ⟨542255534396684322480136721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361503689597789548320091147 542255534396684322480136721)
            ·
              refine ⟨406691650797513241860102541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542255534396684322480136721 406691650797513241860102541)
              ·
                refine ⟨152509369049067465697538453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406691650797513241860102541 152509369049067465697538453)
                ·
                  refine ⟨7148876674175037454572115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152509369049067465697538453 7148876674175037454572115)
                  ·
                    refine ⟨10723315011262556181858173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7148876674175037454572115 10723315011262556181858173)
                    ·
                      refine ⟨4021243129223458568196815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723315011262556181858173 4021243129223458568196815)
                      ·
                        rfl

theorem cell23_7831343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_7831343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831343 prefixEnd_7831343 := by exact prefixLift 7831343
  have htrace : WordTrace (prefixWord ++ tailWord_7831343) baseStart_7831343 baseEnd_7831343 := by
    simpa [prefixWord, tailWord_7831343, baseEnd_7831343] using wordTrace_append hprefix tailTrace_7831343
  have hstable : (prefixWord ++ tailWord_7831343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831343).length < 2 ^ (prefixWord ++ tailWord_7831343).sum := by decide
  have hdescent : baseEnd_7831343 < baseStart_7831343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831400 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7831400 : Nat := 118140960795 + 7831400 * 2 ^ 59
def prefixEnd_7831400 : Nat := 4983230072969 + 3 ^ 40 * 7831400 * 2
def baseEnd_7831400 : Nat := 4021272397620764845184053

theorem tailTrace_7831400 : CollatzResearch.WordTrace tailWord_7831400 prefixEnd_7831400 4021272397620764845184053 := by
  unfold tailWord_7831400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142817311914091385740781827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190423082552121847654375769 142817311914091385740781827)
  ·
    refine ⟨214225967871137078611172741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142817311914091385740781827 214225967871137078611172741)
    ·
      refine ⟨40167368975838202239594889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214225967871137078611172741 40167368975838202239594889)
      ·
        refine ⟨30125526731878651679696167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40167368975838202239594889 30125526731878651679696167)
        ·
          refine ⟨45188290097817977519544251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30125526731878651679696167 45188290097817977519544251)
          ·
            refine ⟨67782435146726966279316377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45188290097817977519544251 67782435146726966279316377)
            ·
              refine ⟨50836826360045224709487283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67782435146726966279316377 50836826360045224709487283)
              ·
                refine ⟨76255239540067837064230925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50836826360045224709487283 76255239540067837064230925)
                ·
                  refine ⟨28595714827525438899086597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76255239540067837064230925 28595714827525438899086597)
                  ·
                    refine ⟨5361696530161019793578737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28595714827525438899086597 5361696530161019793578737)
                    ·
                      refine ⟨4021272397620764845184053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361696530161019793578737 4021272397620764845184053)
                      ·
                        rfl

theorem cell23_7831400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7831400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831400 prefixEnd_7831400 := by exact prefixLift 7831400
  have htrace : WordTrace (prefixWord ++ tailWord_7831400) baseStart_7831400 baseEnd_7831400 := by
    simpa [prefixWord, tailWord_7831400, baseEnd_7831400] using wordTrace_append hprefix tailTrace_7831400
  have hstable : (prefixWord ++ tailWord_7831400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831400).length < 2 ^ (prefixWord ++ tailWord_7831400).sum := by decide
  have hdescent : baseEnd_7831400 < baseStart_7831400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831417 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 2, 2, 2]
def baseStart_7831417 : Nat := 118140960795 + 7831417 * 2 ^ 59
def prefixEnd_7831417 : Nat := 4983230072969 + 3 ^ 40 * 7831417 * 2
def baseEnd_7831417 : Nat := 4021281126791891278671475

theorem tailTrace_7831417 : CollatzResearch.WordTrace tailWord_7831417 prefixEnd_7831417 4021281126791891278671475 := by
  unfold tailWord_7831417
  simp only [CollatzResearch.WordTrace]
  refine ⟨285635243869121183384932505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190423495912747455589955003 285635243869121183384932505)
  ·
    refine ⟨214226432901840887538699379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285635243869121183384932505 214226432901840887538699379)
    ·
      refine ⟨321339649352761331308049069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214226432901840887538699379 321339649352761331308049069)
      ·
        refine ⟨120502368507285499240518401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321339649352761331308049069 120502368507285499240518401)
        ·
          refine ⟨90376776380464124430388801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120502368507285499240518401 90376776380464124430388801)
          ·
            refine ⟨67782582285348093322791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90376776380464124430388801 67782582285348093322791601)
            ·
              refine ⟨50836936714011069992093701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67782582285348093322791601 50836936714011069992093701)
              ·
                refine ⟨9531925633877075623517569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50836936714011069992093701 9531925633877075623517569)
                ·
                  refine ⟨7148944225407806717638177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9531925633877075623517569 7148944225407806717638177)
                  ·
                    refine ⟨5361708169055855038228633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7148944225407806717638177 5361708169055855038228633)
                    ·
                      refine ⟨4021281126791891278671475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361708169055855038228633 4021281126791891278671475)
                      ·
                        rfl

theorem cell23_7831417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_7831417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831417 prefixEnd_7831417 := by exact prefixLift 7831417
  have htrace : WordTrace (prefixWord ++ tailWord_7831417) baseStart_7831417 baseEnd_7831417 := by
    simpa [prefixWord, tailWord_7831417, baseEnd_7831417] using wordTrace_append hprefix tailTrace_7831417
  have hstable : (prefixWord ++ tailWord_7831417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831417).length < 2 ^ (prefixWord ++ tailWord_7831417).sum := by decide
  have hdescent : baseEnd_7831417 < baseStart_7831417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831433 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_7831433 : Nat := 118140960795 + 7831433 * 2 ^ 59
def prefixEnd_7831433 : Nat := 4983230072969 + 3 ^ 40 * 7831433 * 2
def baseEnd_7831433 : Nat := 4021289342482363216071401

theorem tailTrace_7831433 : CollatzResearch.WordTrace tailWord_7831433 prefixEnd_7831433 4021289342482363216071401 := by
  unfold tailWord_7831433
  simp only [CollatzResearch.WordTrace]
  refine ⟨285635827437063218117514953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190423884958042145411676635 285635827437063218117514953)
  ·
    refine ⟨214226870577797413588136215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285635827437063218117514953 214226870577797413588136215)
    ·
      refine ⟨321340305866696120382204323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214226870577797413588136215 321340305866696120382204323)
      ·
        refine ⟨482010458800044180573306485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321340305866696120382204323 482010458800044180573306485)
        ·
          refine ⟨45188480512504141928747483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 482010458800044180573306485 45188480512504141928747483)
          ·
            refine ⟨67782720768756212893121225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45188480512504141928747483 67782720768756212893121225)
            ·
              refine ⟨50837040576567159669840919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67782720768756212893121225 50837040576567159669840919)
              ·
                refine ⟨76255560864850739504761379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50837040576567159669840919 76255560864850739504761379)
                ·
                  refine ⟨114383341297276109257142069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76255560864850739504761379 114383341297276109257142069)
                  ·
                    refine ⟨10723438246619635242857069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114383341297276109257142069 10723438246619635242857069)
                    ·
                      refine ⟨4021289342482363216071401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723438246619635242857069 4021289342482363216071401)
                      ·
                        rfl

theorem cell23_7831433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_7831433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831433 prefixEnd_7831433 := by exact prefixLift 7831433
  have htrace : WordTrace (prefixWord ++ tailWord_7831433) baseStart_7831433 baseEnd_7831433 := by
    simpa [prefixWord, tailWord_7831433, baseEnd_7831433] using wordTrace_append hprefix tailTrace_7831433
  have hstable : (prefixWord ++ tailWord_7831433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831433).length < 2 ^ (prefixWord ++ tailWord_7831433).sum := by decide
  have hdescent : baseEnd_7831433 < baseStart_7831433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831438 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7831438 : Nat := 118140960795 + 7831438 * 2 ^ 59
def prefixEnd_7831438 : Nat := 4983230072969 + 3 ^ 40 * 7831438 * 2
def baseEnd_7831438 : Nat := 4021291909885635696508879

theorem tailTrace_7831438 : CollatzResearch.WordTrace tailWord_7831438 prefixEnd_7831438 4021291909885635696508879 := by
  unfold tailWord_7831438
  simp only [CollatzResearch.WordTrace]
  refine ⟨35704501225255637996430871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190424006534696735980964645 35704501225255637996430871)
  ·
    refine ⟨53556751837883456994646307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35704501225255637996430871 53556751837883456994646307)
    ·
      refine ⟨80335127756825185491969461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53556751837883456994646307 80335127756825185491969461)
      ·
        refine ⟨7531418227202361139872137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80335127756825185491969461 7531418227202361139872137)
        ·
          refine ⟨5648563670401770854904103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7531418227202361139872137 5648563670401770854904103)
          ·
            refine ⟨8472845505602656282356155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648563670401770854904103 8472845505602656282356155)
            ·
              refine ⟨12709268258403984423534233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8472845505602656282356155 12709268258403984423534233)
              ·
                refine ⟨9531951193802988317650675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12709268258403984423534233 9531951193802988317650675)
                ·
                  refine ⟨14297926790704482476476013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9531951193802988317650675 14297926790704482476476013)
                  ·
                    refine ⟨5361722546514180928678505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14297926790704482476476013 5361722546514180928678505)
                    ·
                      refine ⟨4021291909885635696508879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361722546514180928678505 4021291909885635696508879)
                      ·
                        rfl

theorem cell23_7831438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7831438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831438 prefixEnd_7831438 := by exact prefixLift 7831438
  have htrace : WordTrace (prefixWord ++ tailWord_7831438) baseStart_7831438 baseEnd_7831438 := by
    simpa [prefixWord, tailWord_7831438, baseEnd_7831438] using wordTrace_append hprefix tailTrace_7831438
  have hstable : (prefixWord ++ tailWord_7831438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831438).length < 2 ^ (prefixWord ++ tailWord_7831438).sum := by decide
  have hdescent : baseEnd_7831438 < baseStart_7831438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831500 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_7831500 : Nat := 118140960795 + 7831500 * 2 ^ 59
def prefixEnd_7831500 : Nat := 4983230072969 + 3 ^ 40 * 7831500 * 2
def baseEnd_7831500 : Nat := 1340441248562071484644531

theorem tailTrace_7831500 : CollatzResearch.WordTrace tailWord_7831500 prefixEnd_7831500 1340441248562071484644531 := by
  unfold tailWord_7831500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142819135563910244280101977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190425514085213659040135969 142819135563910244280101977)
  ·
    refine ⟨107114351672932683210076483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142819135563910244280101977 107114351672932683210076483)
    ·
      refine ⟨160671527509399024815114725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107114351672932683210076483 160671527509399024815114725)
      ·
        refine ⟨30125911408012317152834011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160671527509399024815114725 30125911408012317152834011)
        ·
          refine ⟨45188867112018475729251017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30125911408012317152834011 45188867112018475729251017)
          ·
            refine ⟨33891650334013856796938263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45188867112018475729251017 33891650334013856796938263)
            ·
              refine ⟨50837475501020785195407395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33891650334013856796938263 50837475501020785195407395)
              ·
                refine ⟨76256213251531177793111093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50837475501020785195407395 76256213251531177793111093)
                ·
                  refine ⟨7149019992331047918104165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76256213251531177793111093 7149019992331047918104165)
                  ·
                    refine ⟨1340441248562071484644531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149019992331047918104165 1340441248562071484644531)
                    ·
                      rfl

theorem cell23_7831500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_7831500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831500 prefixEnd_7831500 := by exact prefixLift 7831500
  have htrace : WordTrace (prefixWord ++ tailWord_7831500) baseStart_7831500 baseEnd_7831500 := by
    simpa [prefixWord, tailWord_7831500, baseEnd_7831500] using wordTrace_append hprefix tailTrace_7831500
  have hstable : (prefixWord ++ tailWord_7831500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831500).length < 2 ^ (prefixWord ++ tailWord_7831500).sum := by decide
  have hdescent : baseEnd_7831500 < baseStart_7831500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831534 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7831534 : Nat := 118140960795 + 7831534 * 2 ^ 59
def prefixEnd_7831534 : Nat := 4983230072969 + 3 ^ 40 * 7831534 * 2
def baseEnd_7831534 : Nat := 1340447068009489106969479

theorem tailTrace_7831534 : CollatzResearch.WordTrace tailWord_7831534 prefixEnd_7831534 1340447068009489106969479 := by
  unfold tailWord_7831534
  simp only [CollatzResearch.WordTrace]
  refine ⟨35704938901212164045867707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190426340806464874911294437 35704938901212164045867707)
  ·
    refine ⟨53557408351818246068801561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35704938901212164045867707 53557408351818246068801561)
    ·
      refine ⟨40168056263863684551601171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53557408351818246068801561 40168056263863684551601171)
      ·
        refine ⟨60252084395795526827401757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40168056263863684551601171 60252084395795526827401757)
        ·
          refine ⟨22594531648423322560275659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60252084395795526827401757 22594531648423322560275659)
          ·
            refine ⟨33891797472634983840413489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22594531648423322560275659 33891797472634983840413489)
            ·
              refine ⟨25418848104476237880310117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33891797472634983840413489 25418848104476237880310117)
              ·
                refine ⟨4766034019589294602558147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25418848104476237880310117 4766034019589294602558147)
                ·
                  refine ⟨7149051029383941903837221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766034019589294602558147 7149051029383941903837221)
                  ·
                    refine ⟨1340447068009489106969479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149051029383941903837221 1340447068009489106969479)
                    ·
                      rfl

theorem cell23_7831534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7831534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831534 prefixEnd_7831534 := by exact prefixLift 7831534
  have htrace : WordTrace (prefixWord ++ tailWord_7831534) baseStart_7831534 baseEnd_7831534 := by
    simpa [prefixWord, tailWord_7831534, baseEnd_7831534] using wordTrace_append hprefix tailTrace_7831534
  have hstable : (prefixWord ++ tailWord_7831534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831534).length < 2 ^ (prefixWord ++ tailWord_7831534).sum := by decide
  have hdescent : baseEnd_7831534 < baseStart_7831534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831557 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_7831557 : Nat := 118140960795 + 7831557 * 2 ^ 59
def prefixEnd_7831557 : Nat := 4983230072969 + 3 ^ 40 * 7831557 * 2
def baseEnd_7831557 : Nat := 4021353014083520730920831

theorem tailTrace_7831557 : CollatzResearch.WordTrace tailWord_7831557 prefixEnd_7831557 4021353014083520730920831 := by
  unfold tailWord_7831557
  simp only [CollatzResearch.WordTrace]
  refine ⟨285640350088613987295028925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190426900059075991530019283 285640350088613987295028925)
  ·
    refine ⟨107115131283230245235635847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285640350088613987295028925 107115131283230245235635847)
    ·
      refine ⟨160672696924845367853453771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107115131283230245235635847 160672696924845367853453771)
      ·
        refine ⟨241009045387268051780180657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160672696924845367853453771 241009045387268051780180657)
        ·
          refine ⟨180756784040451038835135493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241009045387268051780180657 180756784040451038835135493)
          ·
            refine ⟨33891897007584569781587905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180756784040451038835135493 33891897007584569781587905)
            ·
              refine ⟨25418922755688427336190929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33891897007584569781587905 25418922755688427336190929)
              ·
                refine ⟨19064192066766320502143197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25418922755688427336190929 19064192066766320502143197)
                ·
                  refine ⟨7149072025037370188303699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19064192066766320502143197 7149072025037370188303699)
                  ·
                    refine ⟨10723608037556055282455549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149072025037370188303699 10723608037556055282455549)
                    ·
                      refine ⟨4021353014083520730920831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723608037556055282455549 4021353014083520730920831)
                      ·
                        rfl

theorem cell23_7831557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_7831557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831557 prefixEnd_7831557 := by exact prefixLift 7831557
  have htrace : WordTrace (prefixWord ++ tailWord_7831557) baseStart_7831557 baseEnd_7831557 := by
    simpa [prefixWord, tailWord_7831557, baseEnd_7831557] using wordTrace_append hprefix tailTrace_7831557
  have hstable : (prefixWord ++ tailWord_7831557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831557).length < 2 ^ (prefixWord ++ tailWord_7831557).sum := by decide
  have hdescent : baseEnd_7831557 < baseStart_7831557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831600 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_7831600 : Nat := 118140960795 + 7831600 * 2 ^ 59
def prefixEnd_7831600 : Nat := 4983230072969 + 3 ^ 40 * 7831600 * 2
def baseEnd_7831600 : Nat := 4021375093751664062683133

theorem tailTrace_7831600 : CollatzResearch.WordTrace tailWord_7831600 prefixEnd_7831600 4021375093751664062683133 := by
  unfold tailWord_7831600
  simp only [CollatzResearch.WordTrace]
  refine ⟨142820959213729102819422127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190427945618305470425896169 142820959213729102819422127)
  ·
    refine ⟨214231438820593654229133191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142820959213729102819422127 214231438820593654229133191)
    ·
      refine ⟨321347158230890481343699787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214231438820593654229133191 321347158230890481343699787)
      ·
        refine ⟨482020737346335722015549681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321347158230890481343699787 482020737346335722015549681)
        ·
          refine ⟨361515553009751791511662261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482020737346335722015549681 361515553009751791511662261)
          ·
            refine ⟨33892083094664230454218337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361515553009751791511662261 33892083094664230454218337)
            ·
              refine ⟨25419062320998172840663753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33892083094664230454218337 25419062320998172840663753)
              ·
                refine ⟨19064296740748629630497815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25419062320998172840663753 19064296740748629630497815)
                ·
                  refine ⟨28596445111122944445746723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19064296740748629630497815 28596445111122944445746723)
                  ·
                    refine ⟨42894667666684416668620085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28596445111122944445746723 42894667666684416668620085)
                    ·
                      refine ⟨4021375093751664062683133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42894667666684416668620085 4021375093751664062683133)
                      ·
                        rfl

theorem cell23_7831600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_7831600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831600 prefixEnd_7831600 := by exact prefixLift 7831600
  have htrace : WordTrace (prefixWord ++ tailWord_7831600) baseStart_7831600 baseEnd_7831600 := by
    simpa [prefixWord, tailWord_7831600, baseEnd_7831600] using wordTrace_append hprefix tailTrace_7831600
  have hstable : (prefixWord ++ tailWord_7831600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831600).length < 2 ^ (prefixWord ++ tailWord_7831600).sum := by decide
  have hdescent : baseEnd_7831600 < baseStart_7831600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831603 : List Nat := [1, 1, 1, 2, 4, 1, 3, 10]
def baseStart_7831603 : Nat := 118140960795 + 7831603 * 2 ^ 59
def prefixEnd_7831603 : Nat := 4983230072969 + 3 ^ 40 * 7831603 * 2
def baseEnd_7831603 : Nat := 148939875340504724109097

theorem tailTrace_7831603 : CollatzResearch.WordTrace tailWord_7831603 prefixEnd_7831603 148939875340504724109097 := by
  unfold tailWord_7831603
  simp only [CollatzResearch.WordTrace]
  refine ⟨285642027846447337151203463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190428018564298224767468975 285642027846447337151203463)
  ·
    refine ⟨428463041769671005726805195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285642027846447337151203463 428463041769671005726805195)
    ·
      refine ⟨642694562654506508590207793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428463041769671005726805195 642694562654506508590207793)
      ·
        refine ⟨482020921990879881442655845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642694562654506508590207793 482020921990879881442655845)
        ·
          refine ⟨90378922873289977770497971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482020921990879881442655845 90378922873289977770497971)
          ·
            refine ⟨135568384309934966655746957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90378922873289977770497971 135568384309934966655746957)
            ·
              refine ⟨50838144116225612495905109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135568384309934966655746957 50838144116225612495905109)
              ·
                refine ⟨148939875340504724109097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50838144116225612495905109 148939875340504724109097)
                ·
                  rfl

theorem cell23_7831603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 10].length) (baseStart_7831603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831603 prefixEnd_7831603 := by exact prefixLift 7831603
  have htrace : WordTrace (prefixWord ++ tailWord_7831603) baseStart_7831603 baseEnd_7831603 := by
    simpa [prefixWord, tailWord_7831603, baseEnd_7831603] using wordTrace_append hprefix tailTrace_7831603
  have hstable : (prefixWord ++ tailWord_7831603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831603).length < 2 ^ (prefixWord ++ tailWord_7831603).sum := by decide
  have hdescent : baseEnd_7831603 < baseStart_7831603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831610 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_7831610 : Nat := 118140960795 + 7831610 * 2 ^ 59
def prefixEnd_7831610 : Nat := 4983230072969 + 3 ^ 40 * 7831610 * 2
def baseEnd_7831610 : Nat := 4021380228558209023558087

theorem tailTrace_7831610 : CollatzResearch.WordTrace tailWord_7831610 prefixEnd_7831610 4021380228558209023558087 := by
  unfold tailWord_7831610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410570789355494336677071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190428188771614651564472189 71410570789355494336677071)
  ·
    refine ⟨107115856184033241505015607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71410570789355494336677071 107115856184033241505015607)
    ·
      refine ⟨160673784276049862257523411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107115856184033241505015607 160673784276049862257523411)
      ·
        refine ⟨241010676414074793386285117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160673784276049862257523411 241010676414074793386285117)
        ·
          refine ⟨90379003655278047519856919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241010676414074793386285117 90379003655278047519856919)
          ·
            refine ⟨135568505482917071279785379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90379003655278047519856919 135568505482917071279785379)
            ·
              refine ⟨203352758224375606919678069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135568505482917071279785379 203352758224375606919678069)
              ·
                refine ⟨19064321083535213148719819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203352758224375606919678069 19064321083535213148719819)
                ·
                  refine ⟨28596481625302819723079729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19064321083535213148719819 28596481625302819723079729)
                  ·
                    refine ⟨21447361218977114792309797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28596481625302819723079729 21447361218977114792309797)
                    ·
                      refine ⟨4021380228558209023558087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21447361218977114792309797 4021380228558209023558087)
                      ·
                        rfl

theorem cell23_7831610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_7831610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831610 prefixEnd_7831610 := by exact prefixLift 7831610
  have htrace : WordTrace (prefixWord ++ tailWord_7831610) baseStart_7831610 baseEnd_7831610 := by
    simpa [prefixWord, tailWord_7831610, baseEnd_7831610] using wordTrace_append hprefix tailTrace_7831610
  have hstable : (prefixWord ++ tailWord_7831610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831610).length < 2 ^ (prefixWord ++ tailWord_7831610).sum := by decide
  have hdescent : baseEnd_7831610 < baseStart_7831610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831614 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7831614 : Nat := 118140960795 + 7831614 * 2 ^ 59
def prefixEnd_7831614 : Nat := 4983230072969 + 3 ^ 40 * 7831614 * 2
def baseEnd_7831614 : Nat := 4021382282480827007908069

theorem tailTrace_7831614 : CollatzResearch.WordTrace tailWord_7831614 prefixEnd_7831614 4021382282480827007908069 := by
  unfold tailWord_7831614
  simp only [CollatzResearch.WordTrace]
  refine ⟨35705303631175935753731737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190428286032938324019902597 35705303631175935753731737)
  ·
    refine ⟨26778977723381951815298803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35705303631175935753731737 26778977723381951815298803)
    ·
      refine ⟨40168466585072927722948205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26778977723381951815298803 40168466585072927722948205)
      ·
        refine ⟨15063174969402347896105577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40168466585072927722948205 15063174969402347896105577)
        ·
          refine ⟨11297381227051760922079183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15063174969402347896105577 11297381227051760922079183)
          ·
            refine ⟨16946071840577641383118775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297381227051760922079183 16946071840577641383118775)
            ·
              refine ⟨25419107760866462074678163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946071840577641383118775 25419107760866462074678163)
              ·
                refine ⟨38128661641299693112017245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25419107760866462074678163 38128661641299693112017245)
                ·
                  refine ⟨14298248115487384917006467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38128661641299693112017245 14298248115487384917006467)
                  ·
                    refine ⟨21447372173231077375509701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14298248115487384917006467 21447372173231077375509701)
                    ·
                      refine ⟨4021382282480827007908069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21447372173231077375509701 4021382282480827007908069)
                      ·
                        rfl

theorem cell23_7831614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7831614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831614 prefixEnd_7831614 := by exact prefixLift 7831614
  have htrace : WordTrace (prefixWord ++ tailWord_7831614) baseStart_7831614 baseEnd_7831614 := by
    simpa [prefixWord, tailWord_7831614, baseEnd_7831614] using wordTrace_append hprefix tailTrace_7831614
  have hstable : (prefixWord ++ tailWord_7831614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831614).length < 2 ^ (prefixWord ++ tailWord_7831614).sum := by decide
  have hdescent : baseEnd_7831614 < baseStart_7831614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831634 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_7831634 : Nat := 118140960795 + 7831634 * 2 ^ 59
def prefixEnd_7831634 : Nat := 4983230072969 + 3 ^ 40 * 7831634 * 2
def baseEnd_7831634 : Nat := 4021392552093916929657977

theorem tailTrace_7831634 : CollatzResearch.WordTrace tailWord_7831634 prefixEnd_7831634 4021392552093916929657977 := by
  unfold tailWord_7831634
  simp only [CollatzResearch.WordTrace]
  refine ⟨71410789627333757361395489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190428772339556686297054637 71410789627333757361395489)
  ·
    refine ⟨53558092220500318021046617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71410789627333757361395489 53558092220500318021046617)
    ·
      refine ⟨40168569165375238515784963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53558092220500318021046617 40168569165375238515784963)
      ·
        refine ⟨60252853748062857773677445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40168569165375238515784963 60252853748062857773677445)
        ·
          refine ⟨11297410077761785832564521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60252853748062857773677445 11297410077761785832564521)
          ·
            refine ⟨8473057558321339374423391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297410077761785832564521 8473057558321339374423391)
            ·
              refine ⟨12709586337482009061635087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473057558321339374423391 12709586337482009061635087)
              ·
                refine ⟨19064379506223013592452631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12709586337482009061635087 19064379506223013592452631)
                ·
                  refine ⟨28596569259334520388678947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19064379506223013592452631 28596569259334520388678947)
                  ·
                    refine ⟨42894853889001780583018421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28596569259334520388678947 42894853889001780583018421)
                    ·
                      refine ⟨4021392552093916929657977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42894853889001780583018421 4021392552093916929657977)
                      ·
                        rfl

theorem cell23_7831634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_7831634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831634 prefixEnd_7831634 := by exact prefixLift 7831634
  have htrace : WordTrace (prefixWord ++ tailWord_7831634) baseStart_7831634 baseEnd_7831634 := by
    simpa [prefixWord, tailWord_7831634, baseEnd_7831634] using wordTrace_append hprefix tailTrace_7831634
  have hstable : (prefixWord ++ tailWord_7831634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831634).length < 2 ^ (prefixWord ++ tailWord_7831634).sum := by decide
  have hdescent : baseEnd_7831634 < baseStart_7831634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831648 : List Nat := [2, 1, 1, 3, 2, 3, 4, 2, 1, 2, 2]
def baseStart_7831648 : Nat := 118140960795 + 7831648 * 2 ^ 59
def prefixEnd_7831648 : Nat := 4983230072969 + 3 ^ 40 * 7831648 * 2
def baseEnd_7831648 : Nat := 4021399740823079874882913

theorem tailTrace_7831648 : CollatzResearch.WordTrace tailWord_7831648 prefixEnd_7831648 4021399740823079874882913 := by
  unfold tailWord_7831648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142821834565642154918295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190429112754189539891061065 142821834565642154918295799)
  ·
    refine ⟨214232751848463232377443699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142821834565642154918295799 214232751848463232377443699)
    ·
      refine ⟨321349127772694848566165549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214232751848463232377443699 321349127772694848566165549)
      ·
        refine ⟨120505922914760568212312081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321349127772694848566165549 120505922914760568212312081)
        ·
          refine ⟨90379442186070426159234061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120505922914760568212312081 90379442186070426159234061)
          ·
            refine ⟨33892290819776409809712773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90379442186070426159234061 33892290819776409809712773)
            ·
              refine ⟨6354804528708076839321145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33892290819776409809712773 6354804528708076839321145)
              ·
                refine ⟨4766103396531057629490859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354804528708076839321145 4766103396531057629490859)
                ·
                  refine ⟨7149155094796586444236289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766103396531057629490859 7149155094796586444236289)
                  ·
                    refine ⟨5361866321097439833177217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7149155094796586444236289 5361866321097439833177217)
                    ·
                      refine ⟨4021399740823079874882913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361866321097439833177217 4021399740823079874882913)
                      ·
                        rfl

theorem cell23_7831648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_7831648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831648 prefixEnd_7831648 := by exact prefixLift 7831648
  have htrace : WordTrace (prefixWord ++ tailWord_7831648) baseStart_7831648 baseEnd_7831648 := by
    simpa [prefixWord, tailWord_7831648, baseEnd_7831648] using wordTrace_append hprefix tailTrace_7831648
  have hstable : (prefixWord ++ tailWord_7831648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831648).length < 2 ^ (prefixWord ++ tailWord_7831648).sum := by decide
  have hdescent : baseEnd_7831648 < baseStart_7831648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831657 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 5, 3, 2]
def baseStart_7831657 : Nat := 118140960795 + 7831657 * 2 ^ 59
def prefixEnd_7831657 : Nat := 4983230072969 + 3 ^ 40 * 7831657 * 2
def baseEnd_7831657 : Nat := 4021404362148970339670371

theorem tailTrace_7831657 : CollatzResearch.WordTrace tailWord_7831657 prefixEnd_7831657 4021404362148970339670371 := by
  unfold tailWord_7831657
  simp only [CollatzResearch.WordTrace]
  refine ⟨285643997388251704373669225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190429331592167802915779483 285643997388251704373669225)
  ·
    refine ⟨214232998041188778280251919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285643997388251704373669225 214232998041188778280251919)
    ·
      refine ⟨321349497061783167420377879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214232998041188778280251919 321349497061783167420377879)
      ·
        refine ⟨482024245592674751130566819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321349497061783167420377879 482024245592674751130566819)
        ·
          refine ⟨723036368389012126695850229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482024245592674751130566819 723036368389012126695850229)
          ·
            refine ⟨67784659536469886877735959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 723036368389012126695850229 67784659536469886877735959)
            ·
              refine ⟨101676989304704830316603939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67784659536469886877735959 101676989304704830316603939)
              ·
                refine ⟨152515483957057245474905909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101676989304704830316603939 152515483957057245474905909)
                ·
                  refine ⟨14298326620974116763272429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152515483957057245474905909 14298326620974116763272429)
                  ·
                    refine ⟨5361872482865293786227161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14298326620974116763272429 5361872482865293786227161)
                    ·
                      refine ⟨4021404362148970339670371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5361872482865293786227161 4021404362148970339670371)
                      ·
                        rfl

theorem cell23_7831657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 3, 2].length) (baseStart_7831657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831657 prefixEnd_7831657 := by exact prefixLift 7831657
  have htrace : WordTrace (prefixWord ++ tailWord_7831657) baseStart_7831657 baseEnd_7831657 := by
    simpa [prefixWord, tailWord_7831657, baseEnd_7831657] using wordTrace_append hprefix tailTrace_7831657
  have hstable : (prefixWord ++ tailWord_7831657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831657).length < 2 ^ (prefixWord ++ tailWord_7831657).sum := by decide
  have hdescent : baseEnd_7831657 < baseStart_7831657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831664 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_7831664 : Nat := 118140960795 + 7831664 * 2 ^ 59
def prefixEnd_7831664 : Nat := 4983230072969 + 3 ^ 40 * 7831664 * 2
def baseEnd_7831664 : Nat := 4021407956513551812282839

theorem tailTrace_7831664 : CollatzResearch.WordTrace tailWord_7831664 prefixEnd_7831664 4021407956513551812282839 := by
  unfold tailWord_7831664
  simp only [CollatzResearch.WordTrace]
  refine ⟨142822126349613172284587023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190429501799484229712782697 142822126349613172284587023)
  ·
    refine ⟨214233189524419758426880535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142822126349613172284587023 214233189524419758426880535)
    ·
      refine ⟨321349784286629637640320803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214233189524419758426880535 321349784286629637640320803)
      ·
        refine ⟨482024676429944456460481205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321349784286629637640320803 482024676429944456460481205)
        ·
          refine ⟨45189813415307292793170113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 482024676429944456460481205 45189813415307292793170113)
          ·
            refine ⟨33892360061480469594877585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45189813415307292793170113 33892360061480469594877585)
            ·
              refine ⟨25419270046110352196158189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33892360061480469594877585 25419270046110352196158189)
              ·
                refine ⟨9532226267291382073559321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25419270046110352196158189 9532226267291382073559321)
                ·
                  refine ⟨7149169700468536555169491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9532226267291382073559321 7149169700468536555169491)
                  ·
                    refine ⟨10723754550702804832754237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149169700468536555169491 10723754550702804832754237)
                    ·
                      refine ⟨4021407956513551812282839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10723754550702804832754237 4021407956513551812282839)
                      ·
                        rfl

theorem cell23_7831664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_7831664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831664 prefixEnd_7831664 := by exact prefixLift 7831664
  have htrace : WordTrace (prefixWord ++ tailWord_7831664) baseStart_7831664 baseEnd_7831664 := by
    simpa [prefixWord, tailWord_7831664, baseEnd_7831664] using wordTrace_append hprefix tailTrace_7831664
  have hstable : (prefixWord ++ tailWord_7831664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831664).length < 2 ^ (prefixWord ++ tailWord_7831664).sum := by decide
  have hdescent : baseEnd_7831664 < baseStart_7831664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831744 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 5]
def baseStart_7831744 : Nat := 118140960795 + 7831744 * 2 ^ 59
def prefixEnd_7831744 : Nat := 4983230072969 + 3 ^ 40 * 7831744 * 2
def baseEnd_7831744 : Nat := 446827670551767944364719

theorem tailTrace_7831744 : CollatzResearch.WordTrace tailWord_7831744 prefixEnd_7831744 446827670551767944364719 := by
  unfold tailWord_7831744
  simp only [CollatzResearch.WordTrace]
  refine ⟨142823585269468259116043143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190431447025957678821390857 142823585269468259116043143)
  ·
    refine ⟨214235377904202388674064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142823585269468259116043143 214235377904202388674064715)
    ·
      refine ⟨321353066856303583011097073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214235377904202388674064715 321353066856303583011097073)
      ·
        refine ⟨241014800142227687258322805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321353066856303583011097073 241014800142227687258322805)
        ·
          refine ⟨22595137513333845680467763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241014800142227687258322805 22595137513333845680467763)
          ·
            refine ⟨33892706270000768520701645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22595137513333845680467763 33892706270000768520701645)
            ·
              refine ⟨12709764851250288195263117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33892706270000768520701645 12709764851250288195263117)
              ·
                refine ⟨4766161819218858073223669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12709764851250288195263117 4766161819218858073223669)
                ·
                  refine ⟨446827670551767944364719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766161819218858073223669 446827670551767944364719)
                  ·
                    rfl

theorem cell23_7831744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 5].length) (baseStart_7831744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831744 prefixEnd_7831744 := by exact prefixLift 7831744
  have htrace : WordTrace (prefixWord ++ tailWord_7831744) baseStart_7831744 baseEnd_7831744 := by
    simpa [prefixWord, tailWord_7831744, baseEnd_7831744] using wordTrace_append hprefix tailTrace_7831744
  have hstable : (prefixWord ++ tailWord_7831744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831744).length < 2 ^ (prefixWord ++ tailWord_7831744).sum := by decide
  have hdescent : baseEnd_7831744 < baseStart_7831744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831760 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_7831760 : Nat := 118140960795 + 7831760 * 2 ^ 59
def prefixEnd_7831760 : Nat := 4983230072969 + 3 ^ 40 * 7831760 * 2
def baseEnd_7831760 : Nat := 4021457250656383436682397

theorem tailTrace_7831760 : CollatzResearch.WordTrace tailWord_7831760 prefixEnd_7831760 4021457250656383436682397 := by
  unfold tailWord_7831760
  simp only [CollatzResearch.WordTrace]
  refine ⟨142823877053439276482334367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190431836071252368643112489 142823877053439276482334367)
  ·
    refine ⟨214235815580158914723501551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142823877053439276482334367 214235815580158914723501551)
    ·
      refine ⟨321353723370238372085252327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214235815580158914723501551 321353723370238372085252327)
      ·
        refine ⟨482030585055357558127878491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321353723370238372085252327 482030585055357558127878491)
        ·
          refine ⟨723045877583036337191817737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482030585055357558127878491 723045877583036337191817737)
          ·
            refine ⟨542284408187277252893863303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723045877583036337191817737 542284408187277252893863303)
            ·
              refine ⟨813426612280915879340794955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542284408187277252893863303 813426612280915879340794955)
              ·
                refine ⟨1220139918421373819011192433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813426612280915879340794955 1220139918421373819011192433)
                ·
                  refine ⟨915104938816030364258394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220139918421373819011192433 915104938816030364258394325)
                  ·
                    refine ⟨21447772003500711662306117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 915104938816030364258394325 21447772003500711662306117)
                    ·
                      refine ⟨4021457250656383436682397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21447772003500711662306117 4021457250656383436682397)
                      ·
                        rfl

theorem cell23_7831760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_7831760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831760 prefixEnd_7831760 := by exact prefixLift 7831760
  have htrace : WordTrace (prefixWord ++ tailWord_7831760) baseStart_7831760 baseEnd_7831760 := by
    simpa [prefixWord, tailWord_7831760, baseEnd_7831760] using wordTrace_append hprefix tailTrace_7831760
  have hstable : (prefixWord ++ tailWord_7831760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831760).length < 2 ^ (prefixWord ++ tailWord_7831760).sum := by decide
  have hdescent : baseEnd_7831760 < baseStart_7831760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831777 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_7831777 : Nat := 118140960795 + 7831777 * 2 ^ 59
def prefixEnd_7831777 : Nat := 4983230072969 + 3 ^ 40 * 7831777 * 2
def baseEnd_7831777 : Nat := 4021465979827509870169819

theorem tailTrace_7831777 : CollatzResearch.WordTrace tailWord_7831777 prefixEnd_7831777 4021465979827509870169819 := by
  unfold tailWord_7831777
  simp only [CollatzResearch.WordTrace]
  refine ⟨285648374147816964868037585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190432249431877976578691723 285648374147816964868037585)
  ·
    refine ⟨214236280610862723651028189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285648374147816964868037585 214236280610862723651028189)
    ·
      refine ⟨80338605229073521369135571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214236280610862723651028189 80338605229073521369135571)
      ·
        refine ⟨120507907843610282053703357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80338605229073521369135571 120507907843610282053703357)
        ·
          refine ⟨45190465441353855770138759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120507907843610282053703357 45190465441353855770138759)
          ·
            refine ⟨67785698162030783655208139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45190465441353855770138759 67785698162030783655208139)
            ·
              refine ⟨101678547243046175482812209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67785698162030783655208139 101678547243046175482812209)
              ·
                refine ⟨76258910432284631612109157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101678547243046175482812209 76258910432284631612109157)
                ·
                  refine ⟨14298545706053368427270467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76258910432284631612109157 14298545706053368427270467)
                  ·
                    refine ⟨21447818559080052640905701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14298545706053368427270467 21447818559080052640905701)
                    ·
                      refine ⟨4021465979827509870169819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21447818559080052640905701 4021465979827509870169819)
                      ·
                        rfl

theorem cell23_7831777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_7831777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831777 prefixEnd_7831777 := by exact prefixLift 7831777
  have htrace : WordTrace (prefixWord ++ tailWord_7831777) baseStart_7831777 baseEnd_7831777 := by
    simpa [prefixWord, tailWord_7831777, baseEnd_7831777] using wordTrace_append hprefix tailTrace_7831777
  have hstable : (prefixWord ++ tailWord_7831777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831777).length < 2 ^ (prefixWord ++ tailWord_7831777).sum := by decide
  have hdescent : baseEnd_7831777 < baseStart_7831777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831787 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 5, 4]
def baseStart_7831787 : Nat := 118140960795 + 7831787 * 2 ^ 59
def prefixEnd_7831787 : Nat := 4983230072969 + 3 ^ 40 * 7831787 * 2
def baseEnd_7831787 : Nat := 1340490371544684943681591

theorem tailTrace_7831787 : CollatzResearch.WordTrace tailWord_7831787 prefixEnd_7831787 1340490371544684943681591 := by
  unfold tailWord_7831787
  simp only [CollatzResearch.WordTrace]
  refine ⟨285648738877780736575901615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190432492585187157717267743 285648738877780736575901615)
  ·
    refine ⟨428473108316671104863852423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285648738877780736575901615 428473108316671104863852423)
    ·
      refine ⟨642709662475006657295778635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428473108316671104863852423 642709662475006657295778635)
      ·
        refine ⟨964064493712509985943667953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642709662475006657295778635 964064493712509985943667953)
        ·
          refine ⟨723048370284382489457750965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964064493712509985943667953 723048370284382489457750965)
          ·
            refine ⟨67785784714160858386664153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 723048370284382489457750965 67785784714160858386664153)
            ·
              refine ⟨50839338535620643789998115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67785784714160858386664153 50839338535620643789998115)
              ·
                refine ⟨76259007803430965684997173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50839338535620643789998115 76259007803430965684997173)
                ·
                  refine ⟨7149281981571653032968485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76259007803430965684997173 7149281981571653032968485)
                  ·
                    refine ⟨1340490371544684943681591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149281981571653032968485 1340490371544684943681591)
                    ·
                      rfl

theorem cell23_7831787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 4].length) (baseStart_7831787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831787 prefixEnd_7831787 := by exact prefixLift 7831787
  have htrace : WordTrace (prefixWord ++ tailWord_7831787) baseStart_7831787 baseEnd_7831787 := by
    simpa [prefixWord, tailWord_7831787, baseEnd_7831787] using wordTrace_append hprefix tailTrace_7831787
  have hstable : (prefixWord ++ tailWord_7831787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831787).length < 2 ^ (prefixWord ++ tailWord_7831787).sum := by decide
  have hdescent : baseEnd_7831787 < baseStart_7831787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831794 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_7831794 : Nat := 118140960795 + 7831794 * 2 ^ 59
def prefixEnd_7831794 : Nat := 4983230072969 + 3 ^ 40 * 7831794 * 2
def baseEnd_7831794 : Nat := 4021474708998636303657241

theorem tailTrace_7831794 : CollatzResearch.WordTrace tailWord_7831794 prefixEnd_7831794 4021474708998636303657241 := by
  unfold tailWord_7831794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412248547188844192851609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190432662792503584514270957 71412248547188844192851609)
  ·
    refine ⟨53559186410391633144638707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71412248547188844192851609 53559186410391633144638707)
    ·
      refine ⟨80338779615587449716958061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53559186410391633144638707 80338779615587449716958061)
      ·
        refine ⟨30127042355845293643859273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80338779615587449716958061 30127042355845293643859273)
        ·
          refine ⟨22595281766883970232894455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30127042355845293643859273 22595281766883970232894455)
          ·
            refine ⟨33892922650325955349341683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22595281766883970232894455 33892922650325955349341683)
            ·
              refine ⟨50839383975488933024012525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33892922650325955349341683 50839383975488933024012525)
              ·
                refine ⟨19064768990808349884004697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50839383975488933024012525 19064768990808349884004697)
                ·
                  refine ⟨14298576743106262413003523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19064768990808349884004697 14298576743106262413003523)
                  ·
                    refine ⟨21447865114659393619505285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14298576743106262413003523 21447865114659393619505285)
                    ·
                      refine ⟨4021474708998636303657241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21447865114659393619505285 4021474708998636303657241)
                      ·
                        rfl

theorem cell23_7831794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_7831794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831794 prefixEnd_7831794 := by exact prefixLift 7831794
  have htrace : WordTrace (prefixWord ++ tailWord_7831794) baseStart_7831794 baseEnd_7831794 := by
    simpa [prefixWord, tailWord_7831794, baseEnd_7831794] using wordTrace_append hprefix tailTrace_7831794
  have hstable : (prefixWord ++ tailWord_7831794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831794).length < 2 ^ (prefixWord ++ tailWord_7831794).sum := by decide
  have hdescent : baseEnd_7831794 < baseStart_7831794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831800 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 10]
def baseStart_7831800 : Nat := 118140960795 + 7831800 * 2 ^ 59
def prefixEnd_7831800 : Nat := 4983230072969 + 3 ^ 40 * 7831800 * 2
def baseEnd_7831800 : Nat := 446830865542507031131357

theorem tailTrace_7831800 : CollatzResearch.WordTrace tailWord_7831800 prefixEnd_7831800 446830865542507031131357 := by
  unfold tailWord_7831800
  simp only [CollatzResearch.WordTrace]
  refine ⟨142824606513366819898062427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190432808684489093197416569 142824606513366819898062427)
  ·
    refine ⟨214236909770050229847093641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142824606513366819898062427 214236909770050229847093641)
    ·
      refine ⟨160677682327537672385320231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214236909770050229847093641 160677682327537672385320231)
      ·
        refine ⟨241016523491306508577980347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160677682327537672385320231 241016523491306508577980347)
        ·
          refine ⟨361524785236959762866970521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241016523491306508577980347 361524785236959762866970521)
          ·
            refine ⟨271143588927719822150227891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361524785236959762866970521 271143588927719822150227891)
            ·
              refine ⟨406715383391579733225341837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271143588927719822150227891 406715383391579733225341837)
              ·
                refine ⟨152518268771842399959503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406715383391579733225341837 152518268771842399959503189)
                ·
                  refine ⟨446830865542507031131357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152518268771842399959503189 446830865542507031131357)
                  ·
                    rfl

theorem cell23_7831800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_7831800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831800 prefixEnd_7831800 := by exact prefixLift 7831800
  have htrace : WordTrace (prefixWord ++ tailWord_7831800) baseStart_7831800 baseEnd_7831800 := by
    simpa [prefixWord, tailWord_7831800, baseEnd_7831800] using wordTrace_append hprefix tailTrace_7831800
  have hstable : (prefixWord ++ tailWord_7831800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831800).length < 2 ^ (prefixWord ++ tailWord_7831800).sum := by decide
  have hdescent : baseEnd_7831800 < baseStart_7831800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831817 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 6]
def baseStart_7831817 : Nat := 118140960795 + 7831817 * 2 ^ 59
def prefixEnd_7831817 : Nat := 4983230072969 + 3 ^ 40 * 7831817 * 2
def baseEnd_7831817 : Nat := 446831835450409968185515

theorem tailTrace_7831817 : CollatzResearch.WordTrace tailWord_7831817 prefixEnd_7831817 446831835450409968185515 := by
  unfold tailWord_7831817
  simp only [CollatzResearch.WordTrace]
  refine ⟨285649833067672051699493705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190433222045114701132995803 285649833067672051699493705)
  ·
    refine ⟨214237374800754038774620279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285649833067672051699493705 214237374800754038774620279)
    ·
      refine ⟨321356062201131058161930419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214237374800754038774620279 321356062201131058161930419)
      ·
        refine ⟨482034093301696587242895629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321356062201131058161930419 482034093301696587242895629)
        ·
          refine ⟨180762784988136220216085861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482034093301696587242895629 180762784988136220216085861)
          ·
            refine ⟨33893022185275541290516099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180762784988136220216085861 33893022185275541290516099)
            ·
              refine ⟨50839533277913311935774149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33893022185275541290516099 50839533277913311935774149)
              ·
                refine ⟨9532412489608745987957653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50839533277913311935774149 9532412489608745987957653)
                ·
                  refine ⟨446831835450409968185515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9532412489608745987957653 446831835450409968185515)
                  ·
                    rfl

theorem cell23_7831817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_7831817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831817 prefixEnd_7831817 := by exact prefixLift 7831817
  have htrace : WordTrace (prefixWord ++ tailWord_7831817) baseStart_7831817 baseEnd_7831817 := by
    simpa [prefixWord, tailWord_7831817, baseEnd_7831817] using wordTrace_append hprefix tailTrace_7831817
  have hstable : (prefixWord ++ tailWord_7831817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831817).length < 2 ^ (prefixWord ++ tailWord_7831817).sum := by decide
  have hdescent : baseEnd_7831817 < baseStart_7831817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831838 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7831838 : Nat := 118140960795 + 7831838 * 2 ^ 59
def prefixEnd_7831838 : Nat := 4983230072969 + 3 ^ 40 * 7831838 * 2
def baseEnd_7831838 : Nat := 1340499100715811377169013

theorem tailTrace_7831838 : CollatzResearch.WordTrace tailWord_7831838 prefixEnd_7831838 1340499100715811377169013 := by
  unfold tailWord_7831838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35706324875074496535751021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190433732667063981524005445 35706324875074496535751021)
  ·
    refine ⟨13389871828152936200906633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35706324875074496535751021 13389871828152936200906633)
    ·
      refine ⟨10042403871114702150679975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13389871828152936200906633 10042403871114702150679975)
      ·
        refine ⟨15063605806672053226019963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042403871114702150679975 15063605806672053226019963)
        ·
          refine ⟨22595408710008079839029945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15063605806672053226019963 22595408710008079839029945)
          ·
            refine ⟨16946556532506059879272459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22595408710008079839029945 16946556532506059879272459)
            ·
              refine ⟨25419834798759089818908689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946556532506059879272459 25419834798759089818908689)
              ·
                refine ⟨19064876099069317364181517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25419834798759089818908689 19064876099069317364181517)
                ·
                  refine ⟨7149328537150994011568069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19064876099069317364181517 7149328537150994011568069)
                  ·
                    refine ⟨1340499100715811377169013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149328537150994011568069 1340499100715811377169013)
                    ·
                      rfl

theorem cell23_7831838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7831838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831838 prefixEnd_7831838 := by exact prefixLift 7831838
  have htrace : WordTrace (prefixWord ++ tailWord_7831838) baseStart_7831838 baseEnd_7831838 := by
    simpa [prefixWord, tailWord_7831838, baseEnd_7831838] using wordTrace_append hprefix tailTrace_7831838
  have hstable : (prefixWord ++ tailWord_7831838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831838).length < 2 ^ (prefixWord ++ tailWord_7831838).sum := by decide
  have hdescent : baseEnd_7831838 < baseStart_7831838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831848 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7831848 : Nat := 118140960795 + 7831848 * 2 ^ 59
def prefixEnd_7831848 : Nat := 4983230072969 + 3 ^ 40 * 7831848 * 2
def baseEnd_7831848 : Nat := 4021502436953979092381993

theorem tailTrace_7831848 : CollatzResearch.WordTrace tailWord_7831848 prefixEnd_7831848 4021502436953979092381993 := by
  unfold tailWord_7831848
  simp only [CollatzResearch.WordTrace]
  refine ⟨142825481865279871996936099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190433975820373162662581465 142825481865279871996936099)
  ·
    refine ⟨214238222797919807995404149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142825481865279871996936099 214238222797919807995404149)
    ·
      refine ⟨20084833387304981999569139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214238222797919807995404149 20084833387304981999569139)
      ·
        refine ⟨30127250080957472999353709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20084833387304981999569139 30127250080957472999353709)
        ·
          refine ⟨11297718780359052374757641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30127250080957472999353709 11297718780359052374757641)
          ·
            refine ⟨8473289085269289281068231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297718780359052374757641 8473289085269289281068231)
            ·
              refine ⟨12709933627903933921602347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473289085269289281068231 12709933627903933921602347)
              ·
                refine ⟨19064900441855900882403521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12709933627903933921602347 19064900441855900882403521)
                ·
                  refine ⟨14298675331391925661802641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19064900441855900882403521 14298675331391925661802641)
                  ·
                    refine ⟨10724006498543944246351981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14298675331391925661802641 10724006498543944246351981)
                    ·
                      refine ⟨4021502436953979092381993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724006498543944246351981 4021502436953979092381993)
                      ·
                        rfl

theorem cell23_7831848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7831848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831848 prefixEnd_7831848 := by exact prefixLift 7831848
  have htrace : WordTrace (prefixWord ++ tailWord_7831848) baseStart_7831848 baseEnd_7831848 := by
    simpa [prefixWord, tailWord_7831848, baseEnd_7831848] using wordTrace_append hprefix tailTrace_7831848
  have hstable : (prefixWord ++ tailWord_7831848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831848).length < 2 ^ (prefixWord ++ tailWord_7831848).sum := by decide
  have hdescent : baseEnd_7831848 < baseStart_7831848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_7831887 : Nat := 118140960795 + 7831887 * 2 ^ 59
def prefixEnd_7831887 : Nat := 4983230072969 + 3 ^ 40 * 7831887 * 2
def baseEnd_7831887 : Nat := 4021522462699504439794313

theorem tailTrace_7831887 : CollatzResearch.WordTrace tailWord_7831887 prefixEnd_7831887 4021522462699504439794313 := by
  unfold tailWord_7831887
  simp only [CollatzResearch.WordTrace]
  refine ⟨285652386177418453654541915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190434924118278969103027943 285652386177418453654541915)
  ·
    refine ⟨428478579266127680481812873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285652386177418453654541915 428478579266127680481812873)
    ·
      refine ⟨321358934449595760361359655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428478579266127680481812873 321358934449595760361359655)
      ·
        refine ⟨482038401674393640542039483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321358934449595760361359655 482038401674393640542039483)
        ·
          refine ⟨723057602511590460813059225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482038401674393640542039483 723057602511590460813059225)
          ·
            refine ⟨542293201883692845609794419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723057602511590460813059225 542293201883692845609794419)
            ·
              refine ⟨813439802825539268414691629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542293201883692845609794419 813439802825539268414691629)
              ·
                refine ⟨305039926059577225655509361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813439802825539268414691629 305039926059577225655509361)
                ·
                  refine ⟨228779944544682919241632021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305039926059577225655509361 228779944544682919241632021)
                  ·
                    refine ⟨10724059900532011839451501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228779944544682919241632021 10724059900532011839451501)
                    ·
                      refine ⟨4021522462699504439794313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724059900532011839451501 4021522462699504439794313)
                      ·
                        rfl

theorem cell23_7831887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_7831887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831887 prefixEnd_7831887 := by exact prefixLift 7831887
  have htrace : WordTrace (prefixWord ++ tailWord_7831887) baseStart_7831887 baseEnd_7831887 := by
    simpa [prefixWord, tailWord_7831887, baseEnd_7831887] using wordTrace_append hprefix tailTrace_7831887
  have hstable : (prefixWord ++ tailWord_7831887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831887).length < 2 ^ (prefixWord ++ tailWord_7831887).sum := by decide
  have hdescent : baseEnd_7831887 < baseStart_7831887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831907 : List Nat := [1, 1, 1, 5, 2, 1, 3, 9]
def baseStart_7831907 : Nat := 118140960795 + 7831907 * 2 ^ 59
def prefixEnd_7831907 : Nat := 4983230072969 + 3 ^ 40 * 7831907 * 2
def baseEnd_7831907 : Nat := 148945656752318309686823

theorem tailTrace_7831907 : CollatzResearch.WordTrace tailWord_7831907 prefixEnd_7831907 148945656752318309686823 := by
  unfold tailWord_7831907
  simp only [CollatzResearch.WordTrace]
  refine ⟨285653115637345997070269975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190435410424897331380179983 285653115637345997070269975)
  ·
    refine ⟨428479673456018995605404963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285653115637345997070269975 428479673456018995605404963)
    ·
      refine ⟨642719510184028493408107445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428479673456018995605404963 642719510184028493408107445)
      ·
        refine ⟨60254954079752671257010073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 642719510184028493408107445 60254954079752671257010073)
        ·
          refine ⟨45191215559814503442757555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60254954079752671257010073 45191215559814503442757555)
          ·
            refine ⟨67786823339721755164136333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45191215559814503442757555 67786823339721755164136333)
            ·
              refine ⟨25420058752395658186551125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67786823339721755164136333 25420058752395658186551125)
              ·
                refine ⟨148945656752318309686823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25420058752395658186551125 148945656752318309686823)
                ·
                  rfl

theorem cell23_7831907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 9].length) (baseStart_7831907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831907 prefixEnd_7831907 := by exact prefixLift 7831907
  have htrace : WordTrace (prefixWord ++ tailWord_7831907) baseStart_7831907 baseEnd_7831907 := by
    simpa [prefixWord, tailWord_7831907, baseEnd_7831907] using wordTrace_append hprefix tailTrace_7831907
  have hstable : (prefixWord ++ tailWord_7831907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831907).length < 2 ^ (prefixWord ++ tailWord_7831907).sum := by decide
  have hdescent : baseEnd_7831907 < baseStart_7831907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831957 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7831957 : Nat := 118140960795 + 7831957 * 2 ^ 59
def prefixEnd_7831957 : Nat := 4983230072969 + 3 ^ 40 * 7831957 * 2
def baseEnd_7831957 : Nat := 4021558406345319165918991

theorem tailTrace_7831957 : CollatzResearch.WordTrace tailWord_7831957 prefixEnd_7831957 4021558406345319165918991 := by
  unfold tailWord_7831957
  simp only [CollatzResearch.WordTrace]
  refine ⟨285654939287164855609590125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190436626191443237073060083 285654939287164855609590125)
  ·
    refine ⟨107120602232686820853596297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285654939287164855609590125 107120602232686820853596297)
    ·
      refine ⟨80340451674515115640197223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107120602232686820853596297 80340451674515115640197223)
      ·
        refine ⟨120510677511772673460295835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80340451674515115640197223 120510677511772673460295835)
        ·
          refine ⟨180766016267659010190443753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120510677511772673460295835 180766016267659010190443753)
          ·
            refine ⟨135574512200744257642832815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180766016267659010190443753 135574512200744257642832815)
            ·
              refine ⟨203361768301116386464249223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135574512200744257642832815 203361768301116386464249223)
              ·
                refine ⟨305042652451674579696373835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203361768301116386464249223 305042652451674579696373835)
                ·
                  refine ⟨457563978677511869544560753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305042652451674579696373835 457563978677511869544560753)
                  ·
                    refine ⟨343172984008133902158420565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457563978677511869544560753 343172984008133902158420565)
                    ·
                      refine ⟨4021558406345319165918991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343172984008133902158420565 4021558406345319165918991)
                      ·
                        rfl

theorem cell23_7831957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7831957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831957 prefixEnd_7831957 := by exact prefixLift 7831957
  have htrace : WordTrace (prefixWord ++ tailWord_7831957) baseStart_7831957 baseEnd_7831957 := by
    simpa [prefixWord, tailWord_7831957, baseEnd_7831957] using wordTrace_append hprefix tailTrace_7831957
  have hstable : (prefixWord ++ tailWord_7831957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831957).length < 2 ^ (prefixWord ++ tailWord_7831957).sum := by decide
  have hdescent : baseEnd_7831957 < baseStart_7831957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831961 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 3, 3, 2]
def baseStart_7831961 : Nat := 118140960795 + 7831961 * 2 ^ 59
def prefixEnd_7831961 : Nat := 4983230072969 + 3 ^ 40 * 7831961 * 2
def baseEnd_7831961 : Nat := 4021560460267937150268973

theorem tailTrace_7831961 : CollatzResearch.WordTrace tailWord_7831961 prefixEnd_7831961 4021560460267937150268973 := by
  unfold tailWord_7831961
  simp only [CollatzResearch.WordTrace]
  refine ⟨285655085179150364292735737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190436723452766909528490491 285655085179150364292735737)
  ·
    refine ⟨214241313884362773219551803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285655085179150364292735737 214241313884362773219551803)
    ·
      refine ⟨321361970826544159829327705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214241313884362773219551803 321361970826544159829327705)
      ·
        refine ⟨241021478119908119871995779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321361970826544159829327705 241021478119908119871995779)
        ·
          refine ⟨361532217179862179807993669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241021478119908119871995779 361532217179862179807993669)
          ·
            refine ⟨67787290721224158713998813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361532217179862179807993669 67787290721224158713998813)
            ·
              refine ⟨25420234020459059517749555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67787290721224158713998813 25420234020459059517749555)
              ·
                refine ⟨38130351030688589276624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25420234020459059517749555 38130351030688589276624333)
                ·
                  refine ⟨14298881636508220978734125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38130351030688589276624333 14298881636508220978734125)
                  ·
                    refine ⟨5362080613690582867025297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14298881636508220978734125 5362080613690582867025297)
                    ·
                      refine ⟨4021560460267937150268973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362080613690582867025297 4021560460267937150268973)
                      ·
                        rfl

theorem cell23_7831961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_7831961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831961 prefixEnd_7831961 := by exact prefixLift 7831961
  have htrace : WordTrace (prefixWord ++ tailWord_7831961) baseStart_7831961 baseEnd_7831961 := by
    simpa [prefixWord, tailWord_7831961, baseEnd_7831961] using wordTrace_append hprefix tailTrace_7831961
  have hstable : (prefixWord ++ tailWord_7831961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831961).length < 2 ^ (prefixWord ++ tailWord_7831961).sum := by decide
  have hdescent : baseEnd_7831961 < baseStart_7831961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7831987 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_7831987 : Nat := 118140960795 + 7831987 * 2 ^ 59
def prefixEnd_7831987 : Nat := 4983230072969 + 3 ^ 40 * 7831987 * 2
def baseEnd_7831987 : Nat := 4021573810764954048543853

theorem tailTrace_7831987 : CollatzResearch.WordTrace tailWord_7831987 prefixEnd_7831987 4021573810764954048543853 := by
  unfold tailWord_7831987
  simp only [CollatzResearch.WordTrace]
  refine ⟨285656033477056170733182215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190437355651370780488788143 285656033477056170733182215)
  ·
    refine ⟨428484050215584256099773323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285656033477056170733182215 428484050215584256099773323)
    ·
      refine ⟨642726075323376384149659985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428484050215584256099773323 642726075323376384149659985)
      ·
        refine ⟨482044556492532288112244989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642726075323376384149659985 482044556492532288112244989)
        ·
          refine ⟨180766708684699608042091871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482044556492532288112244989 180766708684699608042091871)
          ·
            refine ⟨271150063027049412063137807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180766708684699608042091871 271150063027049412063137807)
            ·
              refine ⟨406725094540574118094706711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271150063027049412063137807 406725094540574118094706711)
              ·
                refine ⟨610087641810861177142060067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406725094540574118094706711 610087641810861177142060067)
                ·
                  refine ⟨915131462716291765713090101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610087641810861177142060067 915131462716291765713090101)
                  ·
                    refine ⟨85793574629652353035602197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 915131462716291765713090101 85793574629652353035602197)
                    ·
                      refine ⟨4021573810764954048543853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85793574629652353035602197 4021573810764954048543853)
                      ·
                        rfl

theorem cell23_7831987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_7831987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7831987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7831987 prefixEnd_7831987 := by exact prefixLift 7831987
  have htrace : WordTrace (prefixWord ++ tailWord_7831987) baseStart_7831987 baseEnd_7831987 := by
    simpa [prefixWord, tailWord_7831987, baseEnd_7831987] using wordTrace_append hprefix tailTrace_7831987
  have hstable : (prefixWord ++ tailWord_7831987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7831987).length < 2 ^ (prefixWord ++ tailWord_7831987).sum := by decide
  have hdescent : baseEnd_7831987 < baseStart_7831987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7831987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832008 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_7832008 : Nat := 118140960795 + 7832008 * 2 ^ 59
def prefixEnd_7832008 : Nat := 4983230072969 + 3 ^ 40 * 7832008 * 2
def baseEnd_7832008 : Nat := 4021584593858698466381257

theorem tailTrace_7832008 : CollatzResearch.WordTrace tailWord_7832008 prefixEnd_7832008 4021584593858698466381257 := by
  unfold tailWord_7832008
  simp only [CollatzResearch.WordTrace]
  refine ⟨142828399704990045659848339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190437866273320060879797785 142828399704990045659848339)
  ·
    refine ⟨214242599557485068489772509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142828399704990045659848339 214242599557485068489772509)
    ·
      refine ⟨80340974834056900683664691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214242599557485068489772509 80340974834056900683664691)
      ·
        refine ⟨120511462251085351025497037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80340974834056900683664691 120511462251085351025497037)
        ·
          refine ⟨45191798344157006634561389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120511462251085351025497037 45191798344157006634561389)
          ·
            refine ⟨16946924379058877487960521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45191798344157006634561389 16946924379058877487960521)
            ·
              refine ⟨12710193284294158115970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16946924379058877487960521 12710193284294158115970391)
              ·
                refine ⟨19065289926441237173955587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12710193284294158115970391 19065289926441237173955587)
                ·
                  refine ⟨28597934889661855760933381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19065289926441237173955587 28597934889661855760933381)
                  ·
                    refine ⟨5362112791811597955175009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28597934889661855760933381 5362112791811597955175009)
                    ·
                      refine ⟨4021584593858698466381257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362112791811597955175009 4021584593858698466381257)
                      ·
                        rfl

theorem cell23_7832008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_7832008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832008 prefixEnd_7832008 := by exact prefixLift 7832008
  have htrace : WordTrace (prefixWord ++ tailWord_7832008) baseStart_7832008 baseEnd_7832008 := by
    simpa [prefixWord, tailWord_7832008, baseEnd_7832008] using wordTrace_append hprefix tailTrace_7832008
  have hstable : (prefixWord ++ tailWord_7832008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832008).length < 2 ^ (prefixWord ++ tailWord_7832008).sum := by decide
  have hdescent : baseEnd_7832008 < baseStart_7832008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832024 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_7832024 : Nat := 118140960795 + 7832024 * 2 ^ 59
def prefixEnd_7832024 : Nat := 4983230072969 + 3 ^ 40 * 7832024 * 2
def baseEnd_7832024 : Nat := 4021592809549170403781183

theorem tailTrace_7832024 : CollatzResearch.WordTrace tailWord_7832024 prefixEnd_7832024 4021592809549170403781183 := by
  unfold tailWord_7832024
  simp only [CollatzResearch.WordTrace]
  refine ⟨142828691488961063026139563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190438255318614750701519417 142828691488961063026139563)
  ·
    refine ⟨214243037233441594539209345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142828691488961063026139563 214243037233441594539209345)
    ·
      refine ⟨160682277925081195904407009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214243037233441594539209345 160682277925081195904407009)
      ·
        refine ⟨120511708443810896928305257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160682277925081195904407009 120511708443810896928305257)
        ·
          refine ⟨90383781332858172696228943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120511708443810896928305257 90383781332858172696228943)
          ·
            refine ⟨135575671999287259044343415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90383781332858172696228943 135575671999287259044343415)
            ·
              refine ⟨203363507998930888566515123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135575671999287259044343415 203363507998930888566515123)
              ·
                refine ⟨305045261998396332849772685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203363507998930888566515123 305045261998396332849772685)
                ·
                  refine ⟨114391973249398624818664757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305045261998396332849772685 114391973249398624818664757)
                  ·
                    refine ⟨10724247492131121076749821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114391973249398624818664757 10724247492131121076749821)
                    ·
                      refine ⟨4021592809549170403781183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724247492131121076749821 4021592809549170403781183)
                      ·
                        rfl

theorem cell23_7832024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_7832024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832024 prefixEnd_7832024 := by exact prefixLift 7832024
  have htrace : WordTrace (prefixWord ++ tailWord_7832024) baseStart_7832024 baseEnd_7832024 := by
    simpa [prefixWord, tailWord_7832024, baseEnd_7832024] using wordTrace_append hprefix tailTrace_7832024
  have hstable : (prefixWord ++ tailWord_7832024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832024).length < 2 ^ (prefixWord ++ tailWord_7832024).sum := by decide
  have hdescent : baseEnd_7832024 < baseStart_7832024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832031 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 5]
def baseStart_7832031 : Nat := 118140960795 + 7832031 * 2 ^ 59
def prefixEnd_7832031 : Nat := 4983230072969 + 3 ^ 40 * 7832031 * 2
def baseEnd_7832031 : Nat := 446844044879305764043739

theorem tailTrace_7832031 : CollatzResearch.WordTrace tailWord_7832031 prefixEnd_7832031 446844044879305764043739 := by
  unfold tailWord_7832031
  simp only [CollatzResearch.WordTrace]
  refine ⟨285657638288896766247783947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190438425525931177498522631 285657638288896766247783947)
  ·
    refine ⟨428486457433345149371675921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285657638288896766247783947 428486457433345149371675921)
    ·
      refine ⟨321364843075008862028756941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428486457433345149371675921 321364843075008862028756941)
      ·
        refine ⟨120511816153128323260783853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321364843075008862028756941 120511816153128323260783853)
        ·
          refine ⟨45191931057423121222793945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120511816153128323260783853 45191931057423121222793945)
          ·
            refine ⟨33893948293067340917095459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45191931057423121222793945 33893948293067340917095459)
            ·
              refine ⟨50840922439601011375643189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33893948293067340917095459 50840922439601011375643189)
              ·
                refine ⟨4766336478712594816466549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50840922439601011375643189 4766336478712594816466549)
                ·
                  refine ⟨446844044879305764043739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766336478712594816466549 446844044879305764043739)
                  ·
                    rfl

theorem cell23_7832031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 5].length) (baseStart_7832031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832031 prefixEnd_7832031 := by exact prefixLift 7832031
  have htrace : WordTrace (prefixWord ++ tailWord_7832031) baseStart_7832031 baseEnd_7832031 := by
    simpa [prefixWord, tailWord_7832031, baseEnd_7832031] using wordTrace_append hprefix tailTrace_7832031
  have hstable : (prefixWord ++ tailWord_7832031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832031).length < 2 ^ (prefixWord ++ tailWord_7832031).sum := by decide
  have hdescent : baseEnd_7832031 < baseStart_7832031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832042 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_7832042 : Nat := 118140960795 + 7832042 * 2 ^ 59
def prefixEnd_7832042 : Nat := 4983230072969 + 3 ^ 40 * 7832042 * 2
def baseEnd_7832042 : Nat := 4021602052200951333356101

theorem tailTrace_7832042 : CollatzResearch.WordTrace tailWord_7832042 prefixEnd_7832042 4021602052200951333356101 := by
  unfold tailWord_7832042
  simp only [CollatzResearch.WordTrace]
  refine ⟨71414509872964228781608595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190438692994571276750956253 71414509872964228781608595)
  ·
    refine ⟨107121764809446343172412893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71414509872964228781608595 107121764809446343172412893)
    ·
      refine ⟨40170661803542378689654835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107121764809446343172412893 40170661803542378689654835)
      ·
        refine ⟨60255992705313568034482253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40170661803542378689654835 60255992705313568034482253)
        ·
          refine ⟨22595997264492588012930845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60255992705313568034482253 22595997264492588012930845)
          ·
            refine ⟨8473498974184720504849067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22595997264492588012930845 8473498974184720504849067)
            ·
              refine ⟨12710248461277080757273601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473498974184720504849067 12710248461277080757273601)
              ·
                refine ⟨9532686345957810567955201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12710248461277080757273601 9532686345957810567955201)
                ·
                  refine ⟨7149514759468357925966401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9532686345957810567955201 7149514759468357925966401)
                  ·
                    refine ⟨5362136069601268444474801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7149514759468357925966401 5362136069601268444474801)
                    ·
                      refine ⟨4021602052200951333356101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362136069601268444474801 4021602052200951333356101)
                      ·
                        rfl

theorem cell23_7832042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_7832042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832042 prefixEnd_7832042 := by exact prefixLift 7832042
  have htrace : WordTrace (prefixWord ++ tailWord_7832042) baseStart_7832042 baseEnd_7832042 := by
    simpa [prefixWord, tailWord_7832042, baseEnd_7832042] using wordTrace_append hprefix tailTrace_7832042
  have hstable : (prefixWord ++ tailWord_7832042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832042).length < 2 ^ (prefixWord ++ tailWord_7832042).sum := by decide
  have hdescent : baseEnd_7832042 < baseStart_7832042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832044 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_7832044 : Nat := 118140960795 + 7832044 * 2 ^ 59
def prefixEnd_7832044 : Nat := 4983230072969 + 3 ^ 40 * 7832044 * 2
def baseEnd_7832044 : Nat := 1340534359720753441843697

theorem tailTrace_7832044 : CollatzResearch.WordTrace tailWord_7832044 prefixEnd_7832044 1340534359720753441843697 := by
  unfold tailWord_7832044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142829056218924834734003593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190438741625233112978671457 142829056218924834734003593)
  ·
    refine ⟨107121792164193626050502695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142829056218924834734003593 107121792164193626050502695)
    ·
      refine ⟨160682688246290439075754043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107121792164193626050502695 160682688246290439075754043)
      ·
        refine ⟨241024032369435658613631065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160682688246290439075754043 241024032369435658613631065)
        ·
          refine ⟨180768024277076743960223299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241024032369435658613631065 180768024277076743960223299)
          ·
            refine ⟨271152036415615115940334949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180768024277076743960223299 271152036415615115940334949)
            ·
              refine ⟨50841006827927834238812803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271152036415615115940334949 50841006827927834238812803)
              ·
                refine ⟨76261510241891751358219205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50841006827927834238812803 76261510241891751358219205)
                ·
                  refine ⟨14299033170354703379666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76261510241891751358219205 14299033170354703379666101)
                  ·
                    refine ⟨1340534359720753441843697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14299033170354703379666101 1340534359720753441843697)
                    ·
                      rfl

theorem cell23_7832044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_7832044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832044 prefixEnd_7832044 := by exact prefixLift 7832044
  have htrace : WordTrace (prefixWord ++ tailWord_7832044) baseStart_7832044 baseEnd_7832044 := by
    simpa [prefixWord, tailWord_7832044, baseEnd_7832044] using wordTrace_append hprefix tailTrace_7832044
  have hstable : (prefixWord ++ tailWord_7832044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832044).length < 2 ^ (prefixWord ++ tailWord_7832044).sum := by decide
  have hdescent : baseEnd_7832044 < baseStart_7832044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832074 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_7832074 : Nat := 118140960795 + 7832074 * 2 ^ 59
def prefixEnd_7832074 : Nat := 4983230072969 + 3 ^ 40 * 7832074 * 2
def baseEnd_7832074 : Nat := 1340539494527298402718651

theorem tailTrace_7832074 : CollatzResearch.WordTrace tailWord_7832074 prefixEnd_7832074 1340539494527298402718651 := by
  unfold tailWord_7832074
  simp only [CollatzResearch.WordTrace]
  refine ⟨71414801656935246147899819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190439471085160656394399517 71414801656935246147899819)
  ·
    refine ⟨107122202485402869221849729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71414801656935246147899819 107122202485402869221849729)
    ·
      refine ⟨80341651864052151916387297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107122202485402869221849729 80341651864052151916387297)
      ·
        refine ⟨60256238898039113937290473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80341651864052151916387297 60256238898039113937290473)
        ·
          refine ⟨45192179173529335452967855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60256238898039113937290473 45192179173529335452967855)
          ·
            refine ⟨67788268760294003179451783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45192179173529335452967855 67788268760294003179451783)
            ·
              refine ⟨101682403140441004769177675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67788268760294003179451783 101682403140441004769177675)
              ·
                refine ⟨152523604710661507153766513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101682403140441004769177675 152523604710661507153766513)
                ·
                  refine ⟨114392703532996130365324885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152523604710661507153766513 114392703532996130365324885)
                  ·
                    refine ⟨1340539494527298402718651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114392703532996130365324885 1340539494527298402718651)
                    ·
                      rfl

theorem cell23_7832074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_7832074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832074 prefixEnd_7832074 := by exact prefixLift 7832074
  have htrace : WordTrace (prefixWord ++ tailWord_7832074) baseStart_7832074 baseEnd_7832074 := by
    simpa [prefixWord, tailWord_7832074, baseEnd_7832074] using wordTrace_append hprefix tailTrace_7832074
  have hstable : (prefixWord ++ tailWord_7832074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832074).length < 2 ^ (prefixWord ++ tailWord_7832074).sum := by decide
  have hdescent : baseEnd_7832074 < baseStart_7832074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832081 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_7832081 : Nat := 118140960795 + 7832081 * 2 ^ 59
def prefixEnd_7832081 : Nat := 4983230072969 + 3 ^ 40 * 7832081 * 2
def baseEnd_7832081 : Nat := 4021622077946476680768421

theorem tailTrace_7832081 : CollatzResearch.WordTrace tailWord_7832081 prefixEnd_7832081 4021622077946476680768421 := by
  unfold tailWord_7832081
  simp only [CollatzResearch.WordTrace]
  refine ⟨285659461938715624787104097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190439641292477083191402731 285659461938715624787104097)
  ·
    refine ⟨214244596454036718590328073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285659461938715624787104097 214244596454036718590328073)
    ·
      refine ⟨160683447340527538942746055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214244596454036718590328073 160683447340527538942746055)
      ·
        refine ⟨241025171010791308414119083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160683447340527538942746055 241025171010791308414119083)
        ·
          refine ⟨361537756516186962621178625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241025171010791308414119083 361537756516186962621178625)
          ·
            refine ⟨271153317387140221965883969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361537756516186962621178625 271153317387140221965883969)
            ·
              refine ⟨203364988040355166474412977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271153317387140221965883969 203364988040355166474412977)
              ·
                refine ⟨152523741030266374855809733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203364988040355166474412977 152523741030266374855809733)
                ·
                  refine ⟨28598201443174945285464325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152523741030266374855809733 28598201443174945285464325)
                  ·
                    refine ⟨5362162770595302241024561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28598201443174945285464325 5362162770595302241024561)
                    ·
                      refine ⟨4021622077946476680768421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362162770595302241024561 4021622077946476680768421)
                      ·
                        rfl

theorem cell23_7832081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_7832081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832081 prefixEnd_7832081 := by exact prefixLift 7832081
  have htrace : WordTrace (prefixWord ++ tailWord_7832081) baseStart_7832081 baseEnd_7832081 := by
    simpa [prefixWord, tailWord_7832081, baseEnd_7832081] using wordTrace_append hprefix tailTrace_7832081
  have hstable : (prefixWord ++ tailWord_7832081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832081).length < 2 ^ (prefixWord ++ tailWord_7832081).sum := by decide
  have hdescent : baseEnd_7832081 < baseStart_7832081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832101 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_7832101 : Nat := 118140960795 + 7832101 * 2 ^ 59
def prefixEnd_7832101 : Nat := 4983230072969 + 3 ^ 40 * 7832101 * 2
def baseEnd_7832101 : Nat := 4021632347559566602518329

theorem tailTrace_7832101 : CollatzResearch.WordTrace tailWord_7832101 prefixEnd_7832101 4021632347559566602518329 := by
  unfold tailWord_7832101
  simp only [CollatzResearch.WordTrace]
  refine ⟨285660191398643168202832157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190440127599095445468554771 285660191398643168202832157)
  ·
    refine ⟨107122571774491188076062059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285660191398643168202832157 107122571774491188076062059)
    ·
      refine ⟨160683857661736782114093089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107122571774491188076062059 160683857661736782114093089)
      ·
        refine ⟨120512893246302586585569817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160683857661736782114093089 120512893246302586585569817)
        ·
          refine ⟨90384669934726939939177363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120512893246302586585569817 90384669934726939939177363)
          ·
            refine ⟨135577004902090409908766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90384669934726939939177363 135577004902090409908766045)
            ·
              refine ⟨50841376838283903715787267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135577004902090409908766045 50841376838283903715787267)
              ·
                refine ⟨76262065257425855573680901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50841376838283903715787267 76262065257425855573680901)
                ·
                  refine ⟨14299137235767347920065169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76262065257425855573680901 14299137235767347920065169)
                  ·
                    refine ⟨10724352926825510940048877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14299137235767347920065169 10724352926825510940048877)
                    ·
                      refine ⟨4021632347559566602518329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724352926825510940048877 4021632347559566602518329)
                      ·
                        rfl

theorem cell23_7832101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_7832101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832101 prefixEnd_7832101 := by exact prefixLift 7832101
  have htrace : WordTrace (prefixWord ++ tailWord_7832101) baseStart_7832101 baseEnd_7832101 := by
    simpa [prefixWord, tailWord_7832101, baseEnd_7832101] using wordTrace_append hprefix tailTrace_7832101
  have hstable : (prefixWord ++ tailWord_7832101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832101).length < 2 ^ (prefixWord ++ tailWord_7832101).sum := by decide
  have hdescent : baseEnd_7832101 < baseStart_7832101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832108 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_7832108 : Nat := 118140960795 + 7832108 * 2 ^ 59
def prefixEnd_7832108 : Nat := 4983230072969 + 3 ^ 40 * 7832108 * 2
def baseEnd_7832108 : Nat := 1340545313974716025043599

theorem tailTrace_7832108 : CollatzResearch.WordTrace tailWord_7832108 prefixEnd_7832108 1340545313974716025043599 := by
  unfold tailWord_7832108
  simp only [CollatzResearch.WordTrace]
  refine ⟨142830223354808904199168489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190440297806411872265557985 142830223354808904199168489)
  ·
    refine ⟨107122667516106678149376367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142830223354808904199168489 107122667516106678149376367)
    ·
      refine ⟨160684001274160017224064551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107122667516106678149376367 160684001274160017224064551)
      ·
        refine ⟨241026001911240025836096827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160684001274160017224064551 241026001911240025836096827)
        ·
          refine ⟨361539002866860038754145241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241026001911240025836096827 361539002866860038754145241)
          ·
            refine ⟨271154252150145029065608931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361539002866860038754145241 271154252150145029065608931)
            ·
              refine ⟨406731378225217543598413397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271154252150145029065608931 406731378225217543598413397)
              ·
                refine ⟨4766383338576768089043907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 406731378225217543598413397 4766383338576768089043907)
                ·
                  refine ⟨7149575007865152133565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766383338576768089043907 7149575007865152133565861)
                  ·
                    refine ⟨1340545313974716025043599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149575007865152133565861 1340545313974716025043599)
                    ·
                      rfl

theorem cell23_7832108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_7832108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832108 prefixEnd_7832108 := by exact prefixLift 7832108
  have htrace : WordTrace (prefixWord ++ tailWord_7832108) baseStart_7832108 baseEnd_7832108 := by
    simpa [prefixWord, tailWord_7832108, baseEnd_7832108] using wordTrace_append hprefix tailTrace_7832108
  have hstable : (prefixWord ++ tailWord_7832108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832108).length < 2 ^ (prefixWord ++ tailWord_7832108).sum := by decide
  have hdescent : baseEnd_7832108 < baseStart_7832108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832121 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 6]
def baseStart_7832121 : Nat := 118140960795 + 7832121 * 2 ^ 59
def prefixEnd_7832121 : Nat := 4983230072969 + 3 ^ 40 * 7832121 * 2
def baseEnd_7832121 : Nat := 446849179685850724918693

theorem tailTrace_7832121 : CollatzResearch.WordTrace tailWord_7832121 prefixEnd_7832121 446849179685850724918693 := by
  unfold tailWord_7832121
  simp only [CollatzResearch.WordTrace]
  refine ⟨285660920858570711618560217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190440613905713807745706811 285660920858570711618560217)
  ·
    refine ⟨214245690643928033713920163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285660920858570711618560217 214245690643928033713920163)
    ·
      refine ⟨321368535965892050570880245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214245690643928033713920163 321368535965892050570880245)
      ·
        refine ⟨30128300246802379741020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321368535965892050570880245 30128300246802379741020023)
        ·
          refine ⟨45192450370203569611530035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30128300246802379741020023 45192450370203569611530035)
          ·
            refine ⟨67788675555305354417295053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45192450370203569611530035 67788675555305354417295053)
            ·
              refine ⟨25420753333239507906485645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67788675555305354417295053 25420753333239507906485645)
              ·
                refine ⟨9532782499964815464932117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25420753333239507906485645 9532782499964815464932117)
                ·
                  refine ⟨446849179685850724918693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9532782499964815464932117 446849179685850724918693)
                  ·
                    rfl

theorem cell23_7832121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_7832121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832121 prefixEnd_7832121 := by exact prefixLift 7832121
  have htrace : WordTrace (prefixWord ++ tailWord_7832121) baseStart_7832121 baseEnd_7832121 := by
    simpa [prefixWord, tailWord_7832121, baseEnd_7832121] using wordTrace_append hprefix tailTrace_7832121
  have hstable : (prefixWord ++ tailWord_7832121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832121).length < 2 ^ (prefixWord ++ tailWord_7832121).sum := by decide
  have hdescent : baseEnd_7832121 < baseStart_7832121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832144 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_7832144 : Nat := 118140960795 + 7832144 * 2 ^ 59
def prefixEnd_7832144 : Nat := 4983230072969 + 3 ^ 40 * 7832144 * 2
def baseEnd_7832144 : Nat := 4021654427227709934280631

theorem tailTrace_7832144 : CollatzResearch.WordTrace tailWord_7832144 prefixEnd_7832144 4021654427227709934280631 := by
  unfold tailWord_7832144
  simp only [CollatzResearch.WordTrace]
  refine ⟨142830879868743693273323743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190441173158324924364431657 142830879868743693273323743)
  ·
    refine ⟨214246319803115539909985615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142830879868743693273323743 214246319803115539909985615)
    ·
      refine ⟨321369479704673309864978423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214246319803115539909985615 321369479704673309864978423)
      ·
        refine ⟨482054219557009964797467635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321369479704673309864978423 482054219557009964797467635)
        ·
          refine ⟨723081329335514947196201453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482054219557009964797467635 723081329335514947196201453)
          ·
            refine ⟨271155498500818105198575545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 723081329335514947196201453 271155498500818105198575545)
            ·
              refine ⟨203366623875613578898931659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271155498500818105198575545 203366623875613578898931659)
              ·
                refine ⟨305049935813420368348397489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203366623875613578898931659 305049935813420368348397489)
                ·
                  refine ⟨228787451860065276261298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305049935813420368348397489 228787451860065276261298117)
                  ·
                    refine ⟨42897647223762239298993397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228787451860065276261298117 42897647223762239298993397)
                    ·
                      refine ⟨4021654427227709934280631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42897647223762239298993397 4021654427227709934280631)
                      ·
                        rfl

theorem cell23_7832144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_7832144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832144 prefixEnd_7832144 := by exact prefixLift 7832144
  have htrace : WordTrace (prefixWord ++ tailWord_7832144) baseStart_7832144 baseEnd_7832144 := by
    simpa [prefixWord, tailWord_7832144, baseEnd_7832144] using wordTrace_append hprefix tailTrace_7832144
  have hstable : (prefixWord ++ tailWord_7832144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832144).length < 2 ^ (prefixWord ++ tailWord_7832144).sum := by decide
  have hdescent : baseEnd_7832144 < baseStart_7832144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832182 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_7832182 : Nat := 118140960795 + 7832182 * 2 ^ 59
def prefixEnd_7832182 : Nat := 4983230072969 + 3 ^ 40 * 7832182 * 2
def baseEnd_7832182 : Nat := 4021673939492580785605457

theorem tailTrace_7832182 : CollatzResearch.WordTrace tailWord_7832182 prefixEnd_7832182 4021673939492580785605457 := by
  unfold tailWord_7832182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853946606959357439783175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190442097140899812691020533 17853946606959357439783175)
  ·
    refine ⟨26780919910439036159674763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853946606959357439783175 26780919910439036159674763)
    ·
      refine ⟨40171379865658554239512145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26780919910439036159674763 40171379865658554239512145)
      ·
        refine ⟨30128534899243915679634109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40171379865658554239512145 30128534899243915679634109)
        ·
          refine ⟨11298200587216468379862791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30128534899243915679634109 11298200587216468379862791)
          ·
            refine ⟨16947300880824702569794187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298200587216468379862791 16947300880824702569794187)
            ·
              refine ⟨25420951321237053854691281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16947300880824702569794187 25420951321237053854691281)
              ·
                refine ⟨19065713490927790391018461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25420951321237053854691281 19065713490927790391018461)
                ·
                  refine ⟨7149642559097921396631923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19065713490927790391018461 7149642559097921396631923)
                  ·
                    refine ⟨10724463838646882094947885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149642559097921396631923 10724463838646882094947885)
                    ·
                      refine ⟨4021673939492580785605457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724463838646882094947885 4021673939492580785605457)
                      ·
                        rfl

theorem cell23_7832182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_7832182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832182 prefixEnd_7832182 := by exact prefixLift 7832182
  have htrace : WordTrace (prefixWord ++ tailWord_7832182) baseStart_7832182 baseEnd_7832182 := by
    simpa [prefixWord, tailWord_7832182, baseEnd_7832182] using wordTrace_append hprefix tailTrace_7832182
  have hstable : (prefixWord ++ tailWord_7832182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832182).length < 2 ^ (prefixWord ++ tailWord_7832182).sum := by decide
  have hdescent : baseEnd_7832182 < baseStart_7832182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832202 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_7832202 : Nat := 118140960795 + 7832202 * 2 ^ 59
def prefixEnd_7832202 : Nat := 4983230072969 + 3 ^ 40 * 7832202 * 2
def baseEnd_7832202 : Nat := 1340561403035223569118455

theorem tailTrace_7832202 : CollatzResearch.WordTrace tailWord_7832202 prefixEnd_7832202 1340561403035223569118455 := by
  unfold tailWord_7832202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415968792819315613064715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190442583447518174968172573 71415968792819315613064715)
  ·
    refine ⟨107123953189228973419597073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71415968792819315613064715 107123953189228973419597073)
    ·
      refine ⟨80342964891921730064697805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107123953189228973419597073 80342964891921730064697805)
      ·
        refine ⟨30128611834470648774261677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80342964891921730064697805 30128611834470648774261677)
        ·
          refine ⟨11298229437926493290348129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30128611834470648774261677 11298229437926493290348129)
          ·
            refine ⟨8473672078444869967761097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298229437926493290348129 8473672078444869967761097)
            ·
              refine ⟨6355254058833652475820823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473672078444869967761097 6355254058833652475820823)
              ·
                refine ⟨9532881088250478713731235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355254058833652475820823 9532881088250478713731235)
                ·
                  refine ⟨14299321632375718070596853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9532881088250478713731235 14299321632375718070596853)
                  ·
                    refine ⟨1340561403035223569118455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14299321632375718070596853 1340561403035223569118455)
                    ·
                      rfl

theorem cell23_7832202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_7832202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832202 prefixEnd_7832202 := by exact prefixLift 7832202
  have htrace : WordTrace (prefixWord ++ tailWord_7832202) baseStart_7832202 baseEnd_7832202 := by
    simpa [prefixWord, tailWord_7832202, baseEnd_7832202] using wordTrace_append hprefix tailTrace_7832202
  have hstable : (prefixWord ++ tailWord_7832202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832202).length < 2 ^ (prefixWord ++ tailWord_7832202).sum := by decide
  have hdescent : baseEnd_7832202 < baseStart_7832202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832245 : List Nat := [1, 3, 3, 3, 1, 3, 2, 7]
def baseStart_7832245 : Nat := 118140960795 + 7832245 * 2 ^ 59
def prefixEnd_7832245 : Nat := 4983230072969 + 3 ^ 40 * 7832245 * 2
def baseEnd_7832245 : Nat := 148952084769400519967321

theorem tailTrace_7832245 : CollatzResearch.WordTrace tailWord_7832245 prefixEnd_7832245 148952084769400519967321 := by
  unfold tailWord_7832245
  simp only [CollatzResearch.WordTrace]
  refine ⟨285665443510121480796074189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190443629006747653864049459 285665443510121480796074189)
  ·
    refine ⟨107124541316295555298527821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285665443510121480796074189 107124541316295555298527821)
    ·
      refine ⟨40171702993610833236947933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107124541316295555298527821 40171702993610833236947933)
      ·
        refine ⟨15064388622604062463855475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40171702993610833236947933 15064388622604062463855475)
        ·
          refine ⟨22596582933906093695783213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064388622604062463855475 22596582933906093695783213)
          ·
            refine ⟨8473718600214785135918705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22596582933906093695783213 8473718600214785135918705)
            ·
              refine ⟨6355288950161088851939029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473718600214785135918705 6355288950161088851939029)
              ·
                refine ⟨148952084769400519967321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6355288950161088851939029 148952084769400519967321)
                ·
                  rfl

theorem cell23_7832245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 7].length) (baseStart_7832245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832245 prefixEnd_7832245 := by exact prefixLift 7832245
  have htrace : WordTrace (prefixWord ++ tailWord_7832245) baseStart_7832245 baseEnd_7832245 := by
    simpa [prefixWord, tailWord_7832245, baseEnd_7832245] using wordTrace_append hprefix tailTrace_7832245
  have hstable : (prefixWord ++ tailWord_7832245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832245).length < 2 ^ (prefixWord ++ tailWord_7832245).sum := by decide
  have hdescent : baseEnd_7832245 < baseStart_7832245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832262 : List Nat := [6, 1, 2, 1, 2, 2, 9]
def baseStart_7832262 : Nat := 118140960795 + 7832262 * 2 ^ 59
def prefixEnd_7832262 : Nat := 4983230072969 + 3 ^ 40 * 7832262 * 2
def baseEnd_7832262 : Nat := 49650802690678277439569

theorem tailTrace_7832262 : CollatzResearch.WordTrace tailWord_7832262 prefixEnd_7832262 49650802690678277439569 := by
  unfold tailWord_7832262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927064485970621646857595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190444042367373261799628693 8927064485970621646857595)
  ·
    refine ⟨13390596728955932470286393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8927064485970621646857595 13390596728955932470286393)
    ·
      refine ⟨10042947546716949352714795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13390596728955932470286393 10042947546716949352714795)
      ·
        refine ⟨15064421320075424029072193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10042947546716949352714795 15064421320075424029072193)
        ·
          refine ⟨11298315990056568021804145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15064421320075424029072193 11298315990056568021804145)
          ·
            refine ⟨8473736992542426016353109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298315990056568021804145 8473736992542426016353109)
            ·
              refine ⟨49650802690678277439569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8473736992542426016353109 49650802690678277439569)
              ·
                rfl

theorem cell23_7832262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 9].length) (baseStart_7832262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832262 prefixEnd_7832262 := by exact prefixLift 7832262
  have htrace : WordTrace (prefixWord ++ tailWord_7832262) baseStart_7832262 baseEnd_7832262 := by
    simpa [prefixWord, tailWord_7832262, baseEnd_7832262] using wordTrace_append hprefix tailTrace_7832262
  have hstable : (prefixWord ++ tailWord_7832262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832262).length < 2 ^ (prefixWord ++ tailWord_7832262).sum := by decide
  have hdescent : baseEnd_7832262 < baseStart_7832262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832281 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_7832281 : Nat := 118140960795 + 7832281 * 2 ^ 59
def prefixEnd_7832281 : Nat := 4983230072969 + 3 ^ 40 * 7832281 * 2
def baseEnd_7832281 : Nat := 4021724774077375898267501

theorem tailTrace_7832281 : CollatzResearch.WordTrace tailWord_7832281 prefixEnd_7832281 4021724774077375898267501 := by
  unfold tailWord_7832281
  simp only [CollatzResearch.WordTrace]
  refine ⟨285666756537991058944384697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190444504358660705962923131 285666756537991058944384697)
  ·
    refine ⟨214250067403493294208288523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285666756537991058944384697 214250067403493294208288523)
    ·
      refine ⟨321375101105239941312432785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214250067403493294208288523 321375101105239941312432785)
      ·
        refine ⟨241031325828929955984324589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321375101105239941312432785 241031325828929955984324589)
        ·
          refine ⟨90386747185848733494121721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241031325828929955984324589 90386747185848733494121721)
          ·
            refine ⟨67790060389386550120591291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90386747185848733494121721 67790060389386550120591291)
            ·
              refine ⟨101685090584079825180886937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67790060389386550120591291 101685090584079825180886937)
              ·
                refine ⟨76263817938059868885665203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101685090584079825180886937 76263817938059868885665203)
                ·
                  refine ⟨114395726907089803328497805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76263817938059868885665203 114395726907089803328497805)
                  ·
                    refine ⟨42898397590158676248186677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114395726907089803328497805 42898397590158676248186677)
                    ·
                      refine ⟨4021724774077375898267501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42898397590158676248186677 4021724774077375898267501)
                      ·
                        rfl

theorem cell23_7832281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_7832281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832281 prefixEnd_7832281 := by exact prefixLift 7832281
  have htrace : WordTrace (prefixWord ++ tailWord_7832281) baseStart_7832281 baseEnd_7832281 := by
    simpa [prefixWord, tailWord_7832281, baseEnd_7832281] using wordTrace_append hprefix tailTrace_7832281
  have hstable : (prefixWord ++ tailWord_7832281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832281).length < 2 ^ (prefixWord ++ tailWord_7832281).sum := by decide
  have hdescent : baseEnd_7832281 < baseStart_7832281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832289 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_7832289 : Nat := 118140960795 + 7832289 * 2 ^ 59
def prefixEnd_7832289 : Nat := 4983230072969 + 3 ^ 40 * 7832289 * 2
def baseEnd_7832289 : Nat := 4021728881922611866967465

theorem tailTrace_7832289 : CollatzResearch.WordTrace tailWord_7832289 prefixEnd_7832289 4021728881922611866967465 := by
  unfold tailWord_7832289
  simp only [CollatzResearch.WordTrace]
  refine ⟨285667048321962076310675921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190444698881308050873783947 285667048321962076310675921)
  ·
    refine ⟨214250286241471557233006941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285667048321962076310675921 214250286241471557233006941)
    ·
      refine ⟨80343857340551833962377603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214250286241471557233006941 80343857340551833962377603)
      ·
        refine ⟨120515786010827750943566405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80343857340551833962377603 120515786010827750943566405)
        ·
          refine ⟨22596709877030203301918701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120515786010827750943566405 22596709877030203301918701)
          ·
            refine ⟨8473766203886326238219513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22596709877030203301918701 8473766203886326238219513)
            ·
              refine ⟨6355324652914744678664635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473766203886326238219513 6355324652914744678664635)
              ·
                refine ⟨9532986979372117017996953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355324652914744678664635 9532986979372117017996953)
                ·
                  refine ⟨7149740234529087763497715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9532986979372117017996953 7149740234529087763497715)
                  ·
                    refine ⟨10724610351793631645246573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149740234529087763497715 10724610351793631645246573)
                    ·
                      refine ⟨4021728881922611866967465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724610351793631645246573 4021728881922611866967465)
                      ·
                        rfl

theorem cell23_7832289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_7832289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832289 prefixEnd_7832289 := by exact prefixLift 7832289
  have htrace : WordTrace (prefixWord ++ tailWord_7832289) baseStart_7832289 baseEnd_7832289 := by
    simpa [prefixWord, tailWord_7832289, baseEnd_7832289] using wordTrace_append hprefix tailTrace_7832289
  have hstable : (prefixWord ++ tailWord_7832289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832289).length < 2 ^ (prefixWord ++ tailWord_7832289).sum := by decide
  have hdescent : baseEnd_7832289 < baseStart_7832289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832331 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 7]
def baseStart_7832331 : Nat := 118140960795 + 7832331 * 2 ^ 59
def prefixEnd_7832331 : Nat := 4983230072969 + 3 ^ 40 * 7832331 * 2
def baseEnd_7832331 : Nat := 1340583482703366900880757

theorem tailTrace_7832331 : CollatzResearch.WordTrace tailWord_7832331 prefixEnd_7832331 1340583482703366900880757 := by
  unfold tailWord_7832331
  simp only [CollatzResearch.WordTrace]
  refine ⟨285668580187809917483704847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190445720125206611655803231 285668580187809917483704847)
  ·
    refine ⟨428502870281714876225557271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285668580187809917483704847 428502870281714876225557271)
    ·
      refine ⟨642754305422572314338335907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428502870281714876225557271 642754305422572314338335907)
      ·
        refine ⟨964131458133858471507503861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642754305422572314338335907 964131458133858471507503861)
        ·
          refine ⟨90387324200049231703828487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 964131458133858471507503861 90387324200049231703828487)
          ·
            refine ⟨135580986300073847555742731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90387324200049231703828487 135580986300073847555742731)
            ·
              refine ⟨203371479450110771333614097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135580986300073847555742731 203371479450110771333614097)
              ·
                refine ⟨152528609587583078500210573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203371479450110771333614097 152528609587583078500210573)
                ·
                  refine ⟨57198228595343654437578965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152528609587583078500210573 57198228595343654437578965)
                  ·
                    refine ⟨1340583482703366900880757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57198228595343654437578965 1340583482703366900880757)
                    ·
                      rfl

theorem cell23_7832331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_7832331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832331 prefixEnd_7832331 := by exact prefixLift 7832331
  have htrace : WordTrace (prefixWord ++ tailWord_7832331) baseStart_7832331 baseEnd_7832331 := by
    simpa [prefixWord, tailWord_7832331, baseEnd_7832331] using wordTrace_append hprefix tailTrace_7832331
  have hstable : (prefixWord ++ tailWord_7832331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832331).length < 2 ^ (prefixWord ++ tailWord_7832331).sum := by decide
  have hdescent : baseEnd_7832331 < baseStart_7832331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832361 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_7832361 : Nat := 118140960795 + 7832361 * 2 ^ 59
def prefixEnd_7832361 : Nat := 4983230072969 + 3 ^ 40 * 7832361 * 2
def baseEnd_7832361 : Nat := 1340588617509911861755711

theorem tailTrace_7832361 : CollatzResearch.WordTrace tailWord_7832361 prefixEnd_7832361 1340588617509911861755711 := by
  unfold tailWord_7832361
  simp only [CollatzResearch.WordTrace]
  refine ⟨285669674377701232607296937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190446449585134155071531291 285669674377701232607296937)
  ·
    refine ⟨214252255783275924455472703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285669674377701232607296937 214252255783275924455472703)
    ·
      refine ⟨321378383674913886683209055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214252255783275924455472703 321378383674913886683209055)
      ·
        refine ⟨482067575512370830024813583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321378383674913886683209055 482067575512370830024813583)
        ·
          refine ⟨723101363268556245037220375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482067575512370830024813583 723101363268556245037220375)
          ·
            refine ⟨1084652044902834367555830563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723101363268556245037220375 1084652044902834367555830563)
            ·
              refine ⟨1626978067354251551333745845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084652044902834367555830563 1626978067354251551333745845)
              ·
                refine ⟨152529193814461082937538673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1626978067354251551333745845 152529193814461082937538673)
                ·
                  refine ⟨114396895360845812203154005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152529193814461082937538673 114396895360845812203154005)
                  ·
                    refine ⟨1340588617509911861755711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114396895360845812203154005 1340588617509911861755711)
                    ·
                      rfl

theorem cell23_7832361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_7832361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832361 prefixEnd_7832361 := by exact prefixLift 7832361
  have htrace : WordTrace (prefixWord ++ tailWord_7832361) baseStart_7832361 baseEnd_7832361 := by
    simpa [prefixWord, tailWord_7832361, baseEnd_7832361] using wordTrace_append hprefix tailTrace_7832361
  have hstable : (prefixWord ++ tailWord_7832361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832361).length < 2 ^ (prefixWord ++ tailWord_7832361).sum := by decide
  have hdescent : baseEnd_7832361 < baseStart_7832361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832408 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 6]
def baseStart_7832408 : Nat := 118140960795 + 7832408 * 2 ^ 59
def prefixEnd_7832408 : Nat := 4983230072969 + 3 ^ 40 * 7832408 * 2
def baseEnd_7832408 : Nat := 446865554013388544597713

theorem tailTrace_7832408 : CollatzResearch.WordTrace tailWord_7832408 prefixEnd_7832408 446865554013388544597713 := by
  unfold tailWord_7832408
  simp only [CollatzResearch.WordTrace]
  refine ⟨142835694304265479817128939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190447592405687306422838585 142835694304265479817128939)
  ·
    refine ⟨214253541456398219725693409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142835694304265479817128939 214253541456398219725693409)
    ·
      refine ⟨160690156092298664794270057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214253541456398219725693409 160690156092298664794270057)
      ·
        refine ⟨120517617069223998595702543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160690156092298664794270057 120517617069223998595702543)
        ·
          refine ⟨180776425603835997893553815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120517617069223998595702543 180776425603835997893553815)
          ·
            refine ⟨271164638405753996840330723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180776425603835997893553815 271164638405753996840330723)
            ·
              refine ⟨406746957608630995260496085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271164638405753996840330723 406746957608630995260496085)
              ·
                refine ⟨9533131818952288951417877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406746957608630995260496085 9533131818952288951417877)
                ·
                  refine ⟨446865554013388544597713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9533131818952288951417877 446865554013388544597713)
                  ·
                    rfl

theorem cell23_7832408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_7832408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832408 prefixEnd_7832408 := by exact prefixLift 7832408
  have htrace : WordTrace (prefixWord ++ tailWord_7832408) baseStart_7832408 baseEnd_7832408 := by
    simpa [prefixWord, tailWord_7832408, baseEnd_7832408] using wordTrace_append hprefix tailTrace_7832408
  have hstable : (prefixWord ++ tailWord_7832408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832408).length < 2 ^ (prefixWord ++ tailWord_7832408).sum := by decide
  have hdescent : baseEnd_7832408 < baseStart_7832408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832412 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7832412 : Nat := 118140960795 + 7832412 * 2 ^ 59
def prefixEnd_7832412 : Nat := 4983230072969 + 3 ^ 40 * 7832412 * 2
def baseEnd_7832412 : Nat := 1340597346681038295243133

theorem tailTrace_7832412 : CollatzResearch.WordTrace tailWord_7832412 prefixEnd_7832412 1340597346681038295243133 := by
  unfold tailWord_7832412
  simp only [CollatzResearch.WordTrace]
  refine ⟨142835767250258234158701745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190447689667010978878268993 142835767250258234158701745)
  ·
    refine ⟨107126825437693675619026309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142835767250258234158701745 107126825437693675619026309)
    ·
      refine ⟨20086279769567564178567433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107126825437693675619026309 20086279769567564178567433)
      ·
        refine ⟨15064709827175673133925575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20086279769567564178567433 15064709827175673133925575)
        ·
          refine ⟨22597064740763509700888363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064709827175673133925575 22597064740763509700888363)
          ·
            refine ⟨33895597111145264551332545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22597064740763509700888363 33895597111145264551332545)
            ·
              refine ⟨25421697833358948413499409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33895597111145264551332545 25421697833358948413499409)
              ·
                refine ⟨19066273375019211310124557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25421697833358948413499409 19066273375019211310124557)
                ·
                  refine ⟨7149852515632204241296709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19066273375019211310124557 7149852515632204241296709)
                  ·
                    refine ⟨1340597346681038295243133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149852515632204241296709 1340597346681038295243133)
                    ·
                      rfl

theorem cell23_7832412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7832412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832412 prefixEnd_7832412 := by exact prefixLift 7832412
  have htrace : WordTrace (prefixWord ++ tailWord_7832412) baseStart_7832412 baseEnd_7832412 := by
    simpa [prefixWord, tailWord_7832412, baseEnd_7832412] using wordTrace_append hprefix tailTrace_7832412
  have hstable : (prefixWord ++ tailWord_7832412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832412).length < 2 ^ (prefixWord ++ tailWord_7832412).sum := by decide
  have hdescent : baseEnd_7832412 < baseStart_7832412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832435 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 3]
def baseStart_7832435 : Nat := 118140960795 + 7832435 * 2 ^ 59
def prefixEnd_7832435 : Nat := 4983230072969 + 3 ^ 40 * 7832435 * 2
def baseEnd_7832435 : Nat := 4021803850098168295741793

theorem tailTrace_7832435 : CollatzResearch.WordTrace tailWord_7832435 prefixEnd_7832435 4021803850098168295741793 := by
  unfold tailWord_7832435
  simp only [CollatzResearch.WordTrace]
  refine ⟨285672373379433143245490759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190448248919622095496993839 285672373379433143245490759)
  ·
    refine ⟨428508560069149714868236139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285672373379433143245490759 428508560069149714868236139)
    ·
      refine ⟨642762840103724572302354209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428508560069149714868236139 642762840103724572302354209)
      ·
        refine ⟨482072130077793429226765657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642762840103724572302354209 482072130077793429226765657)
        ·
          refine ⟨361554097558345071920074243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482072130077793429226765657 361554097558345071920074243)
          ·
            refine ⟨542331146337517607880111365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361554097558345071920074243 542331146337517607880111365)
            ·
              refine ⟨101687089938284551477520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542331146337517607880111365 101687089938284551477520881)
              ·
                refine ⟨76265317453713413608140661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101687089938284551477520881 76265317453713413608140661)
                ·
                  refine ⟨7149873511285632525763187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76265317453713413608140661 7149873511285632525763187)
                  ·
                    refine ⟨10724810266928448788644781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149873511285632525763187 10724810266928448788644781)
                    ·
                      refine ⟨4021803850098168295741793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724810266928448788644781 4021803850098168295741793)
                      ·
                        rfl

theorem cell23_7832435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_7832435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832435 prefixEnd_7832435 := by exact prefixLift 7832435
  have htrace : WordTrace (prefixWord ++ tailWord_7832435) baseStart_7832435 baseEnd_7832435 := by
    simpa [prefixWord, tailWord_7832435, baseEnd_7832435] using wordTrace_append hprefix tailTrace_7832435
  have hstable : (prefixWord ++ tailWord_7832435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832435).length < 2 ^ (prefixWord ++ tailWord_7832435).sum := by decide
  have hdescent : baseEnd_7832435 < baseStart_7832435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832446 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7832446 : Nat := 118140960795 + 7832446 * 2 ^ 59
def prefixEnd_7832446 : Nat := 4983230072969 + 3 ^ 40 * 7832446 * 2
def baseEnd_7832446 : Nat := 1340603166128455917568081

theorem tailTrace_7832446 : CollatzResearch.WordTrace tailWord_7832446 prefixEnd_7832446 1340603166128455917568081 := by
  unfold tailWord_7832446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35709096822799161515517649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190448516388262194749427461 35709096822799161515517649)
  ·
    refine ⟨26781822617099371136638237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35709096822799161515517649 26781822617099371136638237)
    ·
      refine ⟨10043183481412264176239339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26781822617099371136638237 10043183481412264176239339)
      ·
        refine ⟨15064775222118396264359009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043183481412264176239339 15064775222118396264359009)
        ·
          refine ⟨11298581416588797198269257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15064775222118396264359009 11298581416588797198269257)
          ·
            refine ⟨8473936062441597898701943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298581416588797198269257 8473936062441597898701943)
            ·
              refine ⟨12710904093662396848052915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473936062441597898701943 12710904093662396848052915)
              ·
                refine ⟨19066356140493595272079373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12710904093662396848052915 19066356140493595272079373)
                ·
                  refine ⟨7149883552685098227029765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19066356140493595272079373 7149883552685098227029765)
                  ·
                    refine ⟨1340603166128455917568081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149883552685098227029765 1340603166128455917568081)
                    ·
                      rfl

theorem cell23_7832446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7832446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832446 prefixEnd_7832446 := by exact prefixLift 7832446
  have htrace : WordTrace (prefixWord ++ tailWord_7832446) baseStart_7832446 baseEnd_7832446 := by
    simpa [prefixWord, tailWord_7832446, baseEnd_7832446] using wordTrace_append hprefix tailTrace_7832446
  have hstable : (prefixWord ++ tailWord_7832446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832446).length < 2 ^ (prefixWord ++ tailWord_7832446).sum := by decide
  have hdescent : baseEnd_7832446 < baseStart_7832446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832479 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 2, 3, 2]
def baseStart_7832479 : Nat := 118140960795 + 7832479 * 2 ^ 59
def prefixEnd_7832479 : Nat := 4983230072969 + 3 ^ 40 * 7832479 * 2
def baseEnd_7832479 : Nat := 4021826443246966123591591

theorem tailTrace_7832479 : CollatzResearch.WordTrace tailWord_7832479 prefixEnd_7832479 4021826443246966123591591 := by
  unfold tailWord_7832479
  simp only [CollatzResearch.WordTrace]
  refine ⟨285673978191273738760092491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190449318794182492506728327 285673978191273738760092491)
  ·
    refine ⟨428510967286910608140138737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285673978191273738760092491 428510967286910608140138737)
    ·
      refine ⟨321383225465182956105104053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428510967286910608140138737 321383225465182956105104053)
      ·
        refine ⟨30129677387360902134853505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321383225465182956105104053 30129677387360902134853505)
        ·
          refine ⟨22597258040520676601140129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30129677387360902134853505 22597258040520676601140129)
          ·
            refine ⟨16947943530390507450855097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597258040520676601140129 16947943530390507450855097)
            ·
              refine ⟨12710957647792880588141323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16947943530390507450855097 12710957647792880588141323)
              ·
                refine ⟨19066436471689320882211985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12710957647792880588141323 19066436471689320882211985)
                ·
                  refine ⟨14299827353766990661658989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19066436471689320882211985 14299827353766990661658989)
                  ·
                    refine ⟨5362435257662621498122121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14299827353766990661658989 5362435257662621498122121)
                    ·
                      refine ⟨4021826443246966123591591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362435257662621498122121 4021826443246966123591591)
                      ·
                        rfl

theorem cell23_7832479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_7832479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832479 prefixEnd_7832479 := by exact prefixLift 7832479
  have htrace : WordTrace (prefixWord ++ tailWord_7832479) baseStart_7832479 baseEnd_7832479 := by
    simpa [prefixWord, tailWord_7832479, baseEnd_7832479] using wordTrace_append hprefix tailTrace_7832479
  have hstable : (prefixWord ++ tailWord_7832479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832479).length < 2 ^ (prefixWord ++ tailWord_7832479).sum := by decide
  have hdescent : baseEnd_7832479 < baseStart_7832479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832492 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_7832492 : Nat := 118140960795 + 7832492 * 2 ^ 59
def prefixEnd_7832492 : Nat := 4983230072969 + 3 ^ 40 * 7832492 * 2
def baseEnd_7832492 : Nat := 4021833118495474572729031

theorem tailTrace_7832492 : CollatzResearch.WordTrace tailWord_7832492 prefixEnd_7832492 4021833118495474572729031 := by
  unfold tailWord_7832492
  simp only [CollatzResearch.WordTrace]
  refine ⟨142837226170113320990157865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190449634893484427986877153 142837226170113320990157865)
  ·
    refine ⟨107127919627584990742618399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142837226170113320990157865 107127919627584990742618399)
    ·
      refine ⟨160691879441377486113927599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107127919627584990742618399 160691879441377486113927599)
      ·
        refine ⟨241037819162066229170891399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160691879441377486113927599 241037819162066229170891399)
        ·
          refine ⟨361556728743099343756337099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241037819162066229170891399 361556728743099343756337099)
          ·
            refine ⟨542335093114649015634505649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361556728743099343756337099 542335093114649015634505649)
            ·
              refine ⟨406751319835986761725879237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542335093114649015634505649 406751319835986761725879237)
              ·
                refine ⟨76265872469247517823602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406751319835986761725879237 76265872469247517823602357)
                ·
                  refine ⟨7149925543991954795962721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76265872469247517823602357 7149925543991954795962721)
                  ·
                    refine ⟨5362444157993966096972041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7149925543991954795962721 5362444157993966096972041)
                    ·
                      refine ⟨4021833118495474572729031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362444157993966096972041 4021833118495474572729031)
                      ·
                        rfl

theorem cell23_7832492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_7832492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832492 prefixEnd_7832492 := by exact prefixLift 7832492
  have htrace : WordTrace (prefixWord ++ tailWord_7832492) baseStart_7832492 baseEnd_7832492 := by
    simpa [prefixWord, tailWord_7832492, baseEnd_7832492] using wordTrace_append hprefix tailTrace_7832492
  have hstable : (prefixWord ++ tailWord_7832492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832492).length < 2 ^ (prefixWord ++ tailWord_7832492).sum := by decide
  have hdescent : baseEnd_7832492 < baseStart_7832492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832528 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_7832528 : Nat := 118140960795 + 7832528 * 2 ^ 59
def prefixEnd_7832528 : Nat := 4983230072969 + 3 ^ 40 * 7832528 * 2
def baseEnd_7832528 : Nat := 1340617201266345477292955

theorem tailTrace_7832528 : CollatzResearch.WordTrace tailWord_7832528 prefixEnd_7832528 1340617201266345477292955 := by
  unfold tailWord_7832528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142837882684048110064313119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190450510245397480085750825 142837882684048110064313119)
  ·
    refine ⟨214256824026072165096469679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142837882684048110064313119 214256824026072165096469679)
    ·
      refine ⟨321385236039108247644704519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214256824026072165096469679 321385236039108247644704519)
      ·
        refine ⟨482077854058662371467056779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321385236039108247644704519 482077854058662371467056779)
        ·
          refine ⟨723116781087993557200585169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482077854058662371467056779 723116781087993557200585169)
          ·
            refine ⟨542337585815995167900438877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723116781087993557200585169 542337585815995167900438877)
            ·
              refine ⟨203376594680998187962664579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542337585815995167900438877 203376594680998187962664579)
              ·
                refine ⟨305064892021497281943996869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203376594680998187962664579 305064892021497281943996869)
                ·
                  refine ⟨57199667254030740364499413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305064892021497281943996869 57199667254030740364499413)
                  ·
                    refine ⟨1340617201266345477292955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57199667254030740364499413 1340617201266345477292955)
                    ·
                      rfl

theorem cell23_7832528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_7832528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832528 prefixEnd_7832528 := by exact prefixLift 7832528
  have htrace : WordTrace (prefixWord ++ tailWord_7832528) baseStart_7832528 baseEnd_7832528 := by
    simpa [prefixWord, tailWord_7832528, baseEnd_7832528] using wordTrace_append hprefix tailTrace_7832528
  have hstable : (prefixWord ++ tailWord_7832528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832528).length < 2 ^ (prefixWord ++ tailWord_7832528).sum := by decide
  have hdescent : baseEnd_7832528 < baseStart_7832528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832532 : List Nat := [2, 4, 1, 2, 1, 3, 3, 7]
def baseStart_7832532 : Nat := 118140960795 + 7832532 * 2 ^ 59
def prefixEnd_7832532 : Nat := 4983230072969 + 3 ^ 40 * 7832532 * 2
def baseEnd_7832532 : Nat := 148957542878579793193661

theorem tailTrace_7832532 : CollatzResearch.WordTrace tailWord_7832532 prefixEnd_7832532 148957542878579793193661 := by
  unfold tailWord_7832532
  simp only [CollatzResearch.WordTrace]
  refine ⟨142837955630040864405885925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190450607506721152541181233 142837955630040864405885925)
  ·
    refine ⟨26782116680632662076103611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142837955630040864405885925 26782116680632662076103611)
    ·
      refine ⟨40173175020948993114155417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782116680632662076103611 40173175020948993114155417)
      ·
        refine ⟨30129881265711744835616563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40173175020948993114155417 30129881265711744835616563)
        ·
          refine ⟨45194821898567617253424845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30129881265711744835616563 45194821898567617253424845)
          ·
            refine ⟨16948058211962856470034317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45194821898567617253424845 16948058211962856470034317)
            ·
              refine ⟨6355521829486071176262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16948058211962856470034317 6355521829486071176262869)
              ·
                refine ⟨148957542878579793193661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6355521829486071176262869 148957542878579793193661)
                ·
                  rfl

theorem cell23_7832532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 7].length) (baseStart_7832532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832532 prefixEnd_7832532 := by exact prefixLift 7832532
  have htrace : WordTrace (prefixWord ++ tailWord_7832532) baseStart_7832532 baseEnd_7832532 := by
    simpa [prefixWord, tailWord_7832532, baseEnd_7832532] using wordTrace_append hprefix tailTrace_7832532
  have hstable : (prefixWord ++ tailWord_7832532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832532).length < 2 ^ (prefixWord ++ tailWord_7832532).sum := by decide
  have hdescent : baseEnd_7832532 < baseStart_7832532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832543 : List Nat := [1, 1, 2, 3, 5, 1, 2, 3, 1, 2, 2]
def baseStart_7832543 : Nat := 118140960795 + 7832543 * 2 ^ 59
def prefixEnd_7832543 : Nat := 4983230072969 + 3 ^ 40 * 7832543 * 2
def baseEnd_7832543 : Nat := 4021859306008853873191297

theorem tailTrace_7832543 : CollatzResearch.WordTrace tailWord_7832543 prefixEnd_7832543 4021859306008853873191297 := by
  unfold tailWord_7832543
  simp only [CollatzResearch.WordTrace]
  refine ⟨285676312463041877690422283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190450874975361251793614855 285676312463041877690422283)
  ·
    refine ⟨428514468694562816535633425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285676312463041877690422283 428514468694562816535633425)
    ·
      refine ⟨321385851520922112401725069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428514468694562816535633425 321385851520922112401725069)
      ·
        refine ⟨120519694320345792150646901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321385851520922112401725069 120519694320345792150646901)
        ·
          refine ⟨11298721342532418014123147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120519694320345792150646901 11298721342532418014123147)
          ·
            refine ⟨16948082013798627021184721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298721342532418014123147 16948082013798627021184721)
            ·
              refine ⟨12711061510348970265888541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16948082013798627021184721 12711061510348970265888541)
              ·
                refine ⟨4766648066380863849708203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12711061510348970265888541 4766648066380863849708203)
                ·
                  refine ⟨7149972099571295774562305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766648066380863849708203 7149972099571295774562305)
                  ·
                    refine ⟨5362479074678471830921729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7149972099571295774562305 5362479074678471830921729)
                    ·
                      refine ⟨4021859306008853873191297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362479074678471830921729 4021859306008853873191297)
                      ·
                        rfl

theorem cell23_7832543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_7832543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832543 prefixEnd_7832543 := by exact prefixLift 7832543
  have htrace : WordTrace (prefixWord ++ tailWord_7832543) baseStart_7832543 baseEnd_7832543 := by
    simpa [prefixWord, tailWord_7832543, baseEnd_7832543] using wordTrace_append hprefix tailTrace_7832543
  have hstable : (prefixWord ++ tailWord_7832543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832543).length < 2 ^ (prefixWord ++ tailWord_7832543).sum := by decide
  have hdescent : baseEnd_7832543 < baseStart_7832543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832546 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7832546 : Nat := 118140960795 + 7832546 * 2 ^ 59
def prefixEnd_7832546 : Nat := 4983230072969 + 3 ^ 40 * 7832546 * 2
def baseEnd_7832546 : Nat := 4021860846450817361453783

theorem tailTrace_7832546 : CollatzResearch.WordTrace tailWord_7832546 prefixEnd_7832546 4021860846450817361453783 := by
  unfold tailWord_7832546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71419105470507752300695373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190450947921354006135187661 71419105470507752300695373)
  ·
    refine ⟨26782164551440407112760765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71419105470507752300695373 26782164551440407112760765)
    ·
      refine ⟨10043311706790152667285287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26782164551440407112760765 10043311706790152667285287)
      ·
        refine ⟨15064967560185229000927931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043311706790152667285287 15064967560185229000927931)
        ·
          refine ⟨22597451340277843501391897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15064967560185229000927931 22597451340277843501391897)
          ·
            refine ⟨16948088505208382626043923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597451340277843501391897 16948088505208382626043923)
            ·
              refine ⟨25422132757812573939065885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948088505208382626043923 25422132757812573939065885)
              ·
                refine ⟨9533299784179715227149707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25422132757812573939065885 9533299784179715227149707)
                ·
                  refine ⟨14299949676269572840724561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533299784179715227149707 14299949676269572840724561)
                  ·
                    refine ⟨10724962257202179630543421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14299949676269572840724561 10724962257202179630543421)
                    ·
                      refine ⟨4021860846450817361453783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724962257202179630543421 4021860846450817361453783)
                      ·
                        rfl

theorem cell23_7832546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7832546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832546 prefixEnd_7832546 := by exact prefixLift 7832546
  have htrace : WordTrace (prefixWord ++ tailWord_7832546) baseStart_7832546 baseEnd_7832546 := by
    simpa [prefixWord, tailWord_7832546, baseEnd_7832546] using wordTrace_append hprefix tailTrace_7832546
  have hstable : (prefixWord ++ tailWord_7832546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832546).length < 2 ^ (prefixWord ++ tailWord_7832546).sum := by decide
  have hdescent : baseEnd_7832546 < baseStart_7832546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832559 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_7832559 : Nat := 118140960795 + 7832559 * 2 ^ 59
def prefixEnd_7832559 : Nat := 4983230072969 + 3 ^ 40 * 7832559 * 2
def baseEnd_7832559 : Nat := 4021867521699325810591223

theorem tailTrace_7832559 : CollatzResearch.WordTrace tailWord_7832559 prefixEnd_7832559 4021867521699325810591223 := by
  unfold tailWord_7832559
  simp only [CollatzResearch.WordTrace]
  refine ⟨285676896030983912423004731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190451264020655941615336487 285676896030983912423004731)
  ·
    refine ⟨428515344046475868634507097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285676896030983912423004731 428515344046475868634507097)
    ·
      refine ⟨321386508034856901475880323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428515344046475868634507097 321386508034856901475880323)
      ·
        refine ⟨482079762052285352213820485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321386508034856901475880323 482079762052285352213820485)
        ·
          refine ⟨90389955384803503540091341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482079762052285352213820485 90389955384803503540091341)
          ·
            refine ⟨33896233269301313827534253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90389955384803503540091341 33896233269301313827534253)
            ·
              refine ⟨12711087475987992685325345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33896233269301313827534253 12711087475987992685325345)
              ·
                refine ⟨9533315606990994513994009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711087475987992685325345 9533315606990994513994009)
                ·
                  refine ⟨7149986705243245885495507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9533315606990994513994009 7149986705243245885495507)
                  ·
                    refine ⟨10724980057864868828243261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7149986705243245885495507 10724980057864868828243261)
                    ·
                      refine ⟨4021867521699325810591223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10724980057864868828243261 4021867521699325810591223)
                      ·
                        rfl

theorem cell23_7832559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_7832559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832559 prefixEnd_7832559 := by exact prefixLift 7832559
  have htrace : WordTrace (prefixWord ++ tailWord_7832559) baseStart_7832559 baseEnd_7832559 := by
    simpa [prefixWord, tailWord_7832559, baseEnd_7832559] using wordTrace_append hprefix tailTrace_7832559
  have hstable : (prefixWord ++ tailWord_7832559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832559).length < 2 ^ (prefixWord ++ tailWord_7832559).sum := by decide
  have hdescent : baseEnd_7832559 < baseStart_7832559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832585 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_7832585 : Nat := 118140960795 + 7832585 * 2 ^ 59
def prefixEnd_7832585 : Nat := 4983230072969 + 3 ^ 40 * 7832585 * 2
def baseEnd_7832585 : Nat := 4021880872196342708866103

theorem tailTrace_7832585 : CollatzResearch.WordTrace tailWord_7832585 prefixEnd_7832585 4021880872196342708866103 := by
  unfold tailWord_7832585
  simp only [CollatzResearch.WordTrace]
  refine ⟨285677844328889718863451209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190451896219259812575634139 285677844328889718863451209)
  ·
    refine ⟨214258383246667289147588407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285677844328889718863451209 214258383246667289147588407)
    ·
      refine ⟨321387574870000933721382611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214258383246667289147588407 321387574870000933721382611)
      ·
        refine ⟨482081362305001400582073917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321387574870000933721382611 482081362305001400582073917)
        ·
          refine ⟨180780510864375525218277719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482081362305001400582073917 180780510864375525218277719)
          ·
            refine ⟨271170766296563287827416579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180780510864375525218277719 271170766296563287827416579)
            ·
              refine ⟨406756149444844931741124869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271170766296563287827416579 406756149444844931741124869)
              ·
                refine ⟨76266778020908424701460913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406756149444844931741124869 76266778020908424701460913)
                ·
                  refine ⟨57200083515681318526095685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76266778020908424701460913 57200083515681318526095685)
                  ·
                    refine ⟨10725015659190247223642941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57200083515681318526095685 10725015659190247223642941)
                    ·
                      refine ⟨4021880872196342708866103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725015659190247223642941 4021880872196342708866103)
                      ·
                        rfl

theorem cell23_7832585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_7832585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832585 prefixEnd_7832585 := by exact prefixLift 7832585
  have htrace : WordTrace (prefixWord ++ tailWord_7832585) baseStart_7832585 baseEnd_7832585 := by
    simpa [prefixWord, tailWord_7832585, baseEnd_7832585] using wordTrace_append hprefix tailTrace_7832585
  have hstable : (prefixWord ++ tailWord_7832585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832585).length < 2 ^ (prefixWord ++ tailWord_7832585).sum := by decide
  have hdescent : baseEnd_7832585 < baseStart_7832585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832586 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_7832586 : Nat := 118140960795 + 7832586 * 2 ^ 59
def prefixEnd_7832586 : Nat := 4983230072969 + 3 ^ 40 * 7832586 * 2
def baseEnd_7832586 : Nat := 4021881385676997204953599

theorem tailTrace_7832586 : CollatzResearch.WordTrace tailWord_7832586 prefixEnd_7832586 4021881385676997204953599 := by
  unfold tailWord_7832586
  simp only [CollatzResearch.WordTrace]
  refine ⟨71419470200471524008559403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190451920534590730689491741 71419470200471524008559403)
  ·
    refine ⟨107129205300707286012839105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71419470200471524008559403 107129205300707286012839105)
    ·
      refine ⟨80346903975530464509629329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107129205300707286012839105 80346903975530464509629329)
      ·
        refine ⟨60260177981647848382221997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80346903975530464509629329 60260177981647848382221997)
        ·
          refine ⟨22597566743117943143333249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60260177981647848382221997 22597566743117943143333249)
          ·
            refine ⟨16948175057338457357499937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22597566743117943143333249 16948175057338457357499937)
            ·
              refine ⟨12711131293003843018124953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16948175057338457357499937 12711131293003843018124953)
              ·
                refine ⟨9533348469752882263593715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711131293003843018124953 9533348469752882263593715)
                ·
                  refine ⟨14300022704629323395390573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533348469752882263593715 14300022704629323395390573)
                  ·
                    refine ⟨5362508514235996273271465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14300022704629323395390573 5362508514235996273271465)
                    ·
                      refine ⟨4021881385676997204953599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362508514235996273271465 4021881385676997204953599)
                      ·
                        rfl

theorem cell23_7832586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_7832586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832586 prefixEnd_7832586 := by exact prefixLift 7832586
  have htrace : WordTrace (prefixWord ++ tailWord_7832586) baseStart_7832586 baseEnd_7832586 := by
    simpa [prefixWord, tailWord_7832586, baseEnd_7832586] using wordTrace_append hprefix tailTrace_7832586
  have hstable : (prefixWord ++ tailWord_7832586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832586).length < 2 ^ (prefixWord ++ tailWord_7832586).sum := by decide
  have hdescent : baseEnd_7832586 < baseStart_7832586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832594 : List Nat := [3, 2, 5, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7832594 : Nat := 118140960795 + 7832594 * 2 ^ 59
def prefixEnd_7832594 : Nat := 4983230072969 + 3 ^ 40 * 7832594 * 2
def baseEnd_7832594 : Nat := 4021885493522233173653563

theorem tailTrace_7832594 : CollatzResearch.WordTrace tailWord_7832594 prefixEnd_7832594 4021885493522233173653563 := by
  unfold tailWord_7832594
  simp only [CollatzResearch.WordTrace]
  refine ⟨71419543146464278350132209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190452115057238075600352557 71419543146464278350132209)
  ·
    refine ⟨53564657359848208762599157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71419543146464278350132209 53564657359848208762599157)
    ·
      refine ⟨5021686627485769571493671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53564657359848208762599157 5021686627485769571493671)
      ·
        refine ⟨7532529941228654357240507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021686627485769571493671 7532529941228654357240507)
        ·
          refine ⟨11298794911842981535860761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532529941228654357240507 11298794911842981535860761)
          ·
            refine ⟨8474096183882236151895571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298794911842981535860761 8474096183882236151895571)
            ·
              refine ⟨12711144275823354227843357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474096183882236151895571 12711144275823354227843357)
              ·
                refine ⟨4766679103433757835441259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12711144275823354227843357 4766679103433757835441259)
                ·
                  refine ⟨7150018655150636753161889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766679103433757835441259 7150018655150636753161889)
                  ·
                    refine ⟨5362513991362977564871417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150018655150636753161889 5362513991362977564871417)
                    ·
                      refine ⟨4021885493522233173653563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362513991362977564871417 4021885493522233173653563)
                      ·
                        rfl

theorem cell23_7832594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7832594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832594 prefixEnd_7832594 := by exact prefixLift 7832594
  have htrace : WordTrace (prefixWord ++ tailWord_7832594) baseStart_7832594 baseEnd_7832594 := by
    simpa [prefixWord, tailWord_7832594, baseEnd_7832594] using wordTrace_append hprefix tailTrace_7832594
  have hstable : (prefixWord ++ tailWord_7832594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832594).length < 2 ^ (prefixWord ++ tailWord_7832594).sum := by decide
  have hdescent : baseEnd_7832594 < baseStart_7832594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832633 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7832633 : Nat := 118140960795 + 7832633 * 2 ^ 59
def prefixEnd_7832633 : Nat := 4983230072969 + 3 ^ 40 * 7832633 * 2
def baseEnd_7832633 : Nat := 4021905519267758521065883

theorem tailTrace_7832633 : CollatzResearch.WordTrace tailWord_7832633 prefixEnd_7832633 4021905519267758521065883 := by
  unfold tailWord_7832633
  simp only [CollatzResearch.WordTrace]
  refine ⟨285679595032715823061198553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190453063355143882040799035 285679595032715823061198553)
  ·
    refine ⟨214259696274536867295898915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285679595032715823061198553 214259696274536867295898915)
    ·
      refine ⟨321389544411805300943848373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214259696274536867295898915 321389544411805300943848373)
      ·
        refine ⟨30130269788606746963485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321389544411805300943848373 30130269788606746963485785)
        ·
          refine ⟨22597702341455060222614339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30130269788606746963485785 22597702341455060222614339)
          ·
            refine ⟨33896553512182590333921509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22597702341455060222614339 33896553512182590333921509)
            ·
              refine ⟨6355603783534235687610283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33896553512182590333921509 6355603783534235687610283)
              ·
                refine ⟨9533405675301353531415425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355603783534235687610283 9533405675301353531415425)
                ·
                  refine ⟨7150054256476015148561569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9533405675301353531415425 7150054256476015148561569)
                  ·
                    refine ⟨5362540692357011361421177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150054256476015148561569 5362540692357011361421177)
                    ·
                      refine ⟨4021905519267758521065883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362540692357011361421177 4021905519267758521065883)
                      ·
                        rfl

theorem cell23_7832633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7832633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832633 prefixEnd_7832633 := by exact prefixLift 7832633
  have htrace : WordTrace (prefixWord ++ tailWord_7832633) baseStart_7832633 baseEnd_7832633 := by
    simpa [prefixWord, tailWord_7832633, baseEnd_7832633] using wordTrace_append hprefix tailTrace_7832633
  have hstable : (prefixWord ++ tailWord_7832633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832633).length < 2 ^ (prefixWord ++ tailWord_7832633).sum := by decide
  have hdescent : baseEnd_7832633 < baseStart_7832633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832672 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_7832672 : Nat := 118140960795 + 7832672 * 2 ^ 59
def prefixEnd_7832672 : Nat := 4983230072969 + 3 ^ 40 * 7832672 * 2
def baseEnd_7832672 : Nat := 4021925545013283868478203

theorem tailTrace_7832672 : CollatzResearch.WordTrace tailWord_7832672 prefixEnd_7832672 4021925545013283868478203 := by
  unfold tailWord_7832672
  simp only [CollatzResearch.WordTrace]
  refine ⟨142840508739787266360934135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190454011653049688481245513 142840508739787266360934135)
  ·
    refine ⟨214260763109680899541401203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142840508739787266360934135 214260763109680899541401203)
    ·
      refine ⟨321391144664521349312101805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214260763109680899541401203 321391144664521349312101805)
      ·
        refine ⟨120521679249195505992038177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321391144664521349312101805 120521679249195505992038177)
        ·
          refine ⟨90391259436896629494028633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120521679249195505992038177 90391259436896629494028633)
          ·
            refine ⟨67793444577672472120521475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90391259436896629494028633 67793444577672472120521475)
            ·
              refine ⟨101690166866508708180782213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67793444577672472120521475 101690166866508708180782213)
              ·
                refine ⟨19066906287470382783896665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101690166866508708180782213 19066906287470382783896665)
                ·
                  refine ⟨14300179715602787087922499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19066906287470382783896665 14300179715602787087922499)
                  ·
                    refine ⟨21450269573404180631883749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14300179715602787087922499 21450269573404180631883749)
                    ·
                      refine ⟨4021925545013283868478203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21450269573404180631883749 4021925545013283868478203)
                      ·
                        rfl

theorem cell23_7832672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_7832672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832672 prefixEnd_7832672 := by exact prefixLift 7832672
  have htrace : WordTrace (prefixWord ++ tailWord_7832672) baseStart_7832672 baseEnd_7832672 := by
    simpa [prefixWord, tailWord_7832672, baseEnd_7832672] using wordTrace_append hprefix tailTrace_7832672
  have hstable : (prefixWord ++ tailWord_7832672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832672).length < 2 ^ (prefixWord ++ tailWord_7832672).sum := by decide
  have hdescent : baseEnd_7832672 < baseStart_7832672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832675 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7832675 : Nat := 118140960795 + 7832675 * 2 ^ 59
def prefixEnd_7832675 : Nat := 4983230072969 + 3 ^ 40 * 7832675 * 2
def baseEnd_7832675 : Nat := 4021927085455247356740689

theorem tailTrace_7832675 : CollatzResearch.WordTrace tailWord_7832675 prefixEnd_7832675 4021927085455247356740689 := by
  unfold tailWord_7832675
  simp only [CollatzResearch.WordTrace]
  refine ⟨285681126898563664234227479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190454084599042442822818319 285681126898563664234227479)
  ·
    refine ⟨428521690347845496351341219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285681126898563664234227479 428521690347845496351341219)
    ·
      refine ⟨642782535521768244527011829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428521690347845496351341219 642782535521768244527011829)
      ·
        refine ⟨60260862705165772924407359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 642782535521768244527011829 60260862705165772924407359)
        ·
          refine ⟨90391294057748659386611039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60260862705165772924407359 90391294057748659386611039)
          ·
            refine ⟨135586941086622989079916559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90391294057748659386611039 135586941086622989079916559)
            ·
              refine ⟨203380411629934483619874839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135586941086622989079916559 203380411629934483619874839)
              ·
                refine ⟨305070617444901725429812259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203380411629934483619874839 305070617444901725429812259)
                ·
                  refine ⟨457605926167352588144718389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305070617444901725429812259 457605926167352588144718389)
                  ·
                    refine ⟨42900555578189305138567349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 457605926167352588144718389 42900555578189305138567349)
                    ·
                      refine ⟨4021927085455247356740689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42900555578189305138567349 4021927085455247356740689)
                      ·
                        rfl

theorem cell23_7832675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7832675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832675 prefixEnd_7832675 := by exact prefixLift 7832675
  have htrace : WordTrace (prefixWord ++ tailWord_7832675) baseStart_7832675 baseEnd_7832675 := by
    simpa [prefixWord, tailWord_7832675, baseEnd_7832675] using wordTrace_append hprefix tailTrace_7832675
  have hstable : (prefixWord ++ tailWord_7832675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832675).length < 2 ^ (prefixWord ++ tailWord_7832675).sum := by decide
  have hdescent : baseEnd_7832675 < baseStart_7832675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832709 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_7832709 : Nat := 118140960795 + 7832709 * 2 ^ 59
def prefixEnd_7832709 : Nat := 4983230072969 + 3 ^ 40 * 7832709 * 2
def baseEnd_7832709 : Nat := 4021944543797500223715533

theorem tailTrace_7832709 : CollatzResearch.WordTrace tailWord_7832709 prefixEnd_7832709 4021944543797500223715533 := by
  unfold tailWord_7832709
  simp only [CollatzResearch.WordTrace]
  refine ⟨285682366980440488040965181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190454911320293658693976787 285682366980440488040965181)
  ·
    refine ⟨107130887617665183015361943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285682366980440488040965181 107130887617665183015361943)
    ·
      refine ⟨160696331426497774523042915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107130887617665183015361943 160696331426497774523042915)
      ·
        refine ⟨241044497139746661784564373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160696331426497774523042915 241044497139746661784564373)
        ·
          refine ⟨11298960803425624771151455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241044497139746661784564373 11298960803425624771151455)
          ·
            refine ⟨16948441205138437156727183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298960803425624771151455 16948441205138437156727183)
            ·
              refine ⟨25422661807707655735090775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948441205138437156727183 25422661807707655735090775)
              ·
                refine ⟨38133992711561483602636163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25422661807707655735090775 38133992711561483602636163)
                ·
                  refine ⟨57200989067342225403954245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38133992711561483602636163 57200989067342225403954245)
                  ·
                    refine ⟨10725185450126667263241421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57200989067342225403954245 10725185450126667263241421)
                    ·
                      refine ⟨4021944543797500223715533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725185450126667263241421 4021944543797500223715533)
                      ·
                        rfl

theorem cell23_7832709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_7832709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832709 prefixEnd_7832709 := by exact prefixLift 7832709
  have htrace : WordTrace (prefixWord ++ tailWord_7832709) baseStart_7832709 baseEnd_7832709 := by
    simpa [prefixWord, tailWord_7832709, baseEnd_7832709] using wordTrace_append hprefix tailTrace_7832709
  have hstable : (prefixWord ++ tailWord_7832709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832709).length < 2 ^ (prefixWord ++ tailWord_7832709).sum := by decide
  have hdescent : baseEnd_7832709 < baseStart_7832709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832715 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_7832715 : Nat := 118140960795 + 7832715 * 2 ^ 59
def prefixEnd_7832715 : Nat := 4983230072969 + 3 ^ 40 * 7832715 * 2
def baseEnd_7832715 : Nat := 4021947624681427200240505

theorem tailTrace_7832715 : CollatzResearch.WordTrace tailWord_7832715 prefixEnd_7832715 4021947624681427200240505 := by
  unfold tailWord_7832715
  simp only [CollatzResearch.WordTrace]
  refine ⟨285682585818418751065683599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190455057212279167377122399 285682585818418751065683599)
  ·
    refine ⟨428523878727628126598525399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285682585818418751065683599 428523878727628126598525399)
    ·
      refine ⟨642785818091442189897788099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428523878727628126598525399 642785818091442189897788099)
      ·
        refine ⟨964178727137163284846682149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642785818091442189897788099 964178727137163284846682149)
        ·
          refine ⟨180783511338218115908752903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 964178727137163284846682149 180783511338218115908752903)
          ·
            refine ⟨271175267007327173863129355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180783511338218115908752903 271175267007327173863129355)
            ·
              refine ⟨406762900510990760794694033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271175267007327173863129355 406762900510990760794694033)
              ·
                refine ⟨305072175383243070596020525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406762900510990760794694033 305072175383243070596020525)
                ·
                  refine ⟨114402065768716151473507697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305072175383243070596020525 114402065768716151473507697)
                  ·
                    refine ⟨85801549326537113605130773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114402065768716151473507697 85801549326537113605130773)
                    ·
                      refine ⟨4021947624681427200240505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85801549326537113605130773 4021947624681427200240505)
                      ·
                        rfl

theorem cell23_7832715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_7832715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832715 prefixEnd_7832715 := by exact prefixLift 7832715
  have htrace : WordTrace (prefixWord ++ tailWord_7832715) baseStart_7832715 baseEnd_7832715 := by
    simpa [prefixWord, tailWord_7832715, baseEnd_7832715] using wordTrace_append hprefix tailTrace_7832715
  have hstable : (prefixWord ++ tailWord_7832715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832715).length < 2 ^ (prefixWord ++ tailWord_7832715).sum := by decide
  have hdescent : baseEnd_7832715 < baseStart_7832715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832732 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7832732 : Nat := 118140960795 + 7832732 * 2 ^ 59
def prefixEnd_7832732 : Nat := 4983230072969 + 3 ^ 40 * 7832732 * 2
def baseEnd_7832732 : Nat := 4021956353852553633727927

theorem tailTrace_7832732 : CollatzResearch.WordTrace tailWord_7832732 prefixEnd_7832732 4021956353852553633727927 := by
  unfold tailWord_7832732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142841602929678581484526225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190455470572904775312701633 142841602929678581484526225)
  ·
    refine ⟨107131202197258936113394669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142841602929678581484526225 107131202197258936113394669)
    ·
      refine ⟨40174200823972101042523001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107131202197258936113394669 40174200823972101042523001)
      ·
        refine ⟨30130650617979075781892251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40174200823972101042523001 30130650617979075781892251)
        ·
          refine ⟨45195975926968613672838377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30130650617979075781892251 45195975926968613672838377)
          ·
            refine ⟨33896981945226460254628783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45195975926968613672838377 33896981945226460254628783)
            ·
              refine ⟨50845472917839690381943175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33896981945226460254628783 50845472917839690381943175)
              ·
                refine ⟨76268209376759535572914763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50845472917839690381943175 76268209376759535572914763)
                ·
                  refine ⟨114402314065139303359372145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76268209376759535572914763 114402314065139303359372145)
                  ·
                    refine ⟨85801735548854477519529109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114402314065139303359372145 85801735548854477519529109)
                    ·
                      refine ⟨4021956353852553633727927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85801735548854477519529109 4021956353852553633727927)
                      ·
                        rfl

theorem cell23_7832732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7832732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832732 prefixEnd_7832732 := by exact prefixLift 7832732
  have htrace : WordTrace (prefixWord ++ tailWord_7832732) baseStart_7832732 baseEnd_7832732 := by
    simpa [prefixWord, tailWord_7832732, baseEnd_7832732] using wordTrace_append hprefix tailTrace_7832732
  have hstable : (prefixWord ++ tailWord_7832732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832732).length < 2 ^ (prefixWord ++ tailWord_7832732).sum := by decide
  have hdescent : baseEnd_7832732 < baseStart_7832732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832745 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_7832745 : Nat := 118140960795 + 7832745 * 2 ^ 59
def prefixEnd_7832745 : Nat := 4983230072969 + 3 ^ 40 * 7832745 * 2
def baseEnd_7832745 : Nat := 4021963029101062082865367

theorem tailTrace_7832745 : CollatzResearch.WordTrace tailWord_7832745 prefixEnd_7832745 4021963029101062082865367 := by
  unfold tailWord_7832745
  simp only [CollatzResearch.WordTrace]
  refine ⟨285683680008310066189275689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190455786672206710792850459 285683680008310066189275689)
  ·
    refine ⟨214262760006232549641956767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285683680008310066189275689 214262760006232549641956767)
    ·
      refine ⟨321394140009348824462935151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214262760006232549641956767 321394140009348824462935151)
      ·
        refine ⟨482091210014023236694402727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321394140009348824462935151 482091210014023236694402727)
        ·
          refine ⟨723136815021034855041604091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482091210014023236694402727 723136815021034855041604091)
          ·
            refine ⟨1084705222531552282562406137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723136815021034855041604091 1084705222531552282562406137)
            ·
              refine ⟨813528916898664211921804603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084705222531552282562406137 813528916898664211921804603)
              ·
                refine ⟨1220293375347996317882706905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813528916898664211921804603 1220293375347996317882706905)
                ·
                  refine ⟨915220031510997238412030179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220293375347996317882706905 915220031510997238412030179)
                  ·
                    refine ⟨1372830047266495857618045269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915220031510997238412030179 1372830047266495857618045269)
                    ·
                      refine ⟨4021963029101062082865367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1372830047266495857618045269 4021963029101062082865367)
                      ·
                        rfl

theorem cell23_7832745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_7832745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832745 prefixEnd_7832745 := by exact prefixLift 7832745
  have htrace : WordTrace (prefixWord ++ tailWord_7832745) baseStart_7832745 baseEnd_7832745 := by
    simpa [prefixWord, tailWord_7832745, baseEnd_7832745] using wordTrace_append hprefix tailTrace_7832745
  have hstable : (prefixWord ++ tailWord_7832745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832745).length < 2 ^ (prefixWord ++ tailWord_7832745).sum := by decide
  have hdescent : baseEnd_7832745 < baseStart_7832745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832759 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 1, 5]
def baseStart_7832759 : Nat := 118140960795 + 7832759 * 2 ^ 59
def prefixEnd_7832759 : Nat := 4983230072969 + 3 ^ 40 * 7832759 * 2
def baseEnd_7832759 : Nat := 1340656739276741676030101

theorem tailTrace_7832759 : CollatzResearch.WordTrace tailWord_7832759 prefixEnd_7832759 1340656739276741676030101 := by
  unfold tailWord_7832759
  simp only [CollatzResearch.WordTrace]
  refine ⟨285684190630259346580285331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190456127086839564386856887 285684190630259346580285331)
  ·
    refine ⟨428526285945389019870427997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285684190630259346580285331 428526285945389019870427997)
    ·
      refine ⟨160697357229520882451410499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428526285945389019870427997 160697357229520882451410499)
      ·
        refine ⟨241046035844281323677115749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160697357229520882451410499 241046035844281323677115749)
        ·
          refine ⟨45196131720802748189459203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241046035844281323677115749 45196131720802748189459203)
          ·
            refine ⟨67794197581204122284188805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45196131720802748189459203 67794197581204122284188805)
            ·
              refine ⟨12711412046475772928285401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67794197581204122284188805 12711412046475772928285401)
              ·
                refine ⟨9533559034856829696214051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711412046475772928285401 9533559034856829696214051)
                ·
                  refine ⟨14300338552285244544321077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533559034856829696214051 14300338552285244544321077)
                  ·
                    refine ⟨1340656739276741676030101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14300338552285244544321077 1340656739276741676030101)
                    ·
                      rfl

theorem cell23_7832759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_7832759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832759 prefixEnd_7832759 := by exact prefixLift 7832759
  have htrace : WordTrace (prefixWord ++ tailWord_7832759) baseStart_7832759 baseEnd_7832759 := by
    simpa [prefixWord, tailWord_7832759, baseEnd_7832759] using wordTrace_append hprefix tailTrace_7832759
  have hstable : (prefixWord ++ tailWord_7832759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832759).length < 2 ^ (prefixWord ++ tailWord_7832759).sum := by decide
  have hdescent : baseEnd_7832759 < baseStart_7832759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832766 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_7832766 : Nat := 118140960795 + 7832766 * 2 ^ 59
def prefixEnd_7832766 : Nat := 4983230072969 + 3 ^ 40 * 7832766 * 2
def baseEnd_7832766 : Nat := 4021973812194806500702771

theorem tailTrace_7832766 : CollatzResearch.WordTrace tailWord_7832766 prefixEnd_7832766 4021973812194806500702771 := by
  unfold tailWord_7832766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710555742654248346973769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190456297294155991183860101 35710555742654248346973769)
  ·
    refine ⟨26782916806990686260230327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35710555742654248346973769 26782916806990686260230327)
    ·
      refine ⟨40174375210486029390345491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782916806990686260230327 40174375210486029390345491)
      ·
        refine ⟨60261562815729044085518237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40174375210486029390345491 60261562815729044085518237)
        ·
          refine ⟨22598086055898391532069339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60261562815729044085518237 22598086055898391532069339)
          ·
            refine ⟨33897129083847587298104009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22598086055898391532069339 33897129083847587298104009)
            ·
              refine ⟨25422846812885690473578007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33897129083847587298104009 25422846812885690473578007)
              ·
                refine ⟨38134270219328535710367011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25422846812885690473578007 38134270219328535710367011)
                ·
                  refine ⟨57201405328992803565550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38134270219328535710367011 57201405328992803565550517)
                  ·
                    refine ⟨5362631749593075334270361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57201405328992803565550517 5362631749593075334270361)
                    ·
                      refine ⟨4021973812194806500702771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362631749593075334270361 4021973812194806500702771)
                      ·
                        rfl

theorem cell23_7832766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_7832766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832766 prefixEnd_7832766 := by exact prefixLift 7832766
  have htrace : WordTrace (prefixWord ++ tailWord_7832766) baseStart_7832766 baseEnd_7832766 := by
    simpa [prefixWord, tailWord_7832766, baseEnd_7832766] using wordTrace_append hprefix tailTrace_7832766
  have hstable : (prefixWord ++ tailWord_7832766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832766).length < 2 ^ (prefixWord ++ tailWord_7832766).sum := by decide
  have hdescent : baseEnd_7832766 < baseStart_7832766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832813 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7832813 : Nat := 118140960795 + 7832813 * 2 ^ 59
def prefixEnd_7832813 : Nat := 4983230072969 + 3 ^ 40 * 7832813 * 2
def baseEnd_7832813 : Nat := 4021997945785567816815055

theorem tailTrace_7832813 : CollatzResearch.WordTrace tailWord_7832813 prefixEnd_7832813 4021997945785567816815055 := by
  unfold tailWord_7832813
  simp only [CollatzResearch.WordTrace]
  refine ⟨285686160172063713802751093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190457440114709142535167395 285686160172063713802751093)
  ·
    refine ⟨26783077516130973169007915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285686160172063713802751093 26783077516130973169007915)
    ·
      refine ⟨40174616274196459753511873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26783077516130973169007915 40174616274196459753511873)
      ·
        refine ⟨30130962205647344815133905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40174616274196459753511873 30130962205647344815133905)
        ·
          refine ⟨22598221654235508611350429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30130962205647344815133905 22598221654235508611350429)
          ·
            refine ⟨8474333120338315729256411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22598221654235508611350429 8474333120338315729256411)
            ·
              refine ⟨12711499680507473593884617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474333120338315729256411 12711499680507473593884617)
              ·
                refine ⟨9533624760380605195413463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711499680507473593884617 9533624760380605195413463)
                ·
                  refine ⟨14300437140570907793120195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533624760380605195413463 14300437140570907793120195)
                  ·
                    refine ⟨21450655710856361689680293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14300437140570907793120195 21450655710856361689680293)
                    ·
                      refine ⟨4021997945785567816815055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21450655710856361689680293 4021997945785567816815055)
                      ·
                        rfl

theorem cell23_7832813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7832813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832813 prefixEnd_7832813 := by exact prefixLift 7832813
  have htrace : WordTrace (prefixWord ++ tailWord_7832813) baseStart_7832813 baseEnd_7832813 := by
    simpa [prefixWord, tailWord_7832813, baseEnd_7832813] using wordTrace_append hprefix tailTrace_7832813
  have hstable : (prefixWord ++ tailWord_7832813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832813).length < 2 ^ (prefixWord ++ tailWord_7832813).sum := by decide
  have hdescent : baseEnd_7832813 < baseStart_7832813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832833 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_7832833 : Nat := 118140960795 + 7832833 * 2 ^ 59
def prefixEnd_7832833 : Nat := 4983230072969 + 3 ^ 40 * 7832833 * 2
def baseEnd_7832833 : Nat := 4022008215398657738564963

theorem tailTrace_7832833 : CollatzResearch.WordTrace tailWord_7832833 prefixEnd_7832833 4022008215398657738564963 := by
  unfold tailWord_7832833
  simp only [CollatzResearch.WordTrace]
  refine ⟨285686889631991257218479153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190457926421327504812319435 285686889631991257218479153)
  ·
    refine ⟨214265167223993442913859365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285686889631991257218479153 214265167223993442913859365)
    ·
      refine ⟨40174718854498770546348631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214265167223993442913859365 40174718854498770546348631)
      ·
        refine ⟨60262078281748155819522947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40174718854498770546348631 60262078281748155819522947)
        ·
          refine ⟨90393117422622233729284421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60262078281748155819522947 90393117422622233729284421)
          ·
            refine ⟨16948709516741668824240829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90393117422622233729284421 16948709516741668824240829)
            ·
              refine ⟨6355766068778125809090311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16948709516741668824240829 6355766068778125809090311)
              ·
                refine ⟨9533649103167188713635467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355766068778125809090311 9533649103167188713635467)
                ·
                  refine ⟨14300473654750783070453201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533649103167188713635467 14300473654750783070453201)
                  ·
                    refine ⟨10725355241063087302839901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14300473654750783070453201 10725355241063087302839901)
                    ·
                      refine ⟨4022008215398657738564963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725355241063087302839901 4022008215398657738564963)
                      ·
                        rfl

theorem cell23_7832833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_7832833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832833 prefixEnd_7832833 := by exact prefixLift 7832833
  have htrace : WordTrace (prefixWord ++ tailWord_7832833) baseStart_7832833 baseEnd_7832833 := by
    simpa [prefixWord, tailWord_7832833, baseEnd_7832833] using wordTrace_append hprefix tailTrace_7832833
  have hstable : (prefixWord ++ tailWord_7832833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832833).length < 2 ^ (prefixWord ++ tailWord_7832833).sum := by decide
  have hdescent : baseEnd_7832833 < baseStart_7832833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832856 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7832856 : Nat := 118140960795 + 7832856 * 2 ^ 59
def prefixEnd_7832856 : Nat := 4983230072969 + 3 ^ 40 * 7832856 * 2
def baseEnd_7832856 : Nat := 4022020025453711148577357

theorem tailTrace_7832856 : CollatzResearch.WordTrace tailWord_7832856 prefixEnd_7832856 4022020025453711148577357 := by
  unfold tailWord_7832856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142843864255453966073283211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190458485673938621431044281 142843864255453966073283211)
  ·
    refine ⟨214265796383180949109924817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142843864255453966073283211 214265796383180949109924817)
    ·
      refine ⟨160699347287385711832443613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214265796383180949109924817 160699347287385711832443613)
      ·
        refine ⟨60262255232769641937166355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160699347287385711832443613 60262255232769641937166355)
        ·
          refine ⟨90393382849154462905749533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60262255232769641937166355 90393382849154462905749533)
          ·
            refine ⟨33897518568432923589656075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90393382849154462905749533 33897518568432923589656075)
            ·
              refine ⟨50846277852649385384484113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33897518568432923589656075 50846277852649385384484113)
              ·
                refine ⟨38134708389487039038363085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50846277852649385384484113 38134708389487039038363085)
                ·
                  refine ⟨14300515646057639639386157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38134708389487039038363085 14300515646057639639386157)
                  ·
                    refine ⟨5362693367271614864769809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14300515646057639639386157 5362693367271614864769809)
                    ·
                      refine ⟨4022020025453711148577357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362693367271614864769809 4022020025453711148577357)
                      ·
                        rfl

theorem cell23_7832856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7832856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832856 prefixEnd_7832856 := by exact prefixLift 7832856
  have htrace : WordTrace (prefixWord ++ tailWord_7832856) baseStart_7832856 baseEnd_7832856 := by
    simpa [prefixWord, tailWord_7832856, baseEnd_7832856] using wordTrace_append hprefix tailTrace_7832856
  have hstable : (prefixWord ++ tailWord_7832856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832856).length < 2 ^ (prefixWord ++ tailWord_7832856).sum := by decide
  have hdescent : baseEnd_7832856 < baseStart_7832856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832903 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_7832903 : Nat := 118140960795 + 7832903 * 2 ^ 59
def prefixEnd_7832903 : Nat := 4983230072969 + 3 ^ 40 * 7832903 * 2
def baseEnd_7832903 : Nat := 4022044159044472464689641

theorem tailTrace_7832903 : CollatzResearch.WordTrace tailWord_7832903 prefixEnd_7832903 4022044159044472464689641 := by
  unfold tailWord_7832903
  simp only [CollatzResearch.WordTrace]
  refine ⟨285689442741737659173527363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190459628494491772782351575 285689442741737659173527363)
  ·
    refine ⟨428534164112606488760291045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285689442741737659173527363 428534164112606488760291045)
    ·
      refine ⟨80350155771113716642554571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428534164112606488760291045 80350155771113716642554571)
      ·
        refine ⟨120525233656670574963831857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80350155771113716642554571 120525233656670574963831857)
        ·
          refine ⟨90393925242502931222873893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120525233656670574963831857 90393925242502931222873893)
          ·
            refine ⟨16948860982969299604288855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90393925242502931222873893 16948860982969299604288855)
            ·
              refine ⟨25423291474453949406433283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948860982969299604288855 25423291474453949406433283)
              ·
                refine ⟨38134937211680924109649925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25423291474453949406433283 38134937211680924109649925)
                ·
                  refine ⟨7150300727190173270559361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38134937211680924109649925 7150300727190173270559361)
                  ·
                    refine ⟨5362725545392629952919521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150300727190173270559361 5362725545392629952919521)
                    ·
                      refine ⟨4022044159044472464689641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362725545392629952919521 4022044159044472464689641)
                      ·
                        rfl

theorem cell23_7832903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_7832903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832903 prefixEnd_7832903 := by exact prefixLift 7832903
  have htrace : WordTrace (prefixWord ++ tailWord_7832903) baseStart_7832903 baseEnd_7832903 := by
    simpa [prefixWord, tailWord_7832903, baseEnd_7832903] using wordTrace_append hprefix tailTrace_7832903
  have hstable : (prefixWord ++ tailWord_7832903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832903).length < 2 ^ (prefixWord ++ tailWord_7832903).sum := by decide
  have hdescent : baseEnd_7832903 < baseStart_7832903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832920 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_7832920 : Nat := 118140960795 + 7832920 * 2 ^ 59
def prefixEnd_7832920 : Nat := 4983230072969 + 3 ^ 40 * 7832920 * 2
def baseEnd_7832920 : Nat := 4022052888215598898177063

theorem tailTrace_7832920 : CollatzResearch.WordTrace tailWord_7832920 prefixEnd_7832920 4022052888215598898177063 := by
  unfold tailWord_7832920
  simp only [CollatzResearch.WordTrace]
  refine ⟨142845031391338035538448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190460041855117380717930809 142845031391338035538448107)
  ·
    refine ⟨214267547087007053307672161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142845031391338035538448107 214267547087007053307672161)
    ·
      refine ⟨160700660315255289980754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214267547087007053307672161 160700660315255289980754121)
      ·
        refine ⟨120525495236441467485565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160700660315255289980754121 120525495236441467485565591)
        ·
          refine ⟨180788242854662201228348387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120525495236441467485565591 180788242854662201228348387)
          ·
            refine ⟨271182364281993301842522581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180788242854662201228348387 271182364281993301842522581)
            ·
              refine ⟨6355836662859218011934123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 271182364281993301842522581 6355836662859218011934123)
              ·
                refine ⟨9533754994288827017901185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355836662859218011934123 9533754994288827017901185)
                ·
                  refine ⟨7150316245716620263425889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9533754994288827017901185 7150316245716620263425889)
                  ·
                    refine ⟨5362737184287465197569417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150316245716620263425889 5362737184287465197569417)
                    ·
                      refine ⟨4022052888215598898177063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362737184287465197569417 4022052888215598898177063)
                      ·
                        rfl

theorem cell23_7832920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_7832920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832920 prefixEnd_7832920 := by exact prefixLift 7832920
  have htrace : WordTrace (prefixWord ++ tailWord_7832920) baseStart_7832920 baseEnd_7832920 := by
    simpa [prefixWord, tailWord_7832920, baseEnd_7832920] using wordTrace_append hprefix tailTrace_7832920
  have hstable : (prefixWord ++ tailWord_7832920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832920).length < 2 ^ (prefixWord ++ tailWord_7832920).sum := by decide
  have hdescent : baseEnd_7832920 < baseStart_7832920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832986 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_7832986 : Nat := 118140960795 + 7832986 * 2 ^ 59
def prefixEnd_7832986 : Nat := 4983230072969 + 3 ^ 40 * 7832986 * 2
def baseEnd_7832986 : Nat := 1340695592646265213317253

theorem tailTrace_7832986 : CollatzResearch.WordTrace tailWord_7832986 prefixEnd_7832986 1340695592646265213317253 := by
  unfold tailWord_7832986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71423117500109241087199703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190461646666957976232532541 71423117500109241087199703)
  ·
    refine ⟨107134676250163861630799555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71423117500109241087199703 107134676250163861630799555)
    ·
      refine ⟨160702014375245792446199333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107134676250163861630799555 160702014375245792446199333)
      ·
        refine ⟨30131627695358586083662375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160702014375245792446199333 30131627695358586083662375)
        ·
          refine ⟨45197441543037879125493563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30131627695358586083662375 45197441543037879125493563)
          ·
            refine ⟨67796162314556818688240345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45197441543037879125493563 67796162314556818688240345)
            ·
              refine ⟨50847121735917614016180259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67796162314556818688240345 50847121735917614016180259)
              ·
                refine ⟨76270682603876421024270389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50847121735917614016180259 76270682603876421024270389)
                ·
                  refine ⟨7150376494113414471025349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76270682603876421024270389 7150376494113414471025349)
                  ·
                    refine ⟨1340695592646265213317253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150376494113414471025349 1340695592646265213317253)
                    ·
                      rfl

theorem cell23_7832986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_7832986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832986 prefixEnd_7832986 := by exact prefixLift 7832986
  have htrace : WordTrace (prefixWord ++ tailWord_7832986) baseStart_7832986 baseEnd_7832986 := by
    simpa [prefixWord, tailWord_7832986, baseEnd_7832986] using wordTrace_append hprefix tailTrace_7832986
  have hstable : (prefixWord ++ tailWord_7832986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832986).length < 2 ^ (prefixWord ++ tailWord_7832986).sum := by decide
  have hdescent : baseEnd_7832986 < baseStart_7832986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7832990 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7832990 : Nat := 118140960795 + 7832990 * 2 ^ 59
def prefixEnd_7832990 : Nat := 4983230072969 + 3 ^ 40 * 7832990 * 2
def baseEnd_7832990 : Nat := 1340696277287137874767247

theorem tailTrace_7832990 : CollatzResearch.WordTrace tailWord_7832990 prefixEnd_7832990 1340696277287137874767247 := by
  unfold tailWord_7832990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35711576986552809128993053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190461743928281648687962949 35711576986552809128993053)
  ·
    refine ⟨13391841369957303423372395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35711576986552809128993053 13391841369957303423372395)
    ·
      refine ⟨20087762054935955135058593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13391841369957303423372395 20087762054935955135058593)
      ·
        refine ⟨15065821541201966351293945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20087762054935955135058593 15065821541201966351293945)
        ·
          refine ⟨11299366155901474763470459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15065821541201966351293945 11299366155901474763470459)
          ·
            refine ⟨16949049233852212145205689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299366155901474763470459 16949049233852212145205689)
            ·
              refine ⟨12711786925389159108904267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16949049233852212145205689 12711786925389159108904267)
              ·
                refine ⟨19067680388083738663356401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12711786925389159108904267 19067680388083738663356401)
                ·
                  refine ⟨14300760291062803997517301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19067680388083738663356401 14300760291062803997517301)
                  ·
                    refine ⟨1340696277287137874767247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14300760291062803997517301 1340696277287137874767247)
                    ·
                      rfl

theorem cell23_7832990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7832990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7832990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7832990 prefixEnd_7832990 := by exact prefixLift 7832990
  have htrace : WordTrace (prefixWord ++ tailWord_7832990) baseStart_7832990 baseEnd_7832990 := by
    simpa [prefixWord, tailWord_7832990, baseEnd_7832990] using wordTrace_append hprefix tailTrace_7832990
  have hstable : (prefixWord ++ tailWord_7832990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7832990).length < 2 ^ (prefixWord ++ tailWord_7832990).sum := by decide
  have hdescent : baseEnd_7832990 < baseStart_7832990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7832990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833013 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_7833013 : Nat := 118140960795 + 7833013 * 2 ^ 59
def prefixEnd_7833013 : Nat := 4983230072969 + 3 ^ 40 * 7833013 * 2
def baseEnd_7833013 : Nat := 4022100641916467034314135

theorem tailTrace_7833013 : CollatzResearch.WordTrace tailWord_7833013 prefixEnd_7833013 4022100641916467034314135 := by
  unfold tailWord_7833013
  simp only [CollatzResearch.WordTrace]
  refine ⟨285693454771339147960031693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190462303180892765306687795 285693454771339147960031693)
  ·
    refine ⟨107135045539252180485011885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285693454771339147960031693 107135045539252180485011885)
    ·
      refine ⟨40175642077219567681879457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107135045539252180485011885 40175642077219567681879457)
      ·
        refine ⟨30131731557914675761409593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40175642077219567681879457 30131731557914675761409593)
        ·
          refine ⟨22598798668436006821057195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30131731557914675761409593 22598798668436006821057195)
          ·
            refine ⟨33898198002654010231585793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22598798668436006821057195 33898198002654010231585793)
            ·
              refine ⟨25423648501990507673689345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33898198002654010231585793 25423648501990507673689345)
              ·
                refine ⟨19067736376492880755267009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25423648501990507673689345 19067736376492880755267009)
                ·
                  refine ⟨14300802282369660566450257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19067736376492880755267009 14300802282369660566450257)
                  ·
                    refine ⟨10725601711777245424837693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14300802282369660566450257 10725601711777245424837693)
                    ·
                      refine ⟨4022100641916467034314135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725601711777245424837693 4022100641916467034314135)
                      ·
                        rfl

theorem cell23_7833013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_7833013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833013 prefixEnd_7833013 := by exact prefixLift 7833013
  have htrace : WordTrace (prefixWord ++ tailWord_7833013) baseStart_7833013 baseEnd_7833013 := by
    simpa [prefixWord, tailWord_7833013, baseEnd_7833013] using wordTrace_append hprefix tailTrace_7833013
  have hstable : (prefixWord ++ tailWord_7833013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833013).length < 2 ^ (prefixWord ++ tailWord_7833013).sum := by decide
  have hdescent : baseEnd_7833013 < baseStart_7833013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833063 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 1, 5]
def baseStart_7833063 : Nat := 118140960795 + 7833063 * 2 ^ 59
def prefixEnd_7833063 : Nat := 4983230072969 + 3 ^ 40 * 7833063 * 2
def baseEnd_7833063 : Nat := 1340708771983063946229635

theorem tailTrace_7833063 : CollatzResearch.WordTrace tailWord_7833063 prefixEnd_7833063 1340708771983063946229635 := by
  unfold tailWord_7833063
  simp only [CollatzResearch.WordTrace]
  refine ⟨285695278421158006499351843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190463518947438670999567895 285695278421158006499351843)
  ·
    refine ⟨428542917631737009749027765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285695278421158006499351843 428542917631737009749027765)
    ·
      refine ⟨40175898527975344663971353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 428542917631737009749027765 40175898527975344663971353)
      ·
        refine ⟨30131923895981508497978515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40175898527975344663971353 30131923895981508497978515)
        ·
          refine ⟨45197885843972262746967773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30131923895981508497978515 45197885843972262746967773)
          ·
            refine ⟨16949207191489598530112915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45197885843972262746967773 16949207191489598530112915)
            ·
              refine ⟨25423810787234397795169373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16949207191489598530112915 25423810787234397795169373)
              ·
                refine ⟨9533929045212899173188515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25423810787234397795169373 9533929045212899173188515)
                ·
                  refine ⟨14300893567819348759782773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533929045212899173188515 14300893567819348759782773)
                  ·
                    refine ⟨1340708771983063946229635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14300893567819348759782773 1340708771983063946229635)
                    ·
                      rfl

theorem cell23_7833063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_7833063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833063 prefixEnd_7833063 := by exact prefixLift 7833063
  have htrace : WordTrace (prefixWord ++ tailWord_7833063) baseStart_7833063 baseEnd_7833063 := by
    simpa [prefixWord, tailWord_7833063, baseEnd_7833063] using wordTrace_append hprefix tailTrace_7833063
  have hstable : (prefixWord ++ tailWord_7833063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833063).length < 2 ^ (prefixWord ++ tailWord_7833063).sum := by decide
  have hdescent : baseEnd_7833063 < baseStart_7833063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833077 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7833077 : Nat := 118140960795 + 7833077 * 2 ^ 59
def prefixEnd_7833077 : Nat := 4983230072969 + 3 ^ 40 * 7833077 * 2
def baseEnd_7833077 : Nat := 4022133504678354783913841

theorem tailTrace_7833077 : CollatzResearch.WordTrace tailWord_7833077 prefixEnd_7833077 4022133504678354783913841 := by
  unfold tailWord_7833077
  simp only [CollatzResearch.WordTrace]
  refine ⟨285695789043107286890361485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190463859362071524593574323 285695789043107286890361485)
  ·
    refine ⟨107135920891165232583885557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285695789043107286890361485 107135920891165232583885557)
    ·
      refine ⟨10043992583546740554739271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107135920891165232583885557 10043992583546740554739271)
      ·
        refine ⟨15065988875320110832108907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043992583546740554739271 15065988875320110832108907)
        ·
          refine ⟨22598983312980166248163361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15065988875320110832108907 22598983312980166248163361)
          ·
            refine ⟨16949237484735124686122521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22598983312980166248163361 16949237484735124686122521)
            ·
              refine ⟨12711928113551343514591891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16949237484735124686122521 12711928113551343514591891)
              ·
                refine ⟨19067892170327015271887837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12711928113551343514591891 19067892170327015271887837)
                ·
                  refine ⟨7150459563872630726957939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19067892170327015271887837 7150459563872630726957939)
                  ·
                    refine ⟨10725689345808946090436909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7150459563872630726957939 10725689345808946090436909)
                    ·
                      refine ⟨4022133504678354783913841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725689345808946090436909 4022133504678354783913841)
                      ·
                        rfl

theorem cell23_7833077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7833077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833077 prefixEnd_7833077 := by exact prefixLift 7833077
  have htrace : WordTrace (prefixWord ++ tailWord_7833077) baseStart_7833077 baseEnd_7833077 := by
    simpa [prefixWord, tailWord_7833077, baseEnd_7833077] using wordTrace_append hprefix tailTrace_7833077
  have hstable : (prefixWord ++ tailWord_7833077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833077).length < 2 ^ (prefixWord ++ tailWord_7833077).sum := by decide
  have hdescent : baseEnd_7833077 < baseStart_7833077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833083 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 7, 2, 2]
def baseStart_7833083 : Nat := 118140960795 + 7833083 * 2 ^ 59
def prefixEnd_7833083 : Nat := 4983230072969 + 3 ^ 40 * 7833083 * 2
def baseEnd_7833083 : Nat := 4022136585562281760438813

theorem tailTrace_7833083 : CollatzResearch.WordTrace tailWord_7833083 prefixEnd_7833083 4022136585562281760438813 := by
  unfold tailWord_7833083
  simp only [CollatzResearch.WordTrace]
  refine ⟨285696007881085549915079903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190464005254057033276719935 285696007881085549915079903)
  ·
    refine ⟨428544011821628324872619855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285696007881085549915079903 428544011821628324872619855)
    ·
      refine ⟨642816017732442487308929783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428544011821628324872619855 642816017732442487308929783)
      ·
        refine ⟨964224026598663730963394675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642816017732442487308929783 964224026598663730963394675)
        ·
          refine ⟨1446336039897995596445092013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964224026598663730963394675 1446336039897995596445092013)
          ·
            refine ⟨542376014961748348666909505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1446336039897995596445092013 542376014961748348666909505)
            ·
              refine ⟨406782011221311261500182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542376014961748348666909505 406782011221311261500182129)
              ·
                refine ⟨305086508415983446125136597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406782011221311261500182129 305086508415983446125136597)
                ·
                  refine ⟨7150465040999612018557889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305086508415983446125136597 7150465040999612018557889)
                  ·
                    refine ⟨5362848780749709013918417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150465040999612018557889 5362848780749709013918417)
                    ·
                      refine ⟨4022136585562281760438813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362848780749709013918417 4022136585562281760438813)
                      ·
                        rfl

theorem cell23_7833083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 2, 2].length) (baseStart_7833083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833083 prefixEnd_7833083 := by exact prefixLift 7833083
  have htrace : WordTrace (prefixWord ++ tailWord_7833083) baseStart_7833083 baseEnd_7833083 := by
    simpa [prefixWord, tailWord_7833083, baseEnd_7833083] using wordTrace_append hprefix tailTrace_7833083
  have hstable : (prefixWord ++ tailWord_7833083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833083).length < 2 ^ (prefixWord ++ tailWord_7833083).sum := by decide
  have hdescent : baseEnd_7833083 < baseStart_7833083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833100 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_7833100 : Nat := 118140960795 + 7833100 * 2 ^ 59
def prefixEnd_7833100 : Nat := 4983230072969 + 3 ^ 40 * 7833100 * 2
def baseEnd_7833100 : Nat := 4022145314733408193926235

theorem tailTrace_7833100 : CollatzResearch.WordTrace tailWord_7833100 prefixEnd_7833100 4022145314733408193926235 := by
  unfold tailWord_7833100
  simp only [CollatzResearch.WordTrace]
  refine ⟨142848313961011980909224377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190464418614682641212299169 142848313961011980909224377)
  ·
    refine ⟨107136235470758985681918283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142848313961011980909224377 107136235470758985681918283)
    ·
      refine ⟨160704353206138478522877425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107136235470758985681918283 160704353206138478522877425)
      ·
        refine ⟨120528264904603858892158069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160704353206138478522877425 120528264904603858892158069)
        ·
          refine ⟨11299524834806611771139819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120528264904603858892158069 11299524834806611771139819)
          ·
            refine ⟨16949287252209917656709729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299524834806611771139819 16949287252209917656709729)
            ·
              refine ⟨12711965439157438242532297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16949287252209917656709729 12711965439157438242532297)
              ·
                refine ⟨9533974079368078681899223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12711965439157438242532297 9533974079368078681899223)
                ·
                  refine ⟨14300961119052118022848835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533974079368078681899223 14300961119052118022848835)
                  ·
                    refine ⟨21451441678578177034273253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14300961119052118022848835 21451441678578177034273253)
                    ·
                      refine ⟨4022145314733408193926235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21451441678578177034273253 4022145314733408193926235)
                      ·
                        rfl

theorem cell23_7833100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_7833100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833100 prefixEnd_7833100 := by exact prefixLift 7833100
  have htrace : WordTrace (prefixWord ++ tailWord_7833100) baseStart_7833100 baseEnd_7833100 := by
    simpa [prefixWord, tailWord_7833100, baseEnd_7833100] using wordTrace_append hprefix tailTrace_7833100
  have hstable : (prefixWord ++ tailWord_7833100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833100).length < 2 ^ (prefixWord ++ tailWord_7833100).sum := by decide
  have hdescent : baseEnd_7833100 < baseStart_7833100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833120 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7833120 : Nat := 118140960795 + 7833120 * 2 ^ 59
def prefixEnd_7833120 : Nat := 4983230072969 + 3 ^ 40 * 7833120 * 2
def baseEnd_7833120 : Nat := 4022155584346498115676143

theorem tailTrace_7833120 : CollatzResearch.WordTrace tailWord_7833120 prefixEnd_7833120 4022155584346498115676143 := by
  unfold tailWord_7833120
  simp only [CollatzResearch.WordTrace]
  refine ⟨142848678690975752617088407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190464904921301003489451209 142848678690975752617088407)
  ·
    refine ⟨214273018036463628925632611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142848678690975752617088407 214273018036463628925632611)
    ·
      refine ⟨321409527054695443388448917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214273018036463628925632611 321409527054695443388448917)
      ·
        refine ⟨15066071580688848908833543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321409527054695443388448917 15066071580688848908833543)
        ·
          refine ⟨22599107371033273363250315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066071580688848908833543 22599107371033273363250315)
          ·
            refine ⟨33898661056549910044875473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599107371033273363250315 33898661056549910044875473)
            ·
              refine ⟨25423995792412432533656605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33898661056549910044875473 25423995792412432533656605)
              ·
                refine ⟨9533998422154662200121227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25423995792412432533656605 9533998422154662200121227)
                ·
                  refine ⟨14300997633231993300181841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533998422154662200121227 14300997633231993300181841)
                  ·
                    refine ⟨10725748224923994975136381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14300997633231993300181841 10725748224923994975136381)
                    ·
                      refine ⟨4022155584346498115676143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725748224923994975136381 4022155584346498115676143)
                      ·
                        rfl

theorem cell23_7833120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7833120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833120 prefixEnd_7833120 := by exact prefixLift 7833120
  have htrace : WordTrace (prefixWord ++ tailWord_7833120) baseStart_7833120 baseEnd_7833120 := by
    simpa [prefixWord, tailWord_7833120, baseEnd_7833120] using wordTrace_append hprefix tailTrace_7833120
  have hstable : (prefixWord ++ tailWord_7833120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833120).length < 2 ^ (prefixWord ++ tailWord_7833120).sum := by decide
  have hdescent : baseEnd_7833120 < baseStart_7833120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833123 : List Nat := [1, 1, 1, 4, 6, 1, 9]
def baseStart_7833123 : Nat := 118140960795 + 7833123 * 2 ^ 59
def prefixEnd_7833123 : Nat := 4983230072969 + 3 ^ 40 * 7833123 * 2
def baseEnd_7833123 : Nat := 49656260799857550665909

theorem tailTrace_7833123 : CollatzResearch.WordTrace tailWord_7833123 prefixEnd_7833123 49656260799857550665909 := by
  unfold tailWord_7833123
  simp only [CollatzResearch.WordTrace]
  refine ⟨285697466800940636746536023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190464977867293757831024015 285697466800940636746536023)
  ·
    refine ⟨428546200201410955119804035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285697466800940636746536023 428546200201410955119804035)
    ·
      refine ⟨642819300302116432679706053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428546200201410955119804035 642819300302116432679706053)
      ·
        refine ⟨120528618806646831127444885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 642819300302116432679706053 120528618806646831127444885)
        ·
          refine ⟨5649779006561570209098979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120528618806646831127444885 5649779006561570209098979)
          ·
            refine ⟨8474668509842355313648469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649779006561570209098979 8474668509842355313648469)
            ·
              refine ⟨49656260799857550665909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8474668509842355313648469 49656260799857550665909)
              ·
                rfl

theorem cell23_7833123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 9].length) (baseStart_7833123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833123 prefixEnd_7833123 := by exact prefixLift 7833123
  have htrace : WordTrace (prefixWord ++ tailWord_7833123) baseStart_7833123 baseEnd_7833123 := by
    simpa [prefixWord, tailWord_7833123, baseEnd_7833123] using wordTrace_append hprefix tailTrace_7833123
  have hstable : (prefixWord ++ tailWord_7833123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833123).length < 2 ^ (prefixWord ++ tailWord_7833123).sum := by decide
  have hdescent : baseEnd_7833123 < baseStart_7833123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833134 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7833134 : Nat := 118140960795 + 7833134 * 2 ^ 59
def prefixEnd_7833134 : Nat := 4983230072969 + 3 ^ 40 * 7833134 * 2
def baseEnd_7833134 : Nat := 4022162773075661060901079

theorem tailTrace_7833134 : CollatzResearch.WordTrace tailWord_7833134 prefixEnd_7833134 4022162773075661060901079 := by
  unfold tailWord_7833134
  simp only [CollatzResearch.WordTrace]
  refine ⟨35712233500487598203148307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190465245335933857083457637 35712233500487598203148307)
  ·
    refine ⟨53568350250731397304722461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35712233500487598203148307 53568350250731397304722461)
    ·
      refine ⟨20088131344024273989270923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53568350250731397304722461 20088131344024273989270923)
      ·
        refine ⟨30132197016036410983906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20088131344024273989270923 30132197016036410983906385)
        ·
          refine ⟨22599147762027308237929789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30132197016036410983906385 22599147762027308237929789)
          ·
            refine ⟨8474680410760240589223671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22599147762027308237929789 8474680410760240589223671)
            ·
              refine ⟨12712020616140360883835507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474680410760240589223671 12712020616140360883835507)
              ·
                refine ⟨19068030924210541325753261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12712020616140360883835507 19068030924210541325753261)
                ·
                  refine ⟨7150511596578952997157473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19068030924210541325753261 7150511596578952997157473)
                  ·
                    refine ⟨5362883697434214747868105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150511596578952997157473 5362883697434214747868105)
                    ·
                      refine ⟨4022162773075661060901079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362883697434214747868105 4022162773075661060901079)
                      ·
                        rfl

theorem cell23_7833134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7833134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833134 prefixEnd_7833134 := by exact prefixLift 7833134
  have htrace : WordTrace (prefixWord ++ tailWord_7833134) baseStart_7833134 baseEnd_7833134 := by
    simpa [prefixWord, tailWord_7833134, baseEnd_7833134] using wordTrace_append hprefix tailTrace_7833134
  have hstable : (prefixWord ++ tailWord_7833134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833134).length < 2 ^ (prefixWord ++ tailWord_7833134).sum := by decide
  have hdescent : baseEnd_7833134 < baseStart_7833134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833166 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_7833166 : Nat := 118140960795 + 7833166 * 2 ^ 59
def prefixEnd_7833166 : Nat := 4983230072969 + 3 ^ 40 * 7833166 * 2
def baseEnd_7833166 : Nat := 1340726401485534978566977

theorem tailTrace_7833166 : CollatzResearch.WordTrace tailWord_7833166 prefixEnd_7833166 1340726401485534978566977 := by
  unfold tailWord_7833166
  simp only [CollatzResearch.WordTrace]
  refine ⟨35712379392473106886293919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190466023426523236726900901 35712379392473106886293919)
  ·
    refine ⟨53568569088709660329440879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35712379392473106886293919 53568569088709660329440879)
    ·
      refine ⟨80352853633064490494161319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53568569088709660329440879 80352853633064490494161319)
      ·
        refine ⟨120529280449596735741241979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80352853633064490494161319 120529280449596735741241979)
        ·
          refine ⟨180793920674395103611862969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120529280449596735741241979 180793920674395103611862969)
          ·
            refine ⟨135595440505796327708897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180793920674395103611862969 135595440505796327708897227)
            ·
              refine ⟨203393160758694491563345841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135595440505796327708897227 203393160758694491563345841)
              ·
                refine ⟨152544870569020868672509381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203393160758694491563345841 152544870569020868672509381)
                ·
                  refine ⟨28602163231691412876095509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152544870569020868672509381 28602163231691412876095509)
                  ·
                    refine ⟨1340726401485534978566977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28602163231691412876095509 1340726401485534978566977)
                    ·
                      rfl

theorem cell23_7833166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_7833166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833166 prefixEnd_7833166 := by exact prefixLift 7833166
  have htrace : WordTrace (prefixWord ++ tailWord_7833166) baseStart_7833166 baseEnd_7833166 := by
    simpa [prefixWord, tailWord_7833166, baseEnd_7833166] using wordTrace_append hprefix tailTrace_7833166
  have hstable : (prefixWord ++ tailWord_7833166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833166).length < 2 ^ (prefixWord ++ tailWord_7833166).sum := by decide
  have hdescent : baseEnd_7833166 < baseStart_7833166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833196 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 7]
def baseStart_7833196 : Nat := 118140960795 + 7833196 * 2 ^ 59
def prefixEnd_7833196 : Nat := 4983230072969 + 3 ^ 40 * 7833196 * 2
def baseEnd_7833196 : Nat := 446910512097359979813977

theorem tailTrace_7833196 : CollatzResearch.WordTrace tailWord_7833196 prefixEnd_7833196 446910512097359979813977 := by
  unfold tailWord_7833196
  simp only [CollatzResearch.WordTrace]
  refine ⟨142850064664838085106971721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190466752886450780142628961 142850064664838085106971721)
  ·
    refine ⟨107137548498628563830228791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142850064664838085106971721 107137548498628563830228791)
    ·
      refine ⟨160706322747942845745343187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107137548498628563830228791 160706322747942845745343187)
      ·
        refine ⟨241059484121914268618014781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160706322747942845745343187 241059484121914268618014781)
        ·
          refine ⟨90397306545717850731755543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241059484121914268618014781 90397306545717850731755543)
          ·
            refine ⟨135595959818576776097633315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90397306545717850731755543 135595959818576776097633315)
            ·
              refine ⟨203393939727865164146449973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135595959818576776097633315 203393939727865164146449973)
              ·
                refine ⟨19068181849487359138729685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203393939727865164146449973 19068181849487359138729685)
                ·
                  refine ⟨446910512097359979813977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19068181849487359138729685 446910512097359979813977)
                  ·
                    rfl

theorem cell23_7833196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_7833196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833196 prefixEnd_7833196 := by exact prefixLift 7833196
  have htrace : WordTrace (prefixWord ++ tailWord_7833196) baseStart_7833196 baseEnd_7833196 := by
    simpa [prefixWord, tailWord_7833196, baseEnd_7833196] using wordTrace_append hprefix tailTrace_7833196
  have hstable : (prefixWord ++ tailWord_7833196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833196).length < 2 ^ (prefixWord ++ tailWord_7833196).sum := by decide
  have hdescent : baseEnd_7833196 < baseStart_7833196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833213 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 7]
def baseStart_7833213 : Nat := 118140960795 + 7833213 * 2 ^ 59
def prefixEnd_7833213 : Nat := 4983230072969 + 3 ^ 40 * 7833213 * 2
def baseEnd_7833213 : Nat := 446911482005262916868135

theorem tailTrace_7833213 : CollatzResearch.WordTrace tailWord_7833213 prefixEnd_7833213 446911482005262916868135 := by
  unfold tailWord_7833213
  simp only [CollatzResearch.WordTrace]
  refine ⟨285700749370614582117312293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190467166247076388078208195 285700749370614582117312293)
  ·
    refine ⟨53568890506990234146996055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285700749370614582117312293 53568890506990234146996055)
    ·
      refine ⟨80353335760485351220494083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53568890506990234146996055 80353335760485351220494083)
      ·
        refine ⟨120530003640728026830741125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80353335760485351220494083 120530003640728026830741125)
        ·
          refine ⟨22599375682636505030763961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120530003640728026830741125 22599375682636505030763961)
          ·
            refine ⟨16949531761977378773072971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22599375682636505030763961 16949531761977378773072971)
            ·
              refine ⟨25424297642966068159609457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16949531761977378773072971 25424297642966068159609457)
              ·
                refine ⟨19068223232224551119707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25424297642966068159609457 19068223232224551119707093)
                ·
                  refine ⟨446911482005262916868135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19068223232224551119707093 446911482005262916868135)
                  ·
                    rfl

theorem cell23_7833213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_7833213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833213 prefixEnd_7833213 := by exact prefixLift 7833213
  have htrace : WordTrace (prefixWord ++ tailWord_7833213) baseStart_7833213 baseEnd_7833213 := by
    simpa [prefixWord, tailWord_7833213, baseEnd_7833213] using wordTrace_append hprefix tailTrace_7833213
  have hstable : (prefixWord ++ tailWord_7833213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833213).length < 2 ^ (prefixWord ++ tailWord_7833213).sum := by decide
  have hdescent : baseEnd_7833213 < baseStart_7833213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833230 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_7833230 : Nat := 118140960795 + 7833230 * 2 ^ 59
def prefixEnd_7833230 : Nat := 4983230072969 + 3 ^ 40 * 7833230 * 2
def baseEnd_7833230 : Nat := 446912451913165853922293

theorem tailTrace_7833230 : CollatzResearch.WordTrace tailWord_7833230 prefixEnd_7833230 446912451913165853922293 := by
  unfold tailWord_7833230
  simp only [CollatzResearch.WordTrace]
  refine ⟨35712671176444124252585143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190467579607701996013787429 35712671176444124252585143)
  ·
    refine ⟨53569006764666186378877715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35712671176444124252585143 53569006764666186378877715)
    ·
      refine ⟨80353510146999279568316573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53569006764666186378877715 80353510146999279568316573)
      ·
        refine ⟨30132566305124729838118715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80353510146999279568316573 30132566305124729838118715)
        ·
          refine ⟨45198849457687094757178073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30132566305124729838118715 45198849457687094757178073)
          ·
            refine ⟨33899137093265321067883555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45198849457687094757178073 33899137093265321067883555)
            ·
              refine ⟨50848705639897981601825333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33899137093265321067883555 50848705639897981601825333)
              ·
                refine ⟨4767066153740435775171125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50848705639897981601825333 4767066153740435775171125)
                ·
                  refine ⟨446912451913165853922293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767066153740435775171125 446912451913165853922293)
                  ·
                    rfl

theorem cell23_7833230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_7833230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833230 prefixEnd_7833230 := by exact prefixLift 7833230
  have htrace : WordTrace (prefixWord ++ tailWord_7833230) baseStart_7833230 baseEnd_7833230 := by
    simpa [prefixWord, tailWord_7833230, baseEnd_7833230] using wordTrace_append hprefix tailTrace_7833230
  have hstable : (prefixWord ++ tailWord_7833230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833230).length < 2 ^ (prefixWord ++ tailWord_7833230).sum := by decide
  have hdescent : baseEnd_7833230 < baseStart_7833230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833233 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_7833233 : Nat := 118140960795 + 7833233 * 2 ^ 59
def prefixEnd_7833233 : Nat := 4983230072969 + 3 ^ 40 * 7833233 * 2
def baseEnd_7833233 : Nat := 4022213607660456173563123

theorem tailTrace_7833233 : CollatzResearch.WordTrace tailWord_7833233 prefixEnd_7833233 4022213607660456173563123 := by
  unfold tailWord_7833233
  simp only [CollatzResearch.WordTrace]
  refine ⟨285701478830542125533040353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190467652553694750355360235 285701478830542125533040353)
  ·
    refine ⟨214276109122906594149780265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285701478830542125533040353 214276109122906594149780265)
    ·
      refine ⟨160707081842179945612335199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214276109122906594149780265 160707081842179945612335199)
      ·
        refine ⟨241060622763269918418502799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160707081842179945612335199 241060622763269918418502799)
        ·
          refine ⟨361590934144904877627754199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241060622763269918418502799 361590934144904877627754199)
          ·
            refine ⟨542386401217357316441631299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361590934144904877627754199 542386401217357316441631299)
            ·
              refine ⟨813579601826035974662446949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542386401217357316441631299 813579601826035974662446949)
              ·
                refine ⟨152546175342381745249208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 813579601826035974662446949 152546175342381745249208803)
                ·
                  refine ⟨228819263013572617873813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152546175342381745249208803 228819263013572617873813205)
                  ·
                    refine ⟨5362951476880608231417497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228819263013572617873813205 5362951476880608231417497)
                    ·
                      refine ⟨4022213607660456173563123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5362951476880608231417497 4022213607660456173563123)
                      ·
                        rfl

theorem cell23_7833233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_7833233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833233 prefixEnd_7833233 := by exact prefixLift 7833233
  have htrace : WordTrace (prefixWord ++ tailWord_7833233) baseStart_7833233 baseEnd_7833233 := by
    simpa [prefixWord, tailWord_7833233, baseEnd_7833233] using wordTrace_append hprefix tailTrace_7833233
  have hstable : (prefixWord ++ tailWord_7833233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833233).length < 2 ^ (prefixWord ++ tailWord_7833233).sum := by decide
  have hdescent : baseEnd_7833233 < baseStart_7833233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833283 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3]
def baseStart_7833283 : Nat := 118140960795 + 7833283 * 2 ^ 59
def prefixEnd_7833283 : Nat := 4983230072969 + 3 ^ 40 * 7833283 * 2
def baseEnd_7833283 : Nat := 4022239281693180977937893

theorem tailTrace_7833283 : CollatzResearch.WordTrace tailWord_7833283 prefixEnd_7833283 4022239281693180977937893 := by
  unfold tailWord_7833283
  simp only [CollatzResearch.WordTrace]
  refine ⟨285703302480360984072360503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190468868320240656048240335 285703302480360984072360503)
  ·
    refine ⟨428554953720541476108540755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285703302480360984072360503 428554953720541476108540755)
    ·
      refine ⟨642832430580812214162811133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428554953720541476108540755 642832430580812214162811133)
      ·
        refine ⟨241062161467804580311054175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642832430580812214162811133 241062161467804580311054175)
        ·
          refine ⟨361593242201706870466581263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241062161467804580311054175 361593242201706870466581263)
          ·
            refine ⟨542389863302560305699871895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361593242201706870466581263 542389863302560305699871895)
            ·
              refine ⟨813584794953840458549807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542389863302560305699871895 813584794953840458549807843)
              ·
                refine ⟨1220377192430760687824711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813584794953840458549807843 1220377192430760687824711765)
                ·
                  refine ⟨14301295223797976810445841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1220377192430760687824711765 14301295223797976810445841)
                  ·
                    refine ⟨10725971417848482607834381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14301295223797976810445841 10725971417848482607834381)
                    ·
                      refine ⟨4022239281693180977937893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10725971417848482607834381 4022239281693180977937893)
                      ·
                        rfl

theorem cell23_7833283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_7833283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833283 prefixEnd_7833283 := by exact prefixLift 7833283
  have htrace : WordTrace (prefixWord ++ tailWord_7833283) baseStart_7833283 baseEnd_7833283 := by
    simpa [prefixWord, tailWord_7833283, baseEnd_7833283] using wordTrace_append hprefix tailTrace_7833283
  have hstable : (prefixWord ++ tailWord_7833283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833283).length < 2 ^ (prefixWord ++ tailWord_7833283).sum := by decide
  have hdescent : baseEnd_7833283 < baseStart_7833283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833303 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 6]
def baseStart_7833303 : Nat := 118140960795 + 7833303 * 2 ^ 59
def prefixEnd_7833303 : Nat := 4983230072969 + 3 ^ 40 * 7833303 * 2
def baseEnd_7833303 : Nat := 446916616811807877743089

theorem tailTrace_7833303 : CollatzResearch.WordTrace tailWord_7833303 prefixEnd_7833303 446916616811807877743089 := by
  unfold tailWord_7833303
  simp only [CollatzResearch.WordTrace]
  refine ⟨285704031940288527488088563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190469354626859018325392375 285704031940288527488088563)
  ·
    refine ⟨428556047910432791232132845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285704031940288527488088563 428556047910432791232132845)
    ·
      refine ⟨160708517966412296712049817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428556047910432791232132845 160708517966412296712049817)
      ·
        refine ⟨120531388474809222534037363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160708517966412296712049817 120531388474809222534037363)
        ·
          refine ⟨180797082712213833801056045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120531388474809222534037363 180797082712213833801056045)
          ·
            refine ⟨67798906017080187675396017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180797082712213833801056045 67798906017080187675396017)
            ·
              refine ⟨50849179512810140756547013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67798906017080187675396017 50849179512810140756547013)
              ·
                refine ⟨9534221158651901391852565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50849179512810140756547013 9534221158651901391852565)
                ·
                  refine ⟨446916616811807877743089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534221158651901391852565 446916616811807877743089)
                  ·
                    rfl

theorem cell23_7833303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 6].length) (baseStart_7833303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833303 prefixEnd_7833303 := by exact prefixLift 7833303
  have htrace : WordTrace (prefixWord ++ tailWord_7833303) baseStart_7833303 baseEnd_7833303 := by
    simpa [prefixWord, tailWord_7833303, baseEnd_7833303] using wordTrace_append hprefix tailTrace_7833303
  have hstable : (prefixWord ++ tailWord_7833303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833303).length < 2 ^ (prefixWord ++ tailWord_7833303).sum := by decide
  have hdescent : baseEnd_7833303 < baseStart_7833303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833320 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 6]
def baseStart_7833320 : Nat := 118140960795 + 7833320 * 2 ^ 59
def prefixEnd_7833320 : Nat := 4983230072969 + 3 ^ 40 * 7833320 * 2
def baseEnd_7833320 : Nat := 446917586719710814797247

theorem tailTrace_7833320 : CollatzResearch.WordTrace tailWord_7833320 prefixEnd_7833320 446917586719710814797247 := by
  unfold tailWord_7833320
  simp only [CollatzResearch.WordTrace]
  refine ⟨142852325990613469695728707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190469767987484626260971609 142852325990613469695728707)
  ·
    refine ⟨214278488985920204543593061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142852325990613469695728707 214278488985920204543593061)
    ·
      refine ⟨40177216684860038351923699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214278488985920204543593061 40177216684860038351923699)
      ·
        refine ⟨60265825027290057527885549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40177216684860038351923699 60265825027290057527885549)
        ·
          refine ⟨22599684385233771572957081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60265825027290057527885549 22599684385233771572957081)
          ·
            refine ⟨16949763288925328679717811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22599684385233771572957081 16949763288925328679717811)
            ·
              refine ⟨25424644933387993019576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16949763288925328679717811 25424644933387993019576717)
              ·
                refine ⟨9534241850020497382341269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25424644933387993019576717 9534241850020497382341269)
                ·
                  refine ⟨446917586719710814797247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534241850020497382341269 446917586719710814797247)
                  ·
                    rfl

theorem cell23_7833320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_7833320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833320 prefixEnd_7833320 := by exact prefixLift 7833320
  have htrace : WordTrace (prefixWord ++ tailWord_7833320) baseStart_7833320 baseEnd_7833320 := by
    simpa [prefixWord, tailWord_7833320, baseEnd_7833320] using wordTrace_append hprefix tailTrace_7833320
  have hstable : (prefixWord ++ tailWord_7833320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833320).length < 2 ^ (prefixWord ++ tailWord_7833320).sum := by decide
  have hdescent : baseEnd_7833320 < baseStart_7833320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833370 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_7833370 : Nat := 118140960795 + 7833370 * 2 ^ 59
def prefixEnd_7833370 : Nat := 4983230072969 + 3 ^ 40 * 7833370 * 2
def baseEnd_7833370 : Nat := 4022283954510122137549993

theorem tailTrace_7833370 : CollatzResearch.WordTrace tailWord_7833370 prefixEnd_7833370 4022283954510122137549993 := by
  unfold tailWord_7833370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426618907761449482694391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190470983754030531953851709 71426618907761449482694391)
  ·
    refine ⟨107139928361642174224041587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71426618907761449482694391 107139928361642174224041587)
    ·
      refine ⟨160709892542463261336062381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107139928361642174224041587 160709892542463261336062381)
      ·
        refine ⟨60266209703423723001023393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160709892542463261336062381 60266209703423723001023393)
        ·
          refine ⟨45199657277567792250767545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60266209703423723001023393 45199657277567792250767545)
          ·
            refine ⟨33899742958175844188075659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45199657277567792250767545 33899742958175844188075659)
            ·
              refine ⟨50849614437263766282113489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33899742958175844188075659 50849614437263766282113489)
              ·
                refine ⟨38137210827947824711585117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50849614437263766282113489 38137210827947824711585117)
                ·
                  refine ⟨14301454060480434266844419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38137210827947824711585117 14301454060480434266844419)
                  ·
                    refine ⟨21452181090720651400266629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14301454060480434266844419 21452181090720651400266629)
                    ·
                      refine ⟨4022283954510122137549993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21452181090720651400266629 4022283954510122137549993)
                      ·
                        rfl

theorem cell23_7833370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_7833370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833370 prefixEnd_7833370 := by exact prefixLift 7833370
  have htrace : WordTrace (prefixWord ++ tailWord_7833370) baseStart_7833370 baseEnd_7833370 := by
    simpa [prefixWord, tailWord_7833370, baseEnd_7833370] using wordTrace_append hprefix tailTrace_7833370
  have hstable : (prefixWord ++ tailWord_7833370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833370).length < 2 ^ (prefixWord ++ tailWord_7833370).sum := by decide
  have hdescent : baseEnd_7833370 < baseStart_7833370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833380 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7833380 : Nat := 118140960795 + 7833380 * 2 ^ 59
def prefixEnd_7833380 : Nat := 4983230072969 + 3 ^ 40 * 7833380 * 2
def baseEnd_7833380 : Nat := 1340763029772222366141649

theorem tailTrace_7833380 : CollatzResearch.WordTrace tailWord_7833380 prefixEnd_7833380 1340763029772222366141649 := by
  unfold tailWord_7833380
  simp only [CollatzResearch.WordTrace]
  refine ⟨142853420180504784819320797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190471226907339713092427729 142853420180504784819320797)
  ·
    refine ⟨53570032567689294307245299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142853420180504784819320797 53570032567689294307245299)
    ·
      refine ⟨80355048851533941460867949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53570032567689294307245299 80355048851533941460867949)
      ·
        refine ⟨30133143319325228047825481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80355048851533941460867949 30133143319325228047825481)
        ·
          refine ⟨22599857489493921035869111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30133143319325228047825481 22599857489493921035869111)
          ·
            refine ⟨33899786234240881553803667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599857489493921035869111 33899786234240881553803667)
            ·
              refine ⟨50849679351361322330705501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33899786234240881553803667 50849679351361322330705501)
              ·
                refine ⟨19068629756760495874014563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50849679351361322330705501 19068629756760495874014563)
                ·
                  refine ⟨28602944635140743811021845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19068629756760495874014563 28602944635140743811021845)
                  ·
                    refine ⟨1340763029772222366141649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28602944635140743811021845 1340763029772222366141649)
                    ·
                      rfl

theorem cell23_7833380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7833380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833380 prefixEnd_7833380 := by exact prefixLift 7833380
  have htrace : WordTrace (prefixWord ++ tailWord_7833380) baseStart_7833380 baseEnd_7833380 := by
    simpa [prefixWord, tailWord_7833380, baseEnd_7833380] using wordTrace_append hprefix tailTrace_7833380
  have hstable : (prefixWord ++ tailWord_7833380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833380).length < 2 ^ (prefixWord ++ tailWord_7833380).sum := by decide
  have hdescent : baseEnd_7833380 < baseStart_7833380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833398 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_7833398 : Nat := 118140960795 + 7833398 * 2 ^ 59
def prefixEnd_7833398 : Nat := 4983230072969 + 3 ^ 40 * 7833398 * 2
def baseEnd_7833398 : Nat := 4022298331968448027999865

theorem tailTrace_7833398 : CollatzResearch.WordTrace tailWord_7833398 prefixEnd_7833398 4022298331968448027999865 := by
  unfold tailWord_7833398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856718554684022419549803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190471664583296239141864565 17856718554684022419549803)
  ·
    refine ⟨26785077832026033629324705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856718554684022419549803 26785077832026033629324705)
    ·
      refine ⟨20088808374019525221993529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26785077832026033629324705 20088808374019525221993529)
      ·
        refine ⟨15066606280514643916495147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20088808374019525221993529 15066606280514643916495147)
        ·
          refine ⟨22599909420771965874742721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066606280514643916495147 22599909420771965874742721)
          ·
            refine ⟨16949932065578974406057041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22599909420771965874742721 16949932065578974406057041)
            ·
              refine ⟨12712449049184230804542781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16949932065578974406057041 12712449049184230804542781)
              ·
                refine ⟨4767168393444086551703543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12712449049184230804542781 4767168393444086551703543)
                ·
                  refine ⟨7150752590166129827555315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767168393444086551703543 7150752590166129827555315)
                  ·
                    refine ⟨10726128885249194741332973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7150752590166129827555315 10726128885249194741332973)
                    ·
                      refine ⟨4022298331968448027999865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726128885249194741332973 4022298331968448027999865)
                      ·
                        rfl

theorem cell23_7833398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_7833398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833398 prefixEnd_7833398 := by exact prefixLift 7833398
  have htrace : WordTrace (prefixWord ++ tailWord_7833398) baseStart_7833398 baseEnd_7833398 := by
    simpa [prefixWord, tailWord_7833398, baseEnd_7833398] using wordTrace_append hprefix tailTrace_7833398
  have hstable : (prefixWord ++ tailWord_7833398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833398).length < 2 ^ (prefixWord ++ tailWord_7833398).sum := by decide
  have hdescent : baseEnd_7833398 < baseStart_7833398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833400 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_7833400 : Nat := 118140960795 + 7833400 * 2 ^ 59
def prefixEnd_7833400 : Nat := 4983230072969 + 3 ^ 40 * 7833400 * 2
def baseEnd_7833400 : Nat := 4022299358929757020174855

theorem tailTrace_7833400 : CollatzResearch.WordTrace tailWord_7833400 prefixEnd_7833400 4022299358929757020174855 := by
  unfold tailWord_7833400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142853784910468556527184827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190471713213958075369579769 142853784910468556527184827)
  ·
    refine ⟨214280677365702834790777241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142853784910468556527184827 214280677365702834790777241)
    ·
      refine ⟨160710508024277126093082931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214280677365702834790777241 160710508024277126093082931)
      ·
        refine ⟨241065762036415689139624397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160710508024277126093082931 241065762036415689139624397)
        ·
          refine ⟨90399660763655883427359149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241065762036415689139624397 90399660763655883427359149)
          ·
            refine ⟨33899872786370956285259681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90399660763655883427359149 33899872786370956285259681)
            ·
              refine ⟨25424904589778217213944761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33899872786370956285259681 25424904589778217213944761)
              ·
                refine ⟨19068678442333662910458571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25424904589778217213944761 19068678442333662910458571)
                ·
                  refine ⟨28603017663500494365687857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19068678442333662910458571 28603017663500494365687857)
                  ·
                    refine ⟨21452263247625370774265893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28603017663500494365687857 21452263247625370774265893)
                    ·
                      refine ⟨4022299358929757020174855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21452263247625370774265893 4022299358929757020174855)
                      ·
                        rfl

theorem cell23_7833400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_7833400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833400 prefixEnd_7833400 := by exact prefixLift 7833400
  have htrace : WordTrace (prefixWord ++ tailWord_7833400) baseStart_7833400 baseEnd_7833400 := by
    simpa [prefixWord, tailWord_7833400, baseEnd_7833400] using wordTrace_append hprefix tailTrace_7833400
  have hstable : (prefixWord ++ tailWord_7833400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833400).length < 2 ^ (prefixWord ++ tailWord_7833400).sum := by decide
  have hdescent : baseEnd_7833400 < baseStart_7833400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833401 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_7833401 : Nat := 118140960795 + 7833401 * 2 ^ 59
def prefixEnd_7833401 : Nat := 4983230072969 + 3 ^ 40 * 7833401 * 2
def baseEnd_7833401 : Nat := 1340766624136803838754117

theorem tailTrace_7833401 : CollatzResearch.WordTrace tailWord_7833401 prefixEnd_7833401 1340766624136803838754117 := by
  unfold tailWord_7833401
  simp only [CollatzResearch.WordTrace]
  refine ⟨285707606293933490225156057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190471737529288993483437371 285707606293933490225156057)
  ·
    refine ⟨214280704720450117668867043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285707606293933490225156057 214280704720450117668867043)
    ·
      refine ⟨321421057080675176503300565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214280704720450117668867043 321421057080675176503300565)
      ·
        refine ⟨7533306025328324449296107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 321421057080675176503300565 7533306025328324449296107)
        ·
          refine ⟨11299959037992486673944161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533306025328324449296107 11299959037992486673944161)
          ·
            refine ⟨8474969278494365005458121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11299959037992486673944161 8474969278494365005458121)
            ·
              refine ⟨6356226958870773754093591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8474969278494365005458121 6356226958870773754093591)
              ·
                refine ⟨9534340438306160631140387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356226958870773754093591 9534340438306160631140387)
                ·
                  refine ⟨14301510657459240946710581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9534340438306160631140387 14301510657459240946710581)
                  ·
                    refine ⟨1340766624136803838754117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14301510657459240946710581 1340766624136803838754117)
                    ·
                      rfl

theorem cell23_7833401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_7833401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833401 prefixEnd_7833401 := by exact prefixLift 7833401
  have htrace : WordTrace (prefixWord ++ tailWord_7833401) baseStart_7833401 baseEnd_7833401 := by
    simpa [prefixWord, tailWord_7833401, baseEnd_7833401] using wordTrace_append hprefix tailTrace_7833401
  have hstable : (prefixWord ++ tailWord_7833401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833401).length < 2 ^ (prefixWord ++ tailWord_7833401).sum := by decide
  have hdescent : baseEnd_7833401 < baseStart_7833401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833421 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7833421 : Nat := 118140960795 + 7833421 * 2 ^ 59
def prefixEnd_7833421 : Nat := 4983230072969 + 3 ^ 40 * 7833421 * 2
def baseEnd_7833421 : Nat := 4022310142023501438012259

theorem tailTrace_7833421 : CollatzResearch.WordTrace tailWord_7833421 prefixEnd_7833421 4022310142023501438012259 := by
  unfold tailWord_7833421
  simp only [CollatzResearch.WordTrace]
  refine ⟨285708335753861033640884117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190472223835907355760589411 285708335753861033640884117)
  ·
    refine ⟨13392578238462235951916443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285708335753861033640884117 13392578238462235951916443)
    ·
      refine ⟨20088867357693353927874665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392578238462235951916443 20088867357693353927874665)
      ·
        refine ⟨15066650518270015445905999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20088867357693353927874665 15066650518270015445905999)
        ·
          refine ⟨22599975777405023168858999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066650518270015445905999 22599975777405023168858999)
          ·
            refine ⟨33899963666107534753288499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599975777405023168858999 33899963666107534753288499)
            ·
              refine ⟨50849945499161302129932749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33899963666107534753288499 50849945499161302129932749)
              ·
                refine ⟨19068729562185488298724781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50849945499161302129932749 19068729562185488298724781)
                ·
                  refine ⟨7150773585819558112021793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19068729562185488298724781 7150773585819558112021793)
                  ·
                    refine ⟨5363080189364668584016345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7150773585819558112021793 5363080189364668584016345)
                    ·
                      refine ⟨4022310142023501438012259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363080189364668584016345 4022310142023501438012259)
                      ·
                        rfl

theorem cell23_7833421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7833421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833421 prefixEnd_7833421 := by exact prefixLift 7833421
  have htrace : WordTrace (prefixWord ++ tailWord_7833421) baseStart_7833421 baseEnd_7833421 := by
    simpa [prefixWord, tailWord_7833421, baseEnd_7833421] using wordTrace_append hprefix tailTrace_7833421
  have hstable : (prefixWord ++ tailWord_7833421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833421).length < 2 ^ (prefixWord ++ tailWord_7833421).sum := by decide
  have hdescent : baseEnd_7833421 < baseStart_7833421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833444 : List Nat := [2, 3, 1, 1, 6, 1, 2, 7]
def baseStart_7833444 : Nat := 118140960795 + 7833444 * 2 ^ 59
def prefixEnd_7833444 : Nat := 4983230072969 + 3 ^ 40 * 7833444 * 2
def baseEnd_7833444 : Nat := 148974887114020549926839

theorem tailTrace_7833444 : CollatzResearch.WordTrace tailWord_7833444 prefixEnd_7833444 148974887114020549926839 := by
  unfold tailWord_7833444
  simp only [CollatzResearch.WordTrace]
  refine ⟨142854587316388854284485693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190472783088518472379314257 142854587316388854284485693)
  ·
    refine ⟨53570470243645820356682135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142854587316388854284485693 53570470243645820356682135)
    ·
      refine ⟨80355705365468730535023203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53570470243645820356682135 80355705365468730535023203)
      ·
        refine ⟨120533558048203095802534805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80355705365468730535023203 120533558048203095802534805)
        ·
          refine ⟨5650010533509520115743819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120533558048203095802534805 5650010533509520115743819)
          ·
            refine ⟨8475015800264280173615729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650010533509520115743819 8475015800264280173615729)
            ·
              refine ⟨6356261850198210130211797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475015800264280173615729 6356261850198210130211797)
              ·
                refine ⟨148974887114020549926839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6356261850198210130211797 148974887114020549926839)
                ·
                  rfl

theorem cell23_7833444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 7].length) (baseStart_7833444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833444 prefixEnd_7833444 := by exact prefixLift 7833444
  have htrace : WordTrace (prefixWord ++ tailWord_7833444) baseStart_7833444 baseEnd_7833444 := by
    simpa [prefixWord, tailWord_7833444, baseEnd_7833444] using wordTrace_append hprefix tailTrace_7833444
  have hstable : (prefixWord ++ tailWord_7833444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833444).length < 2 ^ (prefixWord ++ tailWord_7833444).sum := by decide
  have hdescent : baseEnd_7833444 < baseStart_7833444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833454 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7833454 : Nat := 118140960795 + 7833454 * 2 ^ 59
def prefixEnd_7833454 : Nat := 4983230072969 + 3 ^ 40 * 7833454 * 2
def baseEnd_7833454 : Nat := 4022327086885099808899607

theorem tailTrace_7833454 : CollatzResearch.WordTrace tailWord_7833454 prefixEnd_7833454 4022327086885099808899607 := by
  unfold tailWord_7833454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713692420342685034604427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190473026241827653517890277 35713692420342685034604427)
  ·
    refine ⟨53570538630514027551906641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35713692420342685034604427 53570538630514027551906641)
    ·
      refine ⟨40177903972885520663929981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53570538630514027551906641 40177903972885520663929981)
      ·
        refine ⟨15066713989832070248973743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40177903972885520663929981 15066713989832070248973743)
        ·
          refine ⟨22600070984748105373460615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066713989832070248973743 22600070984748105373460615)
          ·
            refine ⟨33900106477122158060190923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22600070984748105373460615 33900106477122158060190923)
            ·
              refine ⟨50850159715683237090286385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33900106477122158060190923 50850159715683237090286385)
              ·
                refine ⟨38137619786762427817714789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50850159715683237090286385 38137619786762427817714789)
                ·
                  refine ⟨7150803710017955215821523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38137619786762427817714789 7150803710017955215821523)
                  ·
                    refine ⟨10726205565026932823732285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7150803710017955215821523 10726205565026932823732285)
                    ·
                      refine ⟨4022327086885099808899607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726205565026932823732285 4022327086885099808899607)
                      ·
                        rfl

theorem cell23_7833454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7833454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833454 prefixEnd_7833454 := by exact prefixLift 7833454
  have htrace : WordTrace (prefixWord ++ tailWord_7833454) baseStart_7833454 baseEnd_7833454 := by
    simpa [prefixWord, tailWord_7833454, baseEnd_7833454] using wordTrace_append hprefix tailTrace_7833454
  have hstable : (prefixWord ++ tailWord_7833454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833454).length < 2 ^ (prefixWord ++ tailWord_7833454).sum := by decide
  have hdescent : baseEnd_7833454 < baseStart_7833454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833530 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_7833530 : Nat := 118140960795 + 7833530 * 2 ^ 59
def prefixEnd_7833530 : Nat := 4983230072969 + 3 ^ 40 * 7833530 * 2
def baseEnd_7833530 : Nat := 1340788703804947170516419

theorem tailTrace_7833530 : CollatzResearch.WordTrace tailWord_7833530 prefixEnd_7833530 1340788703804947170516419 := by
  unfold tailWord_7833530
  simp only [CollatzResearch.WordTrace]
  refine ⟨71428077827616536314150511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190474874206977430171068029 71428077827616536314150511)
  ·
    refine ⟨107142116741424804471225767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71428077827616536314150511 107142116741424804471225767)
    ·
      refine ⟨160713175112137206706838651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107142116741424804471225767 160713175112137206706838651)
      ·
        refine ⟨241069762668205810060257977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160713175112137206706838651 241069762668205810060257977)
        ·
          refine ⟨180802322001154357545193483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241069762668205810060257977 180802322001154357545193483)
          ·
            refine ⟨271203483001731536317790225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180802322001154357545193483 271203483001731536317790225)
            ·
              refine ⟨203402612251298652238342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271203483001731536317790225 203402612251298652238342669)
              ·
                refine ⟨76275979594236994589378501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203402612251298652238342669 76275979594236994589378501)
                ·
                  refine ⟨14301746173919436485508469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76275979594236994589378501 14301746173919436485508469)
                  ·
                    refine ⟨1340788703804947170516419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14301746173919436485508469 1340788703804947170516419)
                    ·
                      rfl

theorem cell23_7833530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_7833530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833530 prefixEnd_7833530 := by exact prefixLift 7833530
  have htrace : WordTrace (prefixWord ++ tailWord_7833530) baseStart_7833530 baseEnd_7833530 := by
    simpa [prefixWord, tailWord_7833530, baseEnd_7833530] using wordTrace_append hprefix tailTrace_7833530
  have hstable : (prefixWord ++ tailWord_7833530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833530).length < 2 ^ (prefixWord ++ tailWord_7833530).sum := by decide
  have hdescent : baseEnd_7833530 < baseStart_7833530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833534 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_7833534 : Nat := 118140960795 + 7833534 * 2 ^ 59
def prefixEnd_7833534 : Nat := 4983230072969 + 3 ^ 40 * 7833534 * 2
def baseEnd_7833534 : Nat := 446929796148606610655471

theorem tailTrace_7833534 : CollatzResearch.WordTrace tailWord_7833534 prefixEnd_7833534 446929796148606610655471 := by
  unfold tailWord_7833534
  simp only [CollatzResearch.WordTrace]
  refine ⟨35714057150306456742468457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190474971468301102626498437 35714057150306456742468457)
  ·
    refine ⟨26785542862729842556851343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35714057150306456742468457 26785542862729842556851343)
    ·
      refine ⟨40178314294094763835277015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26785542862729842556851343 40178314294094763835277015)
      ·
        refine ⟨60267471441142145752915523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40178314294094763835277015 60267471441142145752915523)
        ·
          refine ⟨90401207161713218629373285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60267471441142145752915523 90401207161713218629373285)
          ·
            refine ⟨16950226342821228493007491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90401207161713218629373285 16950226342821228493007491)
            ·
              refine ⟨25425339514231842739511237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16950226342821228493007491 25425339514231842739511237)
              ·
                refine ⟨4767251158918470513658357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25425339514231842739511237 4767251158918470513658357)
                ·
                  refine ⟨446929796148606610655471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767251158918470513658357 446929796148606610655471)
                  ·
                    rfl

theorem cell23_7833534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_7833534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833534 prefixEnd_7833534 := by exact prefixLift 7833534
  have htrace : WordTrace (prefixWord ++ tailWord_7833534) baseStart_7833534 baseEnd_7833534 := by
    simpa [prefixWord, tailWord_7833534, baseEnd_7833534] using wordTrace_append hprefix tailTrace_7833534
  have hstable : (prefixWord ++ tailWord_7833534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833534).length < 2 ^ (prefixWord ++ tailWord_7833534).sum := by decide
  have hdescent : baseEnd_7833534 < baseStart_7833534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833567 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_7833567 : Nat := 118140960795 + 7833567 * 2 ^ 59
def prefixEnd_7833567 : Nat := 4983230072969 + 3 ^ 40 * 7833567 * 2
def baseEnd_7833567 : Nat := 4022385110199057866786587

theorem tailTrace_7833567 : CollatzResearch.WordTrace tailWord_7833567 prefixEnd_7833567 4022385110199057866786587 := by
  unfold tailWord_7833567
  simp only [CollatzResearch.WordTrace]
  refine ⟨285713660811332100575698955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190475773874221400383799303 285713660811332100575698955)
  ·
    refine ⟨428570491216998150863548433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285713660811332100575698955 428570491216998150863548433)
    ·
      refine ⟨321427868412748613147661325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428570491216998150863548433 321427868412748613147661325)
      ·
        refine ⟨120535450654780729930372997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321427868412748613147661325 120535450654780729930372997)
        ·
          refine ⟨22600396997771386861944937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120535450654780729930372997 22600396997771386861944937)
          ·
            refine ⟨16950297748328540146458703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22600396997771386861944937 16950297748328540146458703)
            ·
              refine ⟨25425446622492810219688055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16950297748328540146458703 25425446622492810219688055)
              ·
                refine ⟨38138169933739215329532083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25425446622492810219688055 38138169933739215329532083)
                ·
                  refine ⟨57207254900608822994298125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38138169933739215329532083 57207254900608822994298125)
                  ·
                    refine ⟨21452720587728308622861797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57207254900608822994298125 21452720587728308622861797)
                    ·
                      refine ⟨4022385110199057866786587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21452720587728308622861797 4022385110199057866786587)
                      ·
                        rfl

theorem cell23_7833567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_7833567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833567 prefixEnd_7833567 := by exact prefixLift 7833567
  have htrace : WordTrace (prefixWord ++ tailWord_7833567) baseStart_7833567 baseEnd_7833567 := by
    simpa [prefixWord, tailWord_7833567, baseEnd_7833567] using wordTrace_append hprefix tailTrace_7833567
  have hstable : (prefixWord ++ tailWord_7833567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833567).length < 2 ^ (prefixWord ++ tailWord_7833567).sum := by decide
  have hdescent : baseEnd_7833567 < baseStart_7833567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833580 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_7833580 : Nat := 118140960795 + 7833580 * 2 ^ 59
def prefixEnd_7833580 : Nat := 4983230072969 + 3 ^ 40 * 7833580 * 2
def baseEnd_7833580 : Nat := 4022391785447566315924027

theorem tailTrace_7833580 : CollatzResearch.WordTrace tailWord_7833580 prefixEnd_7833580 4022391785447566315924027 := by
  unfold tailWord_7833580
  simp only [CollatzResearch.WordTrace]
  refine ⟨142857067480142501897961097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190476089973523335863948129 142857067480142501897961097)
  ·
    refine ⟨107142800610106876423470823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142857067480142501897961097 107142800610106876423470823)
    ·
      refine ⟨160714200915160314635206235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107142800610106876423470823 160714200915160314635206235)
      ·
        refine ⟨241071301372740471952809353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160714200915160314635206235 241071301372740471952809353)
        ·
          refine ⟨180803476029555353964607015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241071301372740471952809353 180803476029555353964607015)
          ·
            refine ⟨271205214044333030946910523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180803476029555353964607015 271205214044333030946910523)
            ·
              refine ⟨406807821066499546420365785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271205214044333030946910523 406807821066499546420365785)
              ·
                refine ⟨305105865799874659815274339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406807821066499546420365785 305105865799874659815274339)
                ·
                  refine ⟨457658798699811989722911509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305105865799874659815274339 457658798699811989722911509)
                  ·
                    refine ⟨21452756189053687018261477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 457658798699811989722911509 21452756189053687018261477)
                    ·
                      refine ⟨4022391785447566315924027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21452756189053687018261477 4022391785447566315924027)
                      ·
                        rfl

theorem cell23_7833580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_7833580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833580 prefixEnd_7833580 := by exact prefixLift 7833580
  have htrace : WordTrace (prefixWord ++ tailWord_7833580) baseStart_7833580 baseEnd_7833580 := by
    simpa [prefixWord, tailWord_7833580, baseEnd_7833580] using wordTrace_append hprefix tailTrace_7833580
  have hstable : (prefixWord ++ tailWord_7833580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833580).length < 2 ^ (prefixWord ++ tailWord_7833580).sum := by decide
  have hdescent : baseEnd_7833580 < baseStart_7833580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833587 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3]
def baseStart_7833587 : Nat := 118140960795 + 7833587 * 2 ^ 59
def prefixEnd_7833587 : Nat := 4983230072969 + 3 ^ 40 * 7833587 * 2
def baseEnd_7833587 : Nat := 4022395379812147788536495

theorem tailTrace_7833587 : CollatzResearch.WordTrace tailWord_7833587 prefixEnd_7833587 4022395379812147788536495 := by
  unfold tailWord_7833587
  simp only [CollatzResearch.WordTrace]
  refine ⟨285714390271259643991427015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190476260180839762660951343 285714390271259643991427015)
  ·
    refine ⟨428571585406889465987140523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285714390271259643991427015 428571585406889465987140523)
    ·
      refine ⟨642857378110334198980710785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428571585406889465987140523 642857378110334198980710785)
      ·
        refine ⟨482143033582750649235533089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642857378110334198980710785 482143033582750649235533089)
        ·
          refine ⟨361607275187062986926649817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482143033582750649235533089 361607275187062986926649817)
          ·
            refine ⟨271205456390297240194987363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361607275187062986926649817 271205456390297240194987363)
            ·
              refine ⟨406808184585445860292481045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271205456390297240194987363 406808184585445860292481045)
              ·
                refine ⟨19069133652442774701210049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406808184585445860292481045 19069133652442774701210049)
                ·
                  refine ⟨14301850239332081025907537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19069133652442774701210049 14301850239332081025907537)
                  ·
                    refine ⟨10726387679499060769430653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14301850239332081025907537 10726387679499060769430653)
                    ·
                      refine ⟨4022395379812147788536495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726387679499060769430653 4022395379812147788536495)
                      ·
                        rfl

theorem cell23_7833587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_7833587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833587 prefixEnd_7833587 := by exact prefixLift 7833587
  have htrace : WordTrace (prefixWord ++ tailWord_7833587) baseStart_7833587 baseEnd_7833587 := by
    simpa [prefixWord, tailWord_7833587, baseEnd_7833587] using wordTrace_append hprefix tailTrace_7833587
  have hstable : (prefixWord ++ tailWord_7833587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833587).length < 2 ^ (prefixWord ++ tailWord_7833587).sum := by decide
  have hdescent : baseEnd_7833587 < baseStart_7833587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833628 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_7833628 : Nat := 118140960795 + 7833628 * 2 ^ 59
def prefixEnd_7833628 : Nat := 4983230072969 + 3 ^ 40 * 7833628 * 2
def baseEnd_7833628 : Nat := 1340805477506327376041269

theorem tailTrace_7833628 : CollatzResearch.WordTrace tailWord_7833628 prefixEnd_7833628 1340805477506327376041269 := by
  unfold tailWord_7833628
  simp only [CollatzResearch.WordTrace]
  refine ⟨142857942832055553996834769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190477257109407405329113025 142857942832055553996834769)
  ·
    refine ⟨107143457124041665497626077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142857942832055553996834769 107143457124041665497626077)
    ·
      refine ⟨40178796421515624561609779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107143457124041665497626077 40178796421515624561609779)
      ·
        refine ⟨60268194632273436842414669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40178796421515624561609779 60268194632273436842414669)
        ·
          refine ⟨22600572987102538815905501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60268194632273436842414669 22600572987102538815905501)
          ·
            refine ⟨8475214870163452055964563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22600572987102538815905501 8475214870163452055964563)
            ·
              refine ⟨12712822305245178083946845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475214870163452055964563 12712822305245178083946845)
              ·
                refine ⟨4767308364466941781480067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12712822305245178083946845 4767308364466941781480067)
                ·
                  refine ⟨7150962546700412672220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767308364466941781480067 7150962546700412672220101)
                  ·
                    refine ⟨1340805477506327376041269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150962546700412672220101 1340805477506327376041269)
                    ·
                      rfl

theorem cell23_7833628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_7833628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833628 prefixEnd_7833628 := by exact prefixLift 7833628
  have htrace : WordTrace (prefixWord ++ tailWord_7833628) baseStart_7833628 baseEnd_7833628 := by
    simpa [prefixWord, tailWord_7833628, baseEnd_7833628] using wordTrace_append hprefix tailTrace_7833628
  have hstable : (prefixWord ++ tailWord_7833628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833628).length < 2 ^ (prefixWord ++ tailWord_7833628).sum := by decide
  have hdescent : baseEnd_7833628 < baseStart_7833628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833651 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 1, 1, 3]
def baseStart_7833651 : Nat := 118140960795 + 7833651 * 2 ^ 59
def prefixEnd_7833651 : Nat := 4983230072969 + 3 ^ 40 * 7833651 * 2
def baseEnd_7833651 : Nat := 4022428242574035538136201

theorem tailTrace_7833651 : CollatzResearch.WordTrace tailWord_7833651 prefixEnd_7833651 4022428242574035538136201 := by
  unfold tailWord_7833651
  simp only [CollatzResearch.WordTrace]
  refine ⟨285716724543027782921756807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190477816362018521947837871 285716724543027782921756807)
  ·
    refine ⟨428575086814541674382635211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285716724543027782921756807 428575086814541674382635211)
    ·
      refine ⟨642862630221812511573952817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428575086814541674382635211 642862630221812511573952817)
      ·
        refine ⟨482146972666359383680464613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642862630221812511573952817 482146972666359383680464613)
        ·
          refine ⟨90402557374942384440087115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482146972666359383680464613 90402557374942384440087115)
          ·
            refine ⟨135603836062413576660130673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90402557374942384440087115 135603836062413576660130673)
            ·
              refine ⟨101702877046810182495098005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135603836062413576660130673 101702877046810182495098005)
              ·
                refine ⟨4767322361569227304457719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101702877046810182495098005 4767322361569227304457719)
                ·
                  refine ⟨7150983542353840956686579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767322361569227304457719 7150983542353840956686579)
                  ·
                    refine ⟨10726475313530761435029869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7150983542353840956686579 10726475313530761435029869)
                    ·
                      refine ⟨4022428242574035538136201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726475313530761435029869 4022428242574035538136201)
                      ·
                        rfl

theorem cell23_7833651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 1, 3].length) (baseStart_7833651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833651 prefixEnd_7833651 := by exact prefixLift 7833651
  have htrace : WordTrace (prefixWord ++ tailWord_7833651) baseStart_7833651 baseEnd_7833651 := by
    simpa [prefixWord, tailWord_7833651, baseEnd_7833651] using wordTrace_append hprefix tailTrace_7833651
  have hstable : (prefixWord ++ tailWord_7833651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833651).length < 2 ^ (prefixWord ++ tailWord_7833651).sum := by decide
  have hdescent : baseEnd_7833651 < baseStart_7833651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833654 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7833654 : Nat := 118140960795 + 7833654 * 2 ^ 59
def prefixEnd_7833654 : Nat := 4983230072969 + 3 ^ 40 * 7833654 * 2
def baseEnd_7833654 : Nat := 1340809927671999675466229

theorem tailTrace_7833654 : CollatzResearch.WordTrace tailWord_7833654 prefixEnd_7833654 1340809927671999675466229 := by
  unfold tailWord_7833654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857302122626057152132251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190477889308011276289410677 17857302122626057152132251)
  ·
    refine ⟨26785953183939085728198377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17857302122626057152132251 26785953183939085728198377)
    ·
      refine ⟨20089464887954314296148783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26785953183939085728198377 20089464887954314296148783)
      ·
        refine ⟨30134197331931471444223175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20089464887954314296148783 30134197331931471444223175)
        ·
          refine ⟨45201295997897207166334763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30134197331931471444223175 45201295997897207166334763)
          ·
            refine ⟨67801943996845810749502145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45201295997897207166334763 67801943996845810749502145)
            ·
              refine ⟨50851457997634358062126609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67801943996845810749502145 50851457997634358062126609)
              ·
                refine ⟨38138593498225768546594957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50851457997634358062126609 38138593498225768546594957)
                ·
                  refine ⟨14301972561834663204973109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38138593498225768546594957 14301972561834663204973109)
                  ·
                    refine ⟨1340809927671999675466229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14301972561834663204973109 1340809927671999675466229)
                    ·
                      rfl

theorem cell23_7833654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7833654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833654 prefixEnd_7833654 := by exact prefixLift 7833654
  have htrace : WordTrace (prefixWord ++ tailWord_7833654) baseStart_7833654 baseEnd_7833654 := by
    simpa [prefixWord, tailWord_7833654, baseEnd_7833654] using wordTrace_append hprefix tailTrace_7833654
  have hstable : (prefixWord ++ tailWord_7833654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833654).length < 2 ^ (prefixWord ++ tailWord_7833654).sum := by decide
  have hdescent : baseEnd_7833654 < baseStart_7833654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833667 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 6, 4]
def baseStart_7833667 : Nat := 118140960795 + 7833667 * 2 ^ 59
def prefixEnd_7833667 : Nat := 4983230072969 + 3 ^ 40 * 7833667 * 2
def baseEnd_7833667 : Nat := 1340812152754835825178709

theorem tailTrace_7833667 : CollatzResearch.WordTrace tailWord_7833667 prefixEnd_7833667 1340812152754835825178709 := by
  unfold tailWord_7833667
  simp only [CollatzResearch.WordTrace]
  refine ⟨285717308110969817654339255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190478205407313211769559503 285717308110969817654339255)
  ·
    refine ⟨428575962166454726481508883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285717308110969817654339255 428575962166454726481508883)
    ·
      refine ⟨642863943249682089722263325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428575962166454726481508883 642863943249682089722263325)
      ·
        refine ⟨241073978718630783645848747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642863943249682089722263325 241073978718630783645848747)
        ·
          refine ⟨361610968077946175468773121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241073978718630783645848747 361610968077946175468773121)
          ·
            refine ⟨271208226058459631601579841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361610968077946175468773121 271208226058459631601579841)
            ·
              refine ⟨203406169543844723701184881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271208226058459631601579841 203406169543844723701184881)
              ·
                refine ⟨152554627157883542775888661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203406169543844723701184881 152554627157883542775888661)
                ·
                  refine ⟨7150998148025791067619781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152554627157883542775888661 7150998148025791067619781)
                  ·
                    refine ⟨1340812152754835825178709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150998148025791067619781 1340812152754835825178709)
                    ·
                      rfl

theorem cell23_7833667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 4].length) (baseStart_7833667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833667 prefixEnd_7833667 := by exact prefixLift 7833667
  have htrace : WordTrace (prefixWord ++ tailWord_7833667) baseStart_7833667 baseEnd_7833667 := by
    simpa [prefixWord, tailWord_7833667, baseEnd_7833667] using wordTrace_append hprefix tailTrace_7833667
  have hstable : (prefixWord ++ tailWord_7833667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833667).length < 2 ^ (prefixWord ++ tailWord_7833667).sum := by decide
  have hdescent : baseEnd_7833667 < baseStart_7833667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833687 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7833687 : Nat := 118140960795 + 7833687 * 2 ^ 59
def prefixEnd_7833687 : Nat := 4983230072969 + 3 ^ 40 * 7833687 * 2
def baseEnd_7833687 : Nat := 4022446727877597397286035

theorem tailTrace_7833687 : CollatzResearch.WordTrace tailWord_7833687 prefixEnd_7833687 4022446727877597397286035 := by
  unfold tailWord_7833687
  simp only [CollatzResearch.WordTrace]
  refine ⟨285718037570897361070067315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190478691713931574046711543 285718037570897361070067315)
  ·
    refine ⟨428577056356346041605100973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285718037570897361070067315 428577056356346041605100973)
    ·
      refine ⟨160716396133629765601912865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428577056356346041605100973 160716396133629765601912865)
      ·
        refine ⟨120537297100222324201434649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160716396133629765601912865 120537297100222324201434649)
        ·
          refine ⟨90402972825166743151075987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120537297100222324201434649 90402972825166743151075987)
          ·
            refine ⟨135604459237750114726613981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90402972825166743151075987 135604459237750114726613981)
            ·
              refine ⟨50851672214156293022480243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135604459237750114726613981 50851672214156293022480243)
              ·
                refine ⟨76277508321234439533720365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50851672214156293022480243 76277508321234439533720365)
                ·
                  refine ⟨28604065620462914825145137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76277508321234439533720365 28604065620462914825145137)
                  ·
                    refine ⟨21453049215347186118858853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28604065620462914825145137 21453049215347186118858853)
                    ·
                      refine ⟨4022446727877597397286035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21453049215347186118858853 4022446727877597397286035)
                      ·
                        rfl

theorem cell23_7833687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7833687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833687 prefixEnd_7833687 := by exact prefixLift 7833687
  have htrace : WordTrace (prefixWord ++ tailWord_7833687) baseStart_7833687 baseEnd_7833687 := by
    simpa [prefixWord, tailWord_7833687, baseEnd_7833687] using wordTrace_append hprefix tailTrace_7833687
  have hstable : (prefixWord ++ tailWord_7833687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833687).length < 2 ^ (prefixWord ++ tailWord_7833687).sum := by decide
  have hdescent : baseEnd_7833687 < baseStart_7833687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833701 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_7833701 : Nat := 118140960795 + 7833701 * 2 ^ 59
def prefixEnd_7833701 : Nat := 4983230072969 + 3 ^ 40 * 7833701 * 2
def baseEnd_7833701 : Nat := 1340817972202253447503657

theorem tailTrace_7833701 : CollatzResearch.WordTrace tailWord_7833701 prefixEnd_7833701 1340817972202253447503657 := by
  unfold tailWord_7833701
  simp only [CollatzResearch.WordTrace]
  refine ⟨285718548192846641461076957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190479032128564427640717971 285718548192846641461076957)
  ·
    refine ⟨107144455572317490547903859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285718548192846641461076957 107144455572317490547903859)
    ·
      refine ⟨160716683358476235821855789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107144455572317490547903859 160716683358476235821855789)
      ·
        refine ⟨60268756259428588433195921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160716683358476235821855789 60268756259428588433195921)
        ·
          refine ⟨45201567194571441324896941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60268756259428588433195921 45201567194571441324896941)
          ·
            refine ⟨16950587697964290496836353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45201567194571441324896941 16950587697964290496836353)
            ·
              refine ⟨12712940773473217872627265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16950587697964290496836353 12712940773473217872627265)
              ·
                refine ⟨9534705580104913404470449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12712940773473217872627265 9534705580104913404470449)
                ·
                  refine ⟨7151029185078685053352837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9534705580104913404470449 7151029185078685053352837)
                  ·
                    refine ⟨1340817972202253447503657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151029185078685053352837 1340817972202253447503657)
                    ·
                      rfl

theorem cell23_7833701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_7833701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833701 prefixEnd_7833701 := by exact prefixLift 7833701
  have htrace : WordTrace (prefixWord ++ tailWord_7833701) baseStart_7833701 baseEnd_7833701 := by
    simpa [prefixWord, tailWord_7833701, baseEnd_7833701] using wordTrace_append hprefix tailTrace_7833701
  have hstable : (prefixWord ++ tailWord_7833701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833701).length < 2 ^ (prefixWord ++ tailWord_7833701).sum := by decide
  have hdescent : baseEnd_7833701 < baseStart_7833701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833714 : List Nat := [3, 2, 1, 2, 2, 4, 1, 8]
def baseStart_7833714 : Nat := 118140960795 + 7833714 * 2 ^ 59
def prefixEnd_7833714 : Nat := 4983230072969 + 3 ^ 40 * 7833714 * 2
def baseEnd_7833714 : Nat := 148980021920565510801793

theorem tailTrace_7833714 : CollatzResearch.WordTrace tailWord_7833714 prefixEnd_7833714 148980021920565510801793 := by
  unfold tailWord_7833714
  simp only [CollatzResearch.WordTrace]
  refine ⟨71429755585449886170325049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190479348227866363120866797 71429755585449886170325049)
  ·
    refine ⟨53572316689087414627743787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71429755585449886170325049 53572316689087414627743787)
    ·
      refine ⟨80358475033631121941615681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53572316689087414627743787 80358475033631121941615681)
      ·
        refine ⟨60268856275223341456211761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80358475033631121941615681 60268856275223341456211761)
        ·
          refine ⟨45201642206417506092158821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60268856275223341456211761 45201642206417506092158821)
          ·
            refine ⟨8475307913703282392279779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45201642206417506092158821 8475307913703282392279779)
            ·
              refine ⟨12712961870554923588419669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475307913703282392279779 12712961870554923588419669)
              ·
                refine ⟨148980021920565510801793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12712961870554923588419669 148980021920565510801793)
                ·
                  rfl

theorem cell23_7833714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_7833714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833714 prefixEnd_7833714 := by exact prefixLift 7833714
  have htrace : WordTrace (prefixWord ++ tailWord_7833714) baseStart_7833714 baseEnd_7833714 := by
    simpa [prefixWord, tailWord_7833714, baseEnd_7833714] using wordTrace_append hprefix tailTrace_7833714
  have hstable : (prefixWord ++ tailWord_7833714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833714).length < 2 ^ (prefixWord ++ tailWord_7833714).sum := by decide
  have hdescent : baseEnd_7833714 < baseStart_7833714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833724 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_7833724 : Nat := 118140960795 + 7833724 * 2 ^ 59
def prefixEnd_7833724 : Nat := 4983230072969 + 3 ^ 40 * 7833724 * 2
def baseEnd_7833724 : Nat := 4022465726661813752523365

theorem tailTrace_7833724 : CollatzResearch.WordTrace tailWord_7833724 prefixEnd_7833724 4022465726661813752523365 := by
  unfold tailWord_7833724
  simp only [CollatzResearch.WordTrace]
  refine ⟨142859693535881658194582113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190479591381175544259442817 142859693535881658194582113)
  ·
    refine ⟨107144770151911243645936585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142859693535881658194582113 107144770151911243645936585)
    ·
      refine ⟨80358577613933432734452439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107144770151911243645936585 80358577613933432734452439)
      ·
        refine ⟨120537866420900149101678659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80358577613933432734452439 120537866420900149101678659)
        ·
          refine ⟨180806799631350223652517989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120537866420900149101678659 180806799631350223652517989)
          ·
            refine ⟨33901274930878166934847123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180806799631350223652517989 33901274930878166934847123)
            ·
              refine ⟨50851912396317250402270685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33901274930878166934847123 50851912396317250402270685)
              ·
                refine ⟨19069467148618968900851507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50851912396317250402270685 19069467148618968900851507)
                ·
                  refine ⟨28604200722928453351277261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19069467148618968900851507 28604200722928453351277261)
                  ·
                    refine ⟨10726575271098170006728973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28604200722928453351277261 10726575271098170006728973)
                    ·
                      refine ⟨4022465726661813752523365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726575271098170006728973 4022465726661813752523365)
                      ·
                        rfl

theorem cell23_7833724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_7833724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833724 prefixEnd_7833724 := by exact prefixLift 7833724
  have htrace : WordTrace (prefixWord ++ tailWord_7833724) baseStart_7833724 baseEnd_7833724 := by
    simpa [prefixWord, tailWord_7833724, baseEnd_7833724] using wordTrace_append hprefix tailTrace_7833724
  have hstable : (prefixWord ++ tailWord_7833724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833724).length < 2 ^ (prefixWord ++ tailWord_7833724).sum := by decide
  have hdescent : baseEnd_7833724 < baseStart_7833724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833737 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_7833737 : Nat := 118140960795 + 7833737 * 2 ^ 59
def prefixEnd_7833737 : Nat := 4983230072969 + 3 ^ 40 * 7833737 * 2
def baseEnd_7833737 : Nat := 4022472401910322201660805

theorem tailTrace_7833737 : CollatzResearch.WordTrace tailWord_7833737 prefixEnd_7833737 4022472401910322201660805 := by
  unfold tailWord_7833737
  simp only [CollatzResearch.WordTrace]
  refine ⟨285719861220716219609387465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190479907480477479739591643 285719861220716219609387465)
  ·
    refine ⟨214289895915537164707040599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285719861220716219609387465 214289895915537164707040599)
    ·
      refine ⟨321434843873305747060560899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214289895915537164707040599 321434843873305747060560899)
      ·
        refine ⟨482152265809958620590841349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321434843873305747060560899 482152265809958620590841349)
        ·
          refine ⟨90403549839367241360782753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482152265809958620590841349 90403549839367241360782753)
          ·
            refine ⟨67802662379525431020587065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90403549839367241360782753 67802662379525431020587065)
            ·
              refine ⟨50851996784644073265440299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67802662379525431020587065 50851996784644073265440299)
              ·
                refine ⟨76277995176966109898160449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50851996784644073265440299 76277995176966109898160449)
                ·
                  refine ⟨57208496382724582423620337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76277995176966109898160449 57208496382724582423620337)
                  ·
                    refine ⟨42906372287043436817715253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57208496382724582423620337 42906372287043436817715253)
                    ·
                      refine ⟨4022472401910322201660805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42906372287043436817715253 4022472401910322201660805)
                      ·
                        rfl

theorem cell23_7833737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_7833737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833737 prefixEnd_7833737 := by exact prefixLift 7833737
  have htrace : WordTrace (prefixWord ++ tailWord_7833737) baseStart_7833737 baseEnd_7833737 := by
    simpa [prefixWord, tailWord_7833737, baseEnd_7833737] using wordTrace_append hprefix tailTrace_7833737
  have hstable : (prefixWord ++ tailWord_7833737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833737).length < 2 ^ (prefixWord ++ tailWord_7833737).sum := by decide
  have hdescent : baseEnd_7833737 < baseStart_7833737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833742 : List Nat := [4, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7833742 : Nat := 118140960795 + 7833742 * 2 ^ 59
def prefixEnd_7833742 : Nat := 4983230072969 + 3 ^ 40 * 7833742 * 2
def baseEnd_7833742 : Nat := 4022474969313594682098283

theorem tailTrace_7833742 : CollatzResearch.WordTrace tailWord_7833742 prefixEnd_7833742 4022474969313594682098283 := by
  unfold tailWord_7833742
  simp only [CollatzResearch.WordTrace]
  refine ⟨35715005448212263182914935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190480029057132070308879653 35715005448212263182914935)
  ·
    refine ⟨53572508172318394774372403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35715005448212263182914935 53572508172318394774372403)
    ·
      refine ⟨80358762258477592161558605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53572508172318394774372403 80358762258477592161558605)
      ·
        refine ⟨30134535846929097060584477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80358762258477592161558605 30134535846929097060584477)
        ·
          refine ⟨11300450942598411397719179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30134535846929097060584477 11300450942598411397719179)
          ·
            refine ⟨16950676413897617096578769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11300450942598411397719179 16950676413897617096578769)
            ·
              refine ⟨12713007310423212822434077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16950676413897617096578769 12713007310423212822434077)
              ·
                refine ⟨4767377741408704808412779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12713007310423212822434077 4767377741408704808412779)
                ·
                  refine ⟨7151066612113057212619169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767377741408704808412779 7151066612113057212619169)
                  ·
                    refine ⟨5363299959084792909464377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151066612113057212619169 5363299959084792909464377)
                    ·
                      refine ⟨4022474969313594682098283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363299959084792909464377 4022474969313594682098283)
                      ·
                        rfl

theorem cell23_7833742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7833742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833742 prefixEnd_7833742 := by exact prefixLift 7833742
  have htrace : WordTrace (prefixWord ++ tailWord_7833742) baseStart_7833742 baseEnd_7833742 := by
    simpa [prefixWord, tailWord_7833742, baseEnd_7833742] using wordTrace_append hprefix tailTrace_7833742
  have hstable : (prefixWord ++ tailWord_7833742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833742).length < 2 ^ (prefixWord ++ tailWord_7833742).sum := by decide
  have hdescent : baseEnd_7833742 < baseStart_7833742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833787 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 7]
def baseStart_7833787 : Nat := 118140960795 + 7833787 * 2 ^ 59
def prefixEnd_7833787 : Nat := 4983230072969 + 3 ^ 40 * 7833787 * 2
def baseEnd_7833787 : Nat := 446944230660338556226175

theorem tailTrace_7833787 : CollatzResearch.WordTrace tailWord_7833787 prefixEnd_7833787 446944230660338556226175 := by
  unfold tailWord_7833787
  simp only [CollatzResearch.WordTrace]
  refine ⟨285721684870535078148707615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190481123247023385432471743 285721684870535078148707615)
  ·
    refine ⟨428582527305802617223061423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285721684870535078148707615 428582527305802617223061423)
    ·
      refine ⟨642873790958703925834592135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428582527305802617223061423 642873790958703925834592135)
      ·
        refine ⟨964310686438055888751888203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642873790958703925834592135 964310686438055888751888203)
        ·
          refine ⟨1446466029657083833127832305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964310686438055888751888203 1446466029657083833127832305)
          ·
            refine ⟨1084849522242812874845874229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446466029657083833127832305 1084849522242812874845874229)
            ·
              refine ⟨101704642710263707016800709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1084849522242812874845874229 101704642710263707016800709)
              ·
                refine ⟨19069620508174445065650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101704642710263707016800709 19069620508174445065650133)
                ·
                  refine ⟨446944230660338556226175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19069620508174445065650133 446944230660338556226175)
                  ·
                    rfl

theorem cell23_7833787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 7].length) (baseStart_7833787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833787 prefixEnd_7833787 := by exact prefixLift 7833787
  have htrace : WordTrace (prefixWord ++ tailWord_7833787) baseStart_7833787 baseEnd_7833787 := by
    simpa [prefixWord, tailWord_7833787, baseEnd_7833787] using wordTrace_append hprefix tailTrace_7833787
  have hstable : (prefixWord ++ tailWord_7833787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833787).length < 2 ^ (prefixWord ++ tailWord_7833787).sum := by decide
  have hdescent : baseEnd_7833787 < baseStart_7833787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833821 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 7]
def baseStart_7833821 : Nat := 118140960795 + 7833821 * 2 ^ 59
def prefixEnd_7833821 : Nat := 4983230072969 + 3 ^ 40 * 7833821 * 2
def baseEnd_7833821 : Nat := 446946170476144430334491

theorem tailTrace_7833821 : CollatzResearch.WordTrace tailWord_7833821 prefixEnd_7833821 446946170476144430334491 := by
  unfold tailWord_7833821
  simp only [CollatzResearch.WordTrace]
  refine ⟨285722924952411901955445317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190481949968274601303630211 285722924952411901955445317)
  ·
    refine ⟨53573048428577231616645997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285722924952411901955445317 53573048428577231616645997)
    ·
      refine ⟨20089893160716461856242249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53573048428577231616645997 20089893160716461856242249)
      ·
        refine ⟨15067419870537346392181687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20089893160716461856242249 15067419870537346392181687)
        ·
          refine ⟨22601129805806019588272531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067419870537346392181687 22601129805806019588272531)
          ·
            refine ⟨33901694708709029382408797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22601129805806019588272531 33901694708709029382408797)
            ·
              refine ⟨12713135515765886018403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33901694708709029382408797 12713135515765886018403299)
              ·
                refine ⟨19069703273648829027604949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713135515765886018403299 19069703273648829027604949)
                ·
                  refine ⟨446946170476144430334491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19069703273648829027604949 446946170476144430334491)
                  ·
                    rfl

theorem cell23_7833821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_7833821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833821 prefixEnd_7833821 := by exact prefixLift 7833821
  have htrace : WordTrace (prefixWord ++ tailWord_7833821) baseStart_7833821 baseEnd_7833821 := by
    simpa [prefixWord, tailWord_7833821, baseEnd_7833821] using wordTrace_append hprefix tailTrace_7833821
  have hstable : (prefixWord ++ tailWord_7833821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833821).length < 2 ^ (prefixWord ++ tailWord_7833821).sum := by decide
  have hdescent : baseEnd_7833821 < baseStart_7833821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833826 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7833826 : Nat := 118140960795 + 7833826 * 2 ^ 59
def prefixEnd_7833826 : Nat := 4983230072969 + 3 ^ 40 * 7833826 * 2
def baseEnd_7833826 : Nat := 4022518101688572353447897

theorem tailTrace_7833826 : CollatzResearch.WordTrace tailWord_7833826 prefixEnd_7833826 4022518101688572353447897 := by
  unfold tailWord_7833826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71430776829348446952344333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190482071544929191872918221 71430776829348446952344333)
  ·
    refine ⟨26786541311005667607129125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71430776829348446952344333 26786541311005667607129125)
    ·
      refine ⟨5022476495813562676336711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26786541311005667607129125 5022476495813562676336711)
      ·
        refine ⟨7533714743720344014505067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022476495813562676336711 7533714743720344014505067)
        ·
          refine ⟨11300572115580516021757601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533714743720344014505067 11300572115580516021757601)
          ·
            refine ⟨8475429086685387016318201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11300572115580516021757601 8475429086685387016318201)
            ·
              refine ⟨6356571815014040262238651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475429086685387016318201 6356571815014040262238651)
              ·
                refine ⟨9534857722521060393357977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356571815014040262238651 9534857722521060393357977)
                ·
                  refine ⟨7151143291890795295018483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9534857722521060393357977 7151143291890795295018483)
                  ·
                    refine ⟨10726714937836192942527725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151143291890795295018483 10726714937836192942527725)
                    ·
                      refine ⟨4022518101688572353447897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726714937836192942527725 4022518101688572353447897)
                      ·
                        rfl

theorem cell23_7833826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7833826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833826 prefixEnd_7833826 := by exact prefixLift 7833826
  have htrace : WordTrace (prefixWord ++ tailWord_7833826) baseStart_7833826 baseEnd_7833826 := by
    simpa [prefixWord, tailWord_7833826, baseEnd_7833826] using wordTrace_append hprefix tailTrace_7833826
  have hstable : (prefixWord ++ tailWord_7833826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833826).length < 2 ^ (prefixWord ++ tailWord_7833826).sum := by decide
  have hdescent : baseEnd_7833826 < baseStart_7833826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833832 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7833832 : Nat := 118140960795 + 7833832 * 2 ^ 59
def prefixEnd_7833832 : Nat := 4983230072969 + 3 ^ 40 * 7833832 * 2
def baseEnd_7833832 : Nat := 4022521182572499329972869

theorem tailTrace_7833832 : CollatzResearch.WordTrace tailWord_7833832 prefixEnd_7833832 4022521182572499329972869 := by
  unfold tailWord_7833832
  simp only [CollatzResearch.WordTrace]
  refine ⟨142861663077686025417047875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190482217436914700556063833 142861663077686025417047875)
  ·
    refine ⟨214292494616529038125571813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142861663077686025417047875 214292494616529038125571813)
    ·
      refine ⟨40179842740599194648544715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214292494616529038125571813 40179842740599194648544715)
      ·
        refine ⟨60269764110898791972817073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40179842740599194648544715 60269764110898791972817073)
        ·
          refine ⟨45202323083174093979612805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60269764110898791972817073 45202323083174093979612805)
          ·
            refine ⟨8475435578095142621177401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45202323083174093979612805 8475435578095142621177401)
            ·
              refine ⟨6356576683571356965883051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475435578095142621177401 6356576683571356965883051)
              ·
                refine ⟨9534865025357035448824577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356576683571356965883051 9534865025357035448824577)
                ·
                  refine ⟨7151148769017776586618433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9534865025357035448824577 7151148769017776586618433)
                  ·
                    refine ⟨5363361576763332439963825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151148769017776586618433 5363361576763332439963825)
                    ·
                      refine ⟨4022521182572499329972869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363361576763332439963825 4022521182572499329972869)
                      ·
                        rfl

theorem cell23_7833832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7833832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833832 prefixEnd_7833832 := by exact prefixLift 7833832
  have htrace : WordTrace (prefixWord ++ tailWord_7833832) baseStart_7833832 baseEnd_7833832 := by
    simpa [prefixWord, tailWord_7833832, baseEnd_7833832] using wordTrace_append hprefix tailTrace_7833832
  have hstable : (prefixWord ++ tailWord_7833832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833832).length < 2 ^ (prefixWord ++ tailWord_7833832).sum := by decide
  have hdescent : baseEnd_7833832 < baseStart_7833832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833834 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_7833834 : Nat := 118140960795 + 7833834 * 2 ^ 59
def prefixEnd_7833834 : Nat := 4983230072969 + 3 ^ 40 * 7833834 * 2
def baseEnd_7833834 : Nat := 1340840736511269440715953

theorem tailTrace_7833834 : CollatzResearch.WordTrace tailWord_7833834 prefixEnd_7833834 1340840736511269440715953 := by
  unfold tailWord_7833834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71430849775341201293917139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190482266067576536783779037 71430849775341201293917139)
  ·
    refine ⟨107146274663011801940875709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71430849775341201293917139 107146274663011801940875709)
    ·
      refine ⟨40179852998629425727828391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107146274663011801940875709 40179852998629425727828391)
      ·
        refine ⟨60269779497944138591742587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40179852998629425727828391 60269779497944138591742587)
        ·
          refine ⟨90404669246916207887613881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60269779497944138591742587 90404669246916207887613881)
          ·
            refine ⟨67803501935187155915710411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90404669246916207887613881 67803501935187155915710411)
            ·
              refine ⟨101705252902780733873565617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67803501935187155915710411 101705252902780733873565617)
              ·
                refine ⟨76278939677085550405174213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101705252902780733873565617 76278939677085550405174213)
                ·
                  refine ⟨14302301189453540700970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76278939677085550405174213 14302301189453540700970165)
                  ·
                    refine ⟨1340840736511269440715953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14302301189453540700970165 1340840736511269440715953)
                    ·
                      rfl

theorem cell23_7833834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_7833834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833834 prefixEnd_7833834 := by exact prefixLift 7833834
  have htrace : WordTrace (prefixWord ++ tailWord_7833834) baseStart_7833834 baseEnd_7833834 := by
    simpa [prefixWord, tailWord_7833834, baseEnd_7833834] using wordTrace_append hprefix tailTrace_7833834
  have hstable : (prefixWord ++ tailWord_7833834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833834).length < 2 ^ (prefixWord ++ tailWord_7833834).sum := by decide
  have hdescent : baseEnd_7833834 < baseStart_7833834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833884 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7833884 : Nat := 118140960795 + 7833884 * 2 ^ 59
def prefixEnd_7833884 : Nat := 4983230072969 + 3 ^ 40 * 7833884 * 2
def baseEnd_7833884 : Nat := 4022547883566533126522629

theorem tailTrace_7833884 : CollatzResearch.WordTrace tailWord_7833884 prefixEnd_7833884 4022547883566533126522629 := by
  unfold tailWord_7833884
  simp only [CollatzResearch.WordTrace]
  refine ⟨142862611375591831857494353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190483481834122442476659137 142862611375591831857494353)
  ·
    refine ⟨107146958531693873893120765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142862611375591831857494353 107146958531693873893120765)
    ·
      refine ⟨40180109449385202709920287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107146958531693873893120765 40180109449385202709920287)
      ·
        refine ⟨60270164174077804064880431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40180109449385202709920287 60270164174077804064880431)
        ·
          refine ⟨90405246261116706097320647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60270164174077804064880431 90405246261116706097320647)
          ·
            refine ⟨135607869391675059145980971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90405246261116706097320647 135607869391675059145980971)
            ·
              refine ⟨203411804087512588718971457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135607869391675059145980971 203411804087512588718971457)
              ·
                refine ⟨152558853065634441539228593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203411804087512588718971457 152558853065634441539228593)
                ·
                  refine ⟨114419139799225831154421445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152558853065634441539228593 114419139799225831154421445)
                  ·
                    refine ⟨21453588712354843341454021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114419139799225831154421445 21453588712354843341454021)
                    ·
                      refine ⟨4022547883566533126522629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21453588712354843341454021 4022547883566533126522629)
                      ·
                        rfl

theorem cell23_7833884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7833884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833884 prefixEnd_7833884 := by exact prefixLift 7833884
  have htrace : WordTrace (prefixWord ++ tailWord_7833884) baseStart_7833884 baseEnd_7833884 := by
    simpa [prefixWord, tailWord_7833884, baseEnd_7833884] using wordTrace_append hprefix tailTrace_7833884
  have hstable : (prefixWord ++ tailWord_7833884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833884).length < 2 ^ (prefixWord ++ tailWord_7833884).sum := by decide
  have hdescent : baseEnd_7833884 < baseStart_7833884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833888 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7833888 : Nat := 118140960795 + 7833888 * 2 ^ 59
def prefixEnd_7833888 : Nat := 4983230072969 + 3 ^ 40 * 7833888 * 2
def baseEnd_7833888 : Nat := 4022549937489151110872611

theorem tailTrace_7833888 : CollatzResearch.WordTrace tailWord_7833888 prefixEnd_7833888 4022549937489151110872611 := by
  unfold tailWord_7833888
  simp only [CollatzResearch.WordTrace]
  refine ⟨142862684321584586199067159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190483579095446114932089545 142862684321584586199067159)
  ·
    refine ⟨214294026482376879298600739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142862684321584586199067159 214294026482376879298600739)
    ·
      refine ⟨321441039723565318947901109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214294026482376879298600739 321441039723565318947901109)
      ·
        refine ⟨30135097474084248651365729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321441039723565318947901109 30135097474084248651365729)
        ·
          refine ⟨22601323105563186488524297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30135097474084248651365729 22601323105563186488524297)
          ·
            refine ⟨16950992329172389866393223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22601323105563186488524297 16950992329172389866393223)
            ·
              refine ⟨25426488493758584799589835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16950992329172389866393223 25426488493758584799589835)
              ·
                refine ⟨38139732740637877199384753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25426488493758584799589835 38139732740637877199384753)
                ·
                  refine ⟨28604799555478407899538565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38139732740637877199384753 28604799555478407899538565)
                  ·
                    refine ⟨5363399916652201481163481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28604799555478407899538565 5363399916652201481163481)
                    ·
                      refine ⟨4022549937489151110872611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363399916652201481163481 4022549937489151110872611)
                      ·
                        rfl

theorem cell23_7833888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7833888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833888 prefixEnd_7833888 := by exact prefixLift 7833888
  have htrace : WordTrace (prefixWord ++ tailWord_7833888) baseStart_7833888 baseEnd_7833888 := by
    simpa [prefixWord, tailWord_7833888, baseEnd_7833888] using wordTrace_append hprefix tailTrace_7833888
  have hstable : (prefixWord ++ tailWord_7833888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833888).length < 2 ^ (prefixWord ++ tailWord_7833888).sum := by decide
  have hdescent : baseEnd_7833888 < baseStart_7833888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833902 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7833902 : Nat := 118140960795 + 7833902 * 2 ^ 59
def prefixEnd_7833902 : Nat := 4983230072969 + 3 ^ 40 * 7833902 * 2
def baseEnd_7833902 : Nat := 1340852375406104685365849

theorem tailTrace_7833902 : CollatzResearch.WordTrace tailWord_7833902 prefixEnd_7833902 1340852375406104685365849 := by
  unfold tailWord_7833902
  simp only [CollatzResearch.WordTrace]
  refine ⟨35715734908139806598642995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190483919510078968526095973 35715734908139806598642995)
  ·
    refine ⟨53573602362209709897964493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35715734908139806598642995 53573602362209709897964493)
    ·
      refine ⟨20090100885828641211736685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53573602362209709897964493 20090100885828641211736685)
      ·
        refine ⟨7533787832185740454401257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20090100885828641211736685 7533787832185740454401257)
        ·
          refine ⟨5650340874139305340800943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7533787832185740454401257 5650340874139305340800943)
          ·
            refine ⟨8475511311208958011201415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650340874139305340800943 8475511311208958011201415)
            ·
              refine ⟨12713266966813437016802123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475511311208958011201415 12713266966813437016802123)
              ·
                refine ⟨19069900450220155525203185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713266966813437016802123 19069900450220155525203185)
                ·
                  refine ⟨14302425337665116643902389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19069900450220155525203185 14302425337665116643902389)
                  ·
                    refine ⟨1340852375406104685365849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14302425337665116643902389 1340852375406104685365849)
                    ·
                      rfl

theorem cell23_7833902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7833902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833902 prefixEnd_7833902 := by exact prefixLift 7833902
  have htrace : WordTrace (prefixWord ++ tailWord_7833902) baseStart_7833902 baseEnd_7833902 := by
    simpa [prefixWord, tailWord_7833902, baseEnd_7833902] using wordTrace_append hprefix tailTrace_7833902
  have hstable : (prefixWord ++ tailWord_7833902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833902).length < 2 ^ (prefixWord ++ tailWord_7833902).sum := by decide
  have hdescent : baseEnd_7833902 < baseStart_7833902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833904 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_7833904 : Nat := 118140960795 + 7833904 * 2 ^ 59
def prefixEnd_7833904 : Nat := 4983230072969 + 3 ^ 40 * 7833904 * 2
def baseEnd_7833904 : Nat := 4022558153179623048272537

theorem tailTrace_7833904 : CollatzResearch.WordTrace tailWord_7833904 prefixEnd_7833904 4022558153179623048272537 := by
  unfold tailWord_7833904
  simp only [CollatzResearch.WordTrace]
  refine ⟨142862976105555603565358383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190483968140740804753811177 142862976105555603565358383)
  ·
    refine ⟨214294464158333405348037575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142862976105555603565358383 214294464158333405348037575)
    ·
      refine ⟨321441696237500108022056363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214294464158333405348037575 321441696237500108022056363)
      ·
        refine ⟨482162544356250162033084545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321441696237500108022056363 482162544356250162033084545)
        ·
          refine ⟨361621908267187621524813409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482162544356250162033084545 361621908267187621524813409)
          ·
            refine ⟨271216431200390716143610057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361621908267187621524813409 271216431200390716143610057)
            ·
              refine ⟨203412323400293037107707543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271216431200390716143610057 203412323400293037107707543)
              ·
                refine ⟨305118485100439555661561315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203412323400293037107707543 305118485100439555661561315)
                ·
                  refine ⟨457677727650659333492341973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305118485100439555661561315 457677727650659333492341973)
                  ·
                    refine ⟨10726821741812328128726765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 457677727650659333492341973 10726821741812328128726765)
                    ·
                      refine ⟨4022558153179623048272537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726821741812328128726765 4022558153179623048272537)
                      ·
                        rfl

theorem cell23_7833904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_7833904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833904 prefixEnd_7833904 := by exact prefixLift 7833904
  have htrace : WordTrace (prefixWord ++ tailWord_7833904) baseStart_7833904 baseEnd_7833904 := by
    simpa [prefixWord, tailWord_7833904, baseEnd_7833904] using wordTrace_append hprefix tailTrace_7833904
  have hstable : (prefixWord ++ tailWord_7833904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833904).length < 2 ^ (prefixWord ++ tailWord_7833904).sum := by decide
  have hdescent : baseEnd_7833904 < baseStart_7833904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833905 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_7833905 : Nat := 118140960795 + 7833905 * 2 ^ 59
def prefixEnd_7833905 : Nat := 4983230072969 + 3 ^ 40 * 7833905 * 2
def baseEnd_7833905 : Nat := 4022558666660277544360033

theorem tailTrace_7833905 : CollatzResearch.WordTrace tailWord_7833905 prefixEnd_7833905 4022558666660277544360033 := by
  unfold tailWord_7833905
  simp only [CollatzResearch.WordTrace]
  refine ⟨285725988684107584301503169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190483992456071722867668779 285725988684107584301503169)
  ·
    refine ⟨214294491513080688226127377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285725988684107584301503169 214294491513080688226127377)
    ·
      refine ⟨160720868634810516169595533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214294491513080688226127377 160720868634810516169595533)
      ·
        refine ⟨60270325738053943563598325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160720868634810516169595533 60270325738053943563598325)
        ·
          refine ⟨5650343037942557209087343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60270325738053943563598325 5650343037942557209087343)
          ·
            refine ⟨8475514556913835813631015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650343037942557209087343 8475514556913835813631015)
            ·
              refine ⟨12713271835370753720446523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475514556913835813631015 12713271835370753720446523)
              ·
                refine ⟨19069907753056130580669785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713271835370753720446523 19069907753056130580669785)
                ·
                  refine ⟨14302430814792097935502339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19069907753056130580669785 14302430814792097935502339)
                  ·
                    refine ⟨21453646222188146903253509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14302430814792097935502339 21453646222188146903253509)
                    ·
                      refine ⟨4022558666660277544360033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21453646222188146903253509 4022558666660277544360033)
                      ·
                        rfl

theorem cell23_7833905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_7833905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833905 prefixEnd_7833905 := by exact prefixLift 7833905
  have htrace : WordTrace (prefixWord ++ tailWord_7833905) baseStart_7833905 baseEnd_7833905 := by
    simpa [prefixWord, tailWord_7833905, baseEnd_7833905] using wordTrace_append hprefix tailTrace_7833905
  have hstable : (prefixWord ++ tailWord_7833905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833905).length < 2 ^ (prefixWord ++ tailWord_7833905).sum := by decide
  have hdescent : baseEnd_7833905 < baseStart_7833905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833908 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_7833908 : Nat := 118140960795 + 7833908 * 2 ^ 59
def prefixEnd_7833908 : Nat := 4983230072969 + 3 ^ 40 * 7833908 * 2
def baseEnd_7833908 : Nat := 4022560207102241032622519

theorem tailTrace_7833908 : CollatzResearch.WordTrace tailWord_7833908 prefixEnd_7833908 4022560207102241032622519 := by
  unfold tailWord_7833908
  simp only [CollatzResearch.WordTrace]
  refine ⟨142863049051548357906931189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190484065402064477209241585 142863049051548357906931189)
  ·
    refine ⟨13393410848582658553774799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142863049051548357906931189 13393410848582658553774799)
    ·
      refine ⟨20090116272873987830662199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13393410848582658553774799 20090116272873987830662199)
      ·
        refine ⟨30135174409310981745993299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20090116272873987830662199 30135174409310981745993299)
        ·
          refine ⟨45202761613966472618989949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30135174409310981745993299 45202761613966472618989949)
          ·
            refine ⟨16951035605237427232121231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45202761613966472618989949 16951035605237427232121231)
            ·
              refine ⟨25426553407856140848181847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16951035605237427232121231 25426553407856140848181847)
              ·
                refine ⟨38139830111784211272272771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25426553407856140848181847 38139830111784211272272771)
                ·
                  refine ⟨57209745167676316908409157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38139830111784211272272771 57209745167676316908409157)
                  ·
                    refine ⟨10726827218939309420326717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57209745167676316908409157 10726827218939309420326717)
                    ·
                      refine ⟨4022560207102241032622519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726827218939309420326717 4022560207102241032622519)
                      ·
                        rfl

theorem cell23_7833908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_7833908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833908 prefixEnd_7833908 := by exact prefixLift 7833908
  have htrace : WordTrace (prefixWord ++ tailWord_7833908) baseStart_7833908 baseEnd_7833908 := by
    simpa [prefixWord, tailWord_7833908, baseEnd_7833908] using wordTrace_append hprefix tailTrace_7833908
  have hstable : (prefixWord ++ tailWord_7833908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833908).length < 2 ^ (prefixWord ++ tailWord_7833908).sum := by decide
  have hdescent : baseEnd_7833908 < baseStart_7833908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833934 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7833934 : Nat := 118140960795 + 7833934 * 2 ^ 59
def prefixEnd_7833934 : Nat := 4983230072969 + 3 ^ 40 * 7833934 * 2
def baseEnd_7833934 : Nat := 4022573557599257930897399

theorem tailTrace_7833934 : CollatzResearch.WordTrace tailWord_7833934 prefixEnd_7833934 4022573557599257930897399 := by
  unfold tailWord_7833934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35715880800125315281788607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190484697600668348169539237 35715880800125315281788607)
  ·
    refine ⟨53573821200187972922682911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35715880800125315281788607 53573821200187972922682911)
    ·
      refine ⟨80360731800281959384024367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53573821200187972922682911 80360731800281959384024367)
      ·
        refine ⟨120541097700422939076036551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80360731800281959384024367 120541097700422939076036551)
        ·
          refine ⟨180811646550634408614054827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120541097700422939076036551 180811646550634408614054827)
          ·
            refine ⟨271217469825951612921082241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180811646550634408614054827 271217469825951612921082241)
            ·
              refine ⟨203413102369463709690811681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271217469825951612921082241 203413102369463709690811681)
              ·
                refine ⟨152559826777097782268108761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203413102369463709690811681 152559826777097782268108761)
                ·
                  refine ⟨114419870082823336701081571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152559826777097782268108761 114419870082823336701081571)
                  ·
                    refine ⟨171629805124235005051622357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114419870082823336701081571 171629805124235005051622357)
                    ·
                      refine ⟨4022573557599257930897399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171629805124235005051622357 4022573557599257930897399)
                      ·
                        rfl

theorem cell23_7833934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7833934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833934 prefixEnd_7833934 := by exact prefixLift 7833934
  have htrace : WordTrace (prefixWord ++ tailWord_7833934) baseStart_7833934 baseEnd_7833934 := by
    simpa [prefixWord, tailWord_7833934, baseEnd_7833934] using wordTrace_append hprefix tailTrace_7833934
  have hstable : (prefixWord ++ tailWord_7833934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833934).length < 2 ^ (prefixWord ++ tailWord_7833934).sum := by decide
  have hdescent : baseEnd_7833934 < baseStart_7833934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833938 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_7833938 : Nat := 118140960795 + 7833938 * 2 ^ 59
def prefixEnd_7833938 : Nat := 4983230072969 + 3 ^ 40 * 7833938 * 2
def baseEnd_7833938 : Nat := 4022575611521875915247381

theorem tailTrace_7833938 : CollatzResearch.WordTrace tailWord_7833938 prefixEnd_7833938 4022575611521875915247381 := by
  unfold tailWord_7833938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71431798073247007734363617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190484794861992020624969645 71431798073247007734363617)
  ·
    refine ⟨53573848554935255800772713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71431798073247007734363617 53573848554935255800772713)
    ·
      refine ⟨40180386416201441850579535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53573848554935255800772713 40180386416201441850579535)
      ·
        refine ⟨60270579624302162775869303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40180386416201441850579535 60270579624302162775869303)
        ·
          refine ⟨90405869436453244163803955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60270579624302162775869303 90405869436453244163803955)
          ·
            refine ⟨135608804154679866245705933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90405869436453244163803955 135608804154679866245705933)
            ·
              refine ⟨50853301558004949842139725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135608804154679866245705933 50853301558004949842139725)
              ·
                refine ⟨19069988084251856190802397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50853301558004949842139725 19069988084251856190802397)
                ·
                  refine ⟨7151245531594446071550899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19069988084251856190802397 7151245531594446071550899)
                  ·
                    refine ⟨10726868297391669107326349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151245531594446071550899 10726868297391669107326349)
                    ·
                      refine ⟨4022575611521875915247381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10726868297391669107326349 4022575611521875915247381)
                      ·
                        rfl

theorem cell23_7833938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_7833938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833938 prefixEnd_7833938 := by exact prefixLift 7833938
  have htrace : WordTrace (prefixWord ++ tailWord_7833938) baseStart_7833938 baseEnd_7833938 := by
    simpa [prefixWord, tailWord_7833938, baseEnd_7833938] using wordTrace_append hprefix tailTrace_7833938
  have hstable : (prefixWord ++ tailWord_7833938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833938).length < 2 ^ (prefixWord ++ tailWord_7833938).sum := by decide
  have hdescent : baseEnd_7833938 < baseStart_7833938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833944 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_7833944 : Nat := 118140960795 + 7833944 * 2 ^ 59
def prefixEnd_7833944 : Nat := 4983230072969 + 3 ^ 40 * 7833944 * 2
def baseEnd_7833944 : Nat := 4022578692405802891772353

theorem tailTrace_7833944 : CollatzResearch.WordTrace tailWord_7833944 prefixEnd_7833944 4022578692405802891772353 := by
  unfold tailWord_7833944
  simp only [CollatzResearch.WordTrace]
  refine ⟨142863705565483146981086443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190484940753977529308115257 142863705565483146981086443)
  ·
    refine ⟨214295558348224720471629665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142863705565483146981086443 214295558348224720471629665)
    ·
      refine ⟨160721668761168540353722249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214295558348224720471629665 160721668761168540353722249)
      ·
        refine ⟨120541251570876405265291687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160721668761168540353722249 120541251570876405265291687)
        ·
          refine ⟨180811877356314607897937531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120541251570876405265291687 180811877356314607897937531)
          ·
            refine ⟨271217816034471911846906297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180811877356314607897937531 271217816034471911846906297)
            ·
              refine ⟨203413362025853933885179723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271217816034471911846906297 203413362025853933885179723)
              ·
                refine ⟨305120043038780900827769585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203413362025853933885179723 305120043038780900827769585)
                ·
                  refine ⟨228840032279085675620827189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305120043038780900827769585 228840032279085675620827189)
                  ·
                    refine ⟨21453753026164282089452549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 228840032279085675620827189 21453753026164282089452549)
                    ·
                      refine ⟨4022578692405802891772353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21453753026164282089452549 4022578692405802891772353)
                      ·
                        rfl

theorem cell23_7833944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_7833944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833944 prefixEnd_7833944 := by exact prefixLift 7833944
  have htrace : WordTrace (prefixWord ++ tailWord_7833944) baseStart_7833944 baseEnd_7833944 := by
    simpa [prefixWord, tailWord_7833944, baseEnd_7833944] using wordTrace_append hprefix tailTrace_7833944
  have hstable : (prefixWord ++ tailWord_7833944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833944).length < 2 ^ (prefixWord ++ tailWord_7833944).sum := by decide
  have hdescent : baseEnd_7833944 < baseStart_7833944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833961 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 6, 2]
def baseStart_7833961 : Nat := 118140960795 + 7833961 * 2 ^ 59
def prefixEnd_7833961 : Nat := 4983230072969 + 3 ^ 40 * 7833961 * 2
def baseEnd_7833961 : Nat := 4022587421576929325259775

theorem tailTrace_7833961 : CollatzResearch.WordTrace tailWord_7833961 prefixEnd_7833961 4022587421576929325259775 := by
  unfold tailWord_7833961
  simp only [CollatzResearch.WordTrace]
  refine ⟨285728031171904705865541737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190485354114603137243694491 285728031171904705865541737)
  ·
    refine ⟨214296023378928529399156303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285728031171904705865541737 214296023378928529399156303)
    ·
      refine ⟨321444035068392794098734455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214296023378928529399156303 321444035068392794098734455)
      ·
        refine ⟨482166052602589191148101683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321444035068392794098734455 482166052602589191148101683)
        ·
          refine ⟨723249078903883786722152525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482166052602589191148101683 723249078903883786722152525)
          ·
            refine ⟨271218404588956420020807197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 723249078903883786722152525 271218404588956420020807197)
            ·
              refine ⟨101706901720858657507802699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271218404588956420020807197 101706901720858657507802699)
              ·
                refine ⟨152560352581287986261704049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101706901720858657507802699 152560352581287986261704049)
                ·
                  refine ⟨114420264435965989696278037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152560352581287986261704049 114420264435965989696278037)
                  ·
                    refine ⟨5363449895435905767013033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114420264435965989696278037 5363449895435905767013033)
                    ·
                      refine ⟨4022587421576929325259775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363449895435905767013033 4022587421576929325259775)
                      ·
                        rfl

theorem cell23_7833961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 6, 2].length) (baseStart_7833961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833961 prefixEnd_7833961 := by exact prefixLift 7833961
  have htrace : WordTrace (prefixWord ++ tailWord_7833961) baseStart_7833961 baseEnd_7833961 := by
    simpa [prefixWord, tailWord_7833961, baseEnd_7833961] using wordTrace_append hprefix tailTrace_7833961
  have hstable : (prefixWord ++ tailWord_7833961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833961).length < 2 ^ (prefixWord ++ tailWord_7833961).sum := by decide
  have hdescent : baseEnd_7833961 < baseStart_7833961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833981 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7833981 : Nat := 118140960795 + 7833981 * 2 ^ 59
def prefixEnd_7833981 : Nat := 4983230072969 + 3 ^ 40 * 7833981 * 2
def baseEnd_7833981 : Nat := 4022597691190019247009683

theorem tailTrace_7833981 : CollatzResearch.WordTrace tailWord_7833981 prefixEnd_7833981 4022597691190019247009683 := by
  unfold tailWord_7833981
  simp only [CollatzResearch.WordTrace]
  refine ⟨285728760631832249281269797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190485840421221499520846531 285728760631832249281269797)
  ·
    refine ⟨53574142618468546740238087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285728760631832249281269797 53574142618468546740238087)
    ·
      refine ⟨80361213927702820110357131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53574142618468546740238087 80361213927702820110357131)
      ·
        refine ⟨120541820891554230165535697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80361213927702820110357131 120541820891554230165535697)
        ·
          refine ⟨90406365668665672624151773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120541820891554230165535697 90406365668665672624151773)
          ·
            refine ⟨33902387125749627234056915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90406365668665672624151773 33902387125749627234056915)
            ·
              refine ⟨50853580688624440851085373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33902387125749627234056915 50853580688624440851085373)
              ·
                refine ⟨19070092758234165319157015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50853580688624440851085373 19070092758234165319157015)
                ·
                  refine ⟨28605139137351247978735523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19070092758234165319157015 28605139137351247978735523)
                  ·
                    refine ⟨42907708706026871968103285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28605139137351247978735523 42907708706026871968103285)
                    ·
                      refine ⟨4022597691190019247009683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42907708706026871968103285 4022597691190019247009683)
                      ·
                        rfl

theorem cell23_7833981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7833981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833981 prefixEnd_7833981 := by exact prefixLift 7833981
  have htrace : WordTrace (prefixWord ++ tailWord_7833981) baseStart_7833981 baseEnd_7833981 := by
    simpa [prefixWord, tailWord_7833981, baseEnd_7833981] using wordTrace_append hprefix tailTrace_7833981
  have hstable : (prefixWord ++ tailWord_7833981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833981).length < 2 ^ (prefixWord ++ tailWord_7833981).sum := by decide
  have hdescent : baseEnd_7833981 < baseStart_7833981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833988 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_7833988 : Nat := 118140960795 + 7833988 * 2 ^ 59
def prefixEnd_7833988 : Nat := 4983230072969 + 3 ^ 40 * 7833988 * 2
def baseEnd_7833988 : Nat := 1340867095184866906540717

theorem tailTrace_7833988 : CollatzResearch.WordTrace tailWord_7833988 prefixEnd_7833988 1340867095184866906540717 := by
  unfold tailWord_7833988
  simp only [CollatzResearch.WordTrace]
  refine ⟨142864507971403444738387309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190486010628537926317849745 142864507971403444738387309)
  ·
    refine ⟨53574190489276291776895241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142864507971403444738387309 53574190489276291776895241)
    ·
      refine ⟨40180642866957218832671431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53574190489276291776895241 40180642866957218832671431)
      ·
        refine ⟨60270964300435828249007147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40180642866957218832671431 60270964300435828249007147)
        ·
          refine ⟨90406446450653742373510721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60270964300435828249007147 90406446450653742373510721)
          ·
            refine ⟨67804834837990306780133041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90406446450653742373510721 67804834837990306780133041)
            ·
              refine ⟨50853626128492730085099781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67804834837990306780133041 50853626128492730085099781)
              ·
                refine ⟨9535054899092386890956209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50853626128492730085099781 9535054899092386890956209)
                ·
                  refine ⟨7151291174319290168217157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535054899092386890956209 7151291174319290168217157)
                  ·
                    refine ⟨1340867095184866906540717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151291174319290168217157 1340867095184866906540717)
                    ·
                      rfl

theorem cell23_7833988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_7833988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833988 prefixEnd_7833988 := by exact prefixLift 7833988
  have htrace : WordTrace (prefixWord ++ tailWord_7833988) baseStart_7833988 baseEnd_7833988 := by
    simpa [prefixWord, tailWord_7833988, baseEnd_7833988] using wordTrace_append hprefix tailTrace_7833988
  have hstable : (prefixWord ++ tailWord_7833988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833988).length < 2 ^ (prefixWord ++ tailWord_7833988).sum := by decide
  have hdescent : baseEnd_7833988 < baseStart_7833988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833995 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 3, 2, 2]
def baseStart_7833995 : Nat := 118140960795 + 7833995 * 2 ^ 59
def prefixEnd_7833995 : Nat := 4983230072969 + 3 ^ 40 * 7833995 * 2
def baseEnd_7833995 : Nat := 4022604879919182192234619

theorem tailTrace_7833995 : CollatzResearch.WordTrace tailWord_7833995 prefixEnd_7833995 4022604879919182192234619 := by
  unfold tailWord_7833995
  simp only [CollatzResearch.WordTrace]
  refine ⟨285729271253781529672279439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190486180835854353114852959 285729271253781529672279439)
  ·
    refine ⟨428593906880672294508419159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285729271253781529672279439 428593906880672294508419159)
    ·
      refine ⟨642890860321008441762628739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428593906880672294508419159 642890860321008441762628739)
      ·
        refine ⟨964336290481512662643943109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642890860321008441762628739 964336290481512662643943109)
        ·
          refine ⟨180813054465283624245739333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 964336290481512662643943109 180813054465283624245739333)
          ·
            refine ⟨33902447712240679546076125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180813054465283624245739333 33902447712240679546076125)
            ·
              refine ⟨12713417892090254829778547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33902447712240679546076125 12713417892090254829778547)
              ·
                refine ⟨19070126838135382244667821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713417892090254829778547 19070126838135382244667821)
                ·
                  refine ⟨7151297564300768341750433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19070126838135382244667821 7151297564300768341750433)
                  ·
                    refine ⟨5363473173225576256312825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151297564300768341750433 5363473173225576256312825)
                    ·
                      refine ⟨4022604879919182192234619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363473173225576256312825 4022604879919182192234619)
                      ·
                        rfl

theorem cell23_7833995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 2, 2].length) (baseStart_7833995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833995 prefixEnd_7833995 := by exact prefixLift 7833995
  have htrace : WordTrace (prefixWord ++ tailWord_7833995) baseStart_7833995 baseEnd_7833995 := by
    simpa [prefixWord, tailWord_7833995, baseEnd_7833995] using wordTrace_append hprefix tailTrace_7833995
  have hstable : (prefixWord ++ tailWord_7833995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833995).length < 2 ^ (prefixWord ++ tailWord_7833995).sum := by decide
  have hdescent : baseEnd_7833995 < baseStart_7833995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7833998 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7833998 : Nat := 118140960795 + 7833998 * 2 ^ 59
def prefixEnd_7833998 : Nat := 4983230072969 + 3 ^ 40 * 7833998 * 2
def baseEnd_7833998 : Nat := 4022606420361145680497105

theorem tailTrace_7833998 : CollatzResearch.WordTrace tailWord_7833998 prefixEnd_7833998 4022606420361145680497105 := by
  unfold tailWord_7833998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716172584096332648079831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190486253781847107456425765 35716172584096332648079831)
  ·
    refine ⟨53574258876144498972119747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716172584096332648079831 53574258876144498972119747)
    ·
      refine ⟨80361388314216748458179621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53574258876144498972119747 80361388314216748458179621)
      ·
        refine ⟨15067760308915640335908679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80361388314216748458179621 15067760308915640335908679)
        ·
          refine ⟨22601640463373460503863019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067760308915640335908679 22601640463373460503863019)
          ·
            refine ⟨33902460695060190755794529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22601640463373460503863019 33902460695060190755794529)
            ·
              refine ⟨25426845521295143066845897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33902460695060190755794529 25426845521295143066845897)
              ·
                refine ⟨19070134140971357300134423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25426845521295143066845897 19070134140971357300134423)
                ·
                  refine ⟨28605201211457035950201635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19070134140971357300134423 28605201211457035950201635)
                  ·
                    refine ⟨42907801817185553925302453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28605201211457035950201635 42907801817185553925302453)
                    ·
                      refine ⟨4022606420361145680497105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42907801817185553925302453 4022606420361145680497105)
                      ·
                        rfl

theorem cell23_7833998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7833998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7833998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7833998 prefixEnd_7833998 := by exact prefixLift 7833998
  have htrace : WordTrace (prefixWord ++ tailWord_7833998) baseStart_7833998 baseEnd_7833998 := by
    simpa [prefixWord, tailWord_7833998, baseEnd_7833998] using wordTrace_append hprefix tailTrace_7833998
  have hstable : (prefixWord ++ tailWord_7833998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7833998).length < 2 ^ (prefixWord ++ tailWord_7833998).sum := by decide
  have hdescent : baseEnd_7833998 < baseStart_7833998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7833998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834045 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7834045 : Nat := 118140960795 + 7834045 * 2 ^ 59
def prefixEnd_7834045 : Nat := 4983230072969 + 3 ^ 40 * 7834045 * 2
def baseEnd_7834045 : Nat := 4022630553951906996609389

theorem tailTrace_7834045 : CollatzResearch.WordTrace tailWord_7834045 prefixEnd_7834045 4022630553951906996609389 := by
  unfold tailWord_7834045
  simp only [CollatzResearch.WordTrace]
  refine ⟨285731094903600388211599589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190487396602400258807733059 285731094903600388211599589)
  ·
    refine ⟨53574580294425072789674923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285731094903600388211599589 53574580294425072789674923)
    ·
      refine ⟨80361870441637609184512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53574580294425072789674923 80361870441637609184512385)
      ·
        refine ⟨60271402831228206888384289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80361870441637609184512385 60271402831228206888384289)
        ·
          refine ⟨45203552123421155166288217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60271402831228206888384289 45203552123421155166288217)
          ·
            refine ⟨33902664092565866374716163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45203552123421155166288217 33902664092565866374716163)
            ·
              refine ⟨50853996138848799562074245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33902664092565866374716163 50853996138848799562074245)
              ·
                refine ⟨9535124276034149917888921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50853996138848799562074245 9535124276034149917888921)
                ·
                  refine ⟨7151343207025612438416691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535124276034149917888921 7151343207025612438416691)
                  ·
                    refine ⟨10727014810538418657625037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151343207025612438416691 10727014810538418657625037)
                    ·
                      refine ⟨4022630553951906996609389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10727014810538418657625037 4022630553951906996609389)
                      ·
                        rfl

theorem cell23_7834045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7834045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834045 prefixEnd_7834045 := by exact prefixLift 7834045
  have htrace : WordTrace (prefixWord ++ tailWord_7834045) baseStart_7834045 baseEnd_7834045 := by
    simpa [prefixWord, tailWord_7834045, baseEnd_7834045] using wordTrace_append hprefix tailTrace_7834045
  have hstable : (prefixWord ++ tailWord_7834045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834045).length < 2 ^ (prefixWord ++ tailWord_7834045).sum := by decide
  have hdescent : baseEnd_7834045 < baseStart_7834045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834081 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7834081 : Nat := 118140960795 + 7834081 * 2 ^ 59
def prefixEnd_7834081 : Nat := 4983230072969 + 3 ^ 40 * 7834081 * 2
def baseEnd_7834081 : Nat := 4022649039255468855759223

theorem tailTrace_7834081 : CollatzResearch.WordTrace tailWord_7834081 prefixEnd_7834081 4022649039255468855759223 := by
  unfold tailWord_7834081
  simp only [CollatzResearch.WordTrace]
  refine ⟨285732407931469966359910097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190488271954313310906606731 285732407931469966359910097)
  ·
    refine ⟨214299305948602474769932573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285732407931469966359910097 214299305948602474769932573)
    ·
      refine ⟨80362239730725928038724715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214299305948602474769932573 80362239730725928038724715)
      ·
        refine ⟨120543359596088892058087073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80362239730725928038724715 120543359596088892058087073)
        ·
          refine ⟨90407519697066669043565305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120543359596088892058087073 90407519697066669043565305)
          ·
            refine ⟨67805639772800001782673979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90407519697066669043565305 67805639772800001782673979)
            ·
              refine ⟨101708459659200002674010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67805639772800001782673979 101708459659200002674010969)
              ·
                refine ⟨76281344744400002005508227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101708459659200002674010969 76281344744400002005508227)
                ·
                  refine ⟨114422017116600003008262341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76281344744400002005508227 114422017116600003008262341)
                  ·
                    refine ⟨21454128209362500564049189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114422017116600003008262341 21454128209362500564049189)
                    ·
                      refine ⟨4022649039255468855759223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21454128209362500564049189 4022649039255468855759223)
                      ·
                        rfl

theorem cell23_7834081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7834081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834081 prefixEnd_7834081 := by exact prefixLift 7834081
  have htrace : WordTrace (prefixWord ++ tailWord_7834081) baseStart_7834081 baseEnd_7834081 := by
    simpa [prefixWord, tailWord_7834081, baseEnd_7834081] using wordTrace_append hprefix tailTrace_7834081
  have hstable : (prefixWord ++ tailWord_7834081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834081).length < 2 ^ (prefixWord ++ tailWord_7834081).sum := by decide
  have hdescent : baseEnd_7834081 < baseStart_7834081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834102 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7834102 : Nat := 118140960795 + 7834102 * 2 ^ 59
def prefixEnd_7834102 : Nat := 4983230072969 + 3 ^ 40 * 7834102 * 2
def baseEnd_7834102 : Nat := 4022659822349213273596627

theorem tailTrace_7834102 : CollatzResearch.WordTrace tailWord_7834102 prefixEnd_7834102 4022659822349213273596627 := by
  unfold tailWord_7834102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858323366524617934151535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190488782576262591297616373 17858323366524617934151535)
  ·
    refine ⟨26787485049786926901227303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17858323366524617934151535 26787485049786926901227303)
    ·
      refine ⟨40181227574680390351840955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26787485049786926901227303 40181227574680390351840955)
      ·
        refine ⟨60271841362020585527761433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40181227574680390351840955 60271841362020585527761433)
        ·
          refine ⟨45203881021515439145821075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60271841362020585527761433 45203881021515439145821075)
          ·
            refine ⟨67805821532273158718731613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45203881021515439145821075 67805821532273158718731613)
            ·
              refine ⟨25427183074602434519524355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67805821532273158718731613 25427183074602434519524355)
              ·
                refine ⟨38140774611903651779286533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25427183074602434519524355 38140774611903651779286533)
                ·
                  refine ⟨7151395239731934708616225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38140774611903651779286533 7151395239731934708616225)
                  ·
                    refine ⟨5363546429798951031462169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151395239731934708616225 5363546429798951031462169)
                    ·
                      refine ⟨4022659822349213273596627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363546429798951031462169 4022659822349213273596627)
                      ·
                        rfl

theorem cell23_7834102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7834102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834102 prefixEnd_7834102 := by exact prefixLift 7834102
  have htrace : WordTrace (prefixWord ++ tailWord_7834102) baseStart_7834102 baseEnd_7834102 := by
    simpa [prefixWord, tailWord_7834102, baseEnd_7834102] using wordTrace_append hprefix tailTrace_7834102
  have hstable : (prefixWord ++ tailWord_7834102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834102).length < 2 ^ (prefixWord ++ tailWord_7834102).sum := by decide
  have hdescent : baseEnd_7834102 < baseStart_7834102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834119 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7834119 : Nat := 118140960795 + 7834119 * 2 ^ 59
def prefixEnd_7834119 : Nat := 4983230072969 + 3 ^ 40 * 7834119 * 2
def baseEnd_7834119 : Nat := 4022668551520339707084049

theorem tailTrace_7834119 : CollatzResearch.WordTrace tailWord_7834119 prefixEnd_7834119 4022668551520339707084049 := by
  unfold tailWord_7834119
  simp only [CollatzResearch.WordTrace]
  refine ⟨285733793905332298849793411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190489195936888199233195607 285733793905332298849793411)
  ·
    refine ⟨428600690857998448274690117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285733793905332298849793411 428600690857998448274690117)
    ·
      refine ⟨80362629535874709051504397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428600690857998448274690117 80362629535874709051504397)
      ·
        refine ⟨30135986075953015894314149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80362629535874709051504397 30135986075953015894314149)
        ·
          refine ⟨5650497389241190480183903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30135986075953015894314149 5650497389241190480183903)
          ·
            refine ⟨8475746083861785720275855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650497389241190480183903 8475746083861785720275855)
            ·
              refine ⟨12713619125792678580413783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475746083861785720275855 12713619125792678580413783)
              ·
                refine ⟨19070428688689017870620675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713619125792678580413783 19070428688689017870620675)
                ·
                  refine ⟨28605643033033526805931013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19070428688689017870620675 28605643033033526805931013)
                  ·
                    refine ⟨5363558068693786276112065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28605643033033526805931013 5363558068693786276112065)
                    ·
                      refine ⟨4022668551520339707084049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363558068693786276112065 4022668551520339707084049)
                      ·
                        rfl

theorem cell23_7834119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7834119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834119 prefixEnd_7834119 := by exact prefixLift 7834119
  have htrace : WordTrace (prefixWord ++ tailWord_7834119) baseStart_7834119 baseEnd_7834119 := by
    simpa [prefixWord, tailWord_7834119, baseEnd_7834119] using wordTrace_append hprefix tailTrace_7834119
  have hstable : (prefixWord ++ tailWord_7834119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834119).length < 2 ^ (prefixWord ++ tailWord_7834119).sum := by decide
  have hdescent : baseEnd_7834119 < baseStart_7834119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834121 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_7834121 : Nat := 118140960795 + 7834121 * 2 ^ 59
def prefixEnd_7834121 : Nat := 4983230072969 + 3 ^ 40 * 7834121 * 2
def baseEnd_7834121 : Nat := 1340889859493882899753013

theorem tailTrace_7834121 : CollatzResearch.WordTrace tailWord_7834121 prefixEnd_7834121 1340889859493882899753013 := by
  unfold tailWord_7834121
  simp only [CollatzResearch.WordTrace]
  refine ⟨285733866851325053191366217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190489244567550035460910811 285733866851325053191366217)
  ·
    refine ⟨214300400138493789893524663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285733866851325053191366217 214300400138493789893524663)
    ·
      refine ⟨321450600207740684840286995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214300400138493789893524663 321450600207740684840286995)
      ·
        refine ⟨482175900311611027260430493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321450600207740684840286995 482175900311611027260430493)
        ·
          refine ⟨180815962616854135222661435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482175900311611027260430493 180815962616854135222661435)
          ·
            refine ⟨271223943925281202833992153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180815962616854135222661435 271223943925281202833992153)
            ·
              refine ⟨203417957943960902125494115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271223943925281202833992153 203417957943960902125494115)
              ·
                refine ⟨305126936915941353188241173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203417957943960902125494115 305126936915941353188241173)
                ·
                  refine ⟨14302825167934750930698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 305126936915941353188241173 14302825167934750930698805)
                  ·
                    refine ⟨1340889859493882899753013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14302825167934750930698805 1340889859493882899753013)
                    ·
                      rfl

theorem cell23_7834121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_7834121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834121 prefixEnd_7834121 := by exact prefixLift 7834121
  have htrace : WordTrace (prefixWord ++ tailWord_7834121) baseStart_7834121 baseEnd_7834121 := by
    simpa [prefixWord, tailWord_7834121, baseEnd_7834121] using wordTrace_append hprefix tailTrace_7834121
  have hstable : (prefixWord ++ tailWord_7834121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834121).length < 2 ^ (prefixWord ++ tailWord_7834121).sum := by decide
  have hdescent : baseEnd_7834121 < baseStart_7834121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834171 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4]
def baseStart_7834171 : Nat := 118140960795 + 7834171 * 2 ^ 59
def prefixEnd_7834171 : Nat := 4983230072969 + 3 ^ 40 * 7834171 * 2
def baseEnd_7834171 : Nat := 4022695252514373503633809

theorem tailTrace_7834171 : CollatzResearch.WordTrace tailWord_7834171 prefixEnd_7834171 4022695252514373503633809 := by
  unfold tailWord_7834171
  simp only [CollatzResearch.WordTrace]
  refine ⟨285735690501143911730686367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190490460334095941153790911 285735690501143911730686367)
  ·
    refine ⟨428603535751715867596029551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285735690501143911730686367 428603535751715867596029551)
    ·
      refine ⟨642905303627573801394044327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428603535751715867596029551 642905303627573801394044327)
      ·
        refine ⟨964357955441360702091066491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642905303627573801394044327 964357955441360702091066491)
        ·
          refine ⟨1446536933162041053136599737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964357955441360702091066491 1446536933162041053136599737)
          ·
            refine ⟨1084902699871530789852449803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446536933162041053136599737 1084902699871530789852449803)
            ·
              refine ⟨1627354049807296184778674705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084902699871530789852449803 1627354049807296184778674705)
              ·
                refine ⟨1220515537355472138584006029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1627354049807296184778674705 1220515537355472138584006029)
                ·
                  refine ⟨457693326508302051969002261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220515537355472138584006029 457693326508302051969002261)
                  ·
                    refine ⟨21454374680076658686046981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 457693326508302051969002261 21454374680076658686046981)
                    ·
                      refine ⟨4022695252514373503633809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21454374680076658686046981 4022695252514373503633809)
                      ·
                        rfl

theorem cell23_7834171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 4].length) (baseStart_7834171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834171 prefixEnd_7834171 := by exact prefixLift 7834171
  have htrace : WordTrace (prefixWord ++ tailWord_7834171) baseStart_7834171 baseEnd_7834171 := by
    simpa [prefixWord, tailWord_7834171, baseEnd_7834171] using wordTrace_append hprefix tailTrace_7834171
  have hstable : (prefixWord ++ tailWord_7834171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834171).length < 2 ^ (prefixWord ++ tailWord_7834171).sum := by decide
  have hdescent : baseEnd_7834171 < baseStart_7834171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_7834201 : Nat := 118140960795 + 7834201 * 2 ^ 59
def prefixEnd_7834201 : Nat := 4983230072969 + 3 ^ 40 * 7834201 * 2
def baseEnd_7834201 : Nat := 4022710656934008386258671

theorem tailTrace_7834201 : CollatzResearch.WordTrace tailWord_7834201 prefixEnd_7834201 4022710656934008386258671 := by
  unfold tailWord_7834201
  simp only [CollatzResearch.WordTrace]
  refine ⟨285736784691035226854278457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190491189794023484569518971 285736784691035226854278457)
  ·
    refine ⟨214302588518276420140708843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285736784691035226854278457 214302588518276420140708843)
    ·
      refine ⟨321453882777414630211063265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214302588518276420140708843 321453882777414630211063265)
      ·
        refine ⟨241090412083060972658297449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321453882777414630211063265 241090412083060972658297449)
        ·
          refine ⟨180817809062295729493723087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241090412083060972658297449 180817809062295729493723087)
          ·
            refine ⟨271226713593443594240584631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180817809062295729493723087 271226713593443594240584631)
            ·
              refine ⟨406840070390165391360876947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271226713593443594240584631 406840070390165391360876947)
              ·
                refine ⟨610260105585248087041315421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406840070390165391360876947 610260105585248087041315421)
                ·
                  refine ⟨228847539594468032640493283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610260105585248087041315421 228847539594468032640493283)
                  ·
                    refine ⟨343271309391702048960739925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228847539594468032640493283 343271309391702048960739925)
                    ·
                      refine ⟨4022710656934008386258671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343271309391702048960739925 4022710656934008386258671)
                      ·
                        rfl

theorem cell23_7834201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_7834201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834201 prefixEnd_7834201 := by exact prefixLift 7834201
  have htrace : WordTrace (prefixWord ++ tailWord_7834201) baseStart_7834201 baseEnd_7834201 := by
    simpa [prefixWord, tailWord_7834201, baseEnd_7834201] using wordTrace_append hprefix tailTrace_7834201
  have hstable : (prefixWord ++ tailWord_7834201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834201).length < 2 ^ (prefixWord ++ tailWord_7834201).sum := by decide
  have hdescent : baseEnd_7834201 < baseStart_7834201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834218 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7834218 : Nat := 118140960795 + 7834218 * 2 ^ 59
def prefixEnd_7834218 : Nat := 4983230072969 + 3 ^ 40 * 7834218 * 2
def baseEnd_7834218 : Nat := 4022719386105134819746093

theorem tailTrace_7834218 : CollatzResearch.WordTrace tailWord_7834218 prefixEnd_7834218 4022719386105134819746093 := by
  unfold tailWord_7834218
  simp only [CollatzResearch.WordTrace]
  refine ⟨71434351182993409689411827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190491603154649092505098205 71434351182993409689411827)
  ·
    refine ⟨107151526774490114534117741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71434351182993409689411827 107151526774490114534117741)
    ·
      refine ⟨40181822540433792950294153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107151526774490114534117741 40181822540433792950294153)
      ·
        refine ⟨30136366905325344712720615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40181822540433792950294153 30136366905325344712720615)
        ·
          refine ⟨45204550357988017069080923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30136366905325344712720615 45204550357988017069080923)
          ·
            refine ⟨67806825536982025603621385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45204550357988017069080923 67806825536982025603621385)
            ·
              refine ⟨50855119152736519202716039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67806825536982025603621385 50855119152736519202716039)
              ·
                refine ⟨76282678729104778804074059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50855119152736519202716039 76282678729104778804074059)
                ·
                  refine ⟨114424018093657168206111089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76282678729104778804074059 114424018093657168206111089)
                  ·
                    refine ⟨85818013570242876154583317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114424018093657168206111089 85818013570242876154583317)
                    ·
                      refine ⟨4022719386105134819746093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85818013570242876154583317 4022719386105134819746093)
                      ·
                        rfl

theorem cell23_7834218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7834218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834218 prefixEnd_7834218 := by exact prefixLift 7834218
  have htrace : WordTrace (prefixWord ++ tailWord_7834218) baseStart_7834218 baseEnd_7834218 := by
    simpa [prefixWord, tailWord_7834218, baseEnd_7834218] using wordTrace_append hprefix tailTrace_7834218
  have hstable : (prefixWord ++ tailWord_7834218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834218).length < 2 ^ (prefixWord ++ tailWord_7834218).sum := by decide
  have hdescent : baseEnd_7834218 < baseStart_7834218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834265 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_7834265 : Nat := 118140960795 + 7834265 * 2 ^ 59
def prefixEnd_7834265 : Nat := 4983230072969 + 3 ^ 40 * 7834265 * 2
def baseEnd_7834265 : Nat := 4022743519695896135858377

theorem tailTrace_7834265 : CollatzResearch.WordTrace tailWord_7834265 prefixEnd_7834265 4022743519695896135858377 := by
  unfold tailWord_7834265
  simp only [CollatzResearch.WordTrace]
  refine ⟨285739118962803365784608249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190492745975202243856405499 285739118962803365784608249)
  ·
    refine ⟨214304339222102524338456187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285739118962803365784608249 214304339222102524338456187)
    ·
      refine ⟨321456508833153786507684281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214304339222102524338456187 321456508833153786507684281)
      ·
        refine ⟨241092381624865339880763211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321456508833153786507684281 241092381624865339880763211)
        ·
          refine ⟨361638572437298009821144817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241092381624865339880763211 361638572437298009821144817)
          ·
            refine ⟨271228929327973507365858613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361638572437298009821144817 271228929327973507365858613)
            ·
              refine ⟨25427712124497516315549245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271228929327973507365858613 25427712124497516315549245)
              ·
                refine ⟨9535392046686568618330967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25427712124497516315549245 9535392046686568618330967)
                ·
                  refine ⟨14303088070029852927496451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9535392046686568618330967 14303088070029852927496451)
                  ·
                    refine ⟨21454632105044779391244677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14303088070029852927496451 21454632105044779391244677)
                    ·
                      refine ⟨4022743519695896135858377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21454632105044779391244677 4022743519695896135858377)
                      ·
                        rfl

theorem cell23_7834265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_7834265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834265 prefixEnd_7834265 := by exact prefixLift 7834265
  have htrace : WordTrace (prefixWord ++ tailWord_7834265) baseStart_7834265 baseEnd_7834265 := by
    simpa [prefixWord, tailWord_7834265, baseEnd_7834265] using wordTrace_append hprefix tailTrace_7834265
  have hstable : (prefixWord ++ tailWord_7834265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834265).length < 2 ^ (prefixWord ++ tailWord_7834265).sum := by decide
  have hdescent : baseEnd_7834265 < baseStart_7834265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834275 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 2, 4]
def baseStart_7834275 : Nat := 118140960795 + 7834275 * 2 ^ 59
def prefixEnd_7834275 : Nat := 4983230072969 + 3 ^ 40 * 7834275 * 2
def baseEnd_7834275 : Nat := 1340916218167480365577777

theorem tailTrace_7834275 : CollatzResearch.WordTrace tailWord_7834275 prefixEnd_7834275 1340916218167480365577777 := by
  unfold tailWord_7834275
  simp only [CollatzResearch.WordTrace]
  refine ⟨285739483692767137492472279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190492989128511424994981519 285739483692767137492472279)
  ·
    refine ⟨428609225539150706238708419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285739483692767137492472279 428609225539150706238708419)
    ·
      refine ⟨642913838308726059358062629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428609225539150706238708419 642913838308726059358062629)
      ·
        refine ⟨120546344682886136129636743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 642913838308726059358062629 120546344682886136129636743)
        ·
          refine ⟨180819517024329204194455115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120546344682886136129636743 180819517024329204194455115)
          ·
            refine ⟨271229275536493806291682673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180819517024329204194455115 271229275536493806291682673)
            ·
              refine ⟨203421956652370354718762005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271229275536493806291682673 203421956652370354718762005)
              ·
                refine ⟨9535404218079860377441969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203421956652370354718762005 9535404218079860377441969)
                ·
                  refine ⟨7151553163559895283081477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535404218079860377441969 7151553163559895283081477)
                  ·
                    refine ⟨1340916218167480365577777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151553163559895283081477 1340916218167480365577777)
                    ·
                      rfl

theorem cell23_7834275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 4].length) (baseStart_7834275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834275 prefixEnd_7834275 := by exact prefixLift 7834275
  have htrace : WordTrace (prefixWord ++ tailWord_7834275) baseStart_7834275 baseEnd_7834275 := by
    simpa [prefixWord, tailWord_7834275, baseEnd_7834275] using wordTrace_append hprefix tailTrace_7834275
  have hstable : (prefixWord ++ tailWord_7834275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834275).length < 2 ^ (prefixWord ++ tailWord_7834275).sum := by decide
  have hdescent : baseEnd_7834275 < baseStart_7834275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834285 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_7834285 : Nat := 118140960795 + 7834285 * 2 ^ 59
def prefixEnd_7834285 : Nat := 4983230072969 + 3 ^ 40 * 7834285 * 2
def baseEnd_7834285 : Nat := 4022753789308986057608285

theorem tailTrace_7834285 : CollatzResearch.WordTrace tailWord_7834285 prefixEnd_7834285 4022753789308986057608285 := by
  unfold tailWord_7834285
  simp only [CollatzResearch.WordTrace]
  refine ⟨285739848422730909200336309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190493232281820606133557539 285739848422730909200336309)
  ·
    refine ⟨26788110789631022737531529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285739848422730909200336309 26788110789631022737531529)
    ·
      refine ⟨20091083092223267053148647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26788110789631022737531529 20091083092223267053148647)
      ·
        refine ⟨30136624638334900579722971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091083092223267053148647 30136624638334900579722971)
        ·
          refine ⟨45204936957502350869584457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30136624638334900579722971 45204936957502350869584457)
          ·
            refine ⟨33903702718126763152188343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45204936957502350869584457 33903702718126763152188343)
            ·
              refine ⟨50855554077190144728282515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33903702718126763152188343 50855554077190144728282515)
              ·
                refine ⟨76283331115785217092423773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50855554077190144728282515 76283331115785217092423773)
                ·
                  refine ⟨28606249168419456409658915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76283331115785217092423773 28606249168419456409658915)
                  ·
                    refine ⟨42909373752629184614488373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28606249168419456409658915 42909373752629184614488373)
                    ·
                      refine ⟨4022753789308986057608285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42909373752629184614488373 4022753789308986057608285)
                      ·
                        rfl

theorem cell23_7834285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_7834285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834285 prefixEnd_7834285 := by exact prefixLift 7834285
  have htrace : WordTrace (prefixWord ++ tailWord_7834285) baseStart_7834285 baseEnd_7834285 := by
    simpa [prefixWord, tailWord_7834285, baseEnd_7834285] using wordTrace_append hprefix tailTrace_7834285
  have hstable : (prefixWord ++ tailWord_7834285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834285).length < 2 ^ (prefixWord ++ tailWord_7834285).sum := by decide
  have hdescent : baseEnd_7834285 < baseStart_7834285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834295 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_7834295 : Nat := 118140960795 + 7834295 * 2 ^ 59
def prefixEnd_7834295 : Nat := 4983230072969 + 3 ^ 40 * 7834295 * 2
def baseEnd_7834295 : Nat := 4022758924115531018483239

theorem tailTrace_7834295 : CollatzResearch.WordTrace tailWord_7834295 prefixEnd_7834295 4022758924115531018483239 := by
  unfold tailWord_7834295
  simp only [CollatzResearch.WordTrace]
  refine ⟨285740213152694680908200339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190493475435129787272133559 285740213152694680908200339)
  ·
    refine ⟨428610319729042021362300509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285740213152694680908200339 428610319729042021362300509)
    ·
      refine ⟨160728869898390758010862691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428610319729042021362300509 160728869898390758010862691)
      ·
        refine ⟨241093304847586137016294037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160728869898390758010862691 241093304847586137016294037)
        ·
          refine ⟨11301248664730600172638783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241093304847586137016294037 11301248664730600172638783)
          ·
            refine ⟨16951872997095900258958175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301248664730600172638783 16951872997095900258958175)
            ·
              refine ⟨25427809495643850388437263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16951872997095900258958175 25427809495643850388437263)
              ·
                refine ⟨38141714243465775582655895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25427809495643850388437263 38141714243465775582655895)
                ·
                  refine ⟨57212571365198663373983843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38141714243465775582655895 57212571365198663373983843)
                  ·
                    refine ⟨85818857047797995060975765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57212571365198663373983843 85818857047797995060975765)
                    ·
                      refine ⟨4022758924115531018483239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85818857047797995060975765 4022758924115531018483239)
                      ·
                        rfl

theorem cell23_7834295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_7834295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834295 prefixEnd_7834295 := by exact prefixLift 7834295
  have htrace : WordTrace (prefixWord ++ tailWord_7834295) baseStart_7834295 baseEnd_7834295 := by
    simpa [prefixWord, tailWord_7834295, baseEnd_7834295] using wordTrace_append hprefix tailTrace_7834295
  have hstable : (prefixWord ++ tailWord_7834295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834295).length < 2 ^ (prefixWord ++ tailWord_7834295).sum := by decide
  have hdescent : baseEnd_7834295 < baseStart_7834295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834322 : List Nat := [3, 2, 2, 2, 4, 1, 9]
def baseStart_7834322 : Nat := 118140960795 + 7834322 * 2 ^ 59
def prefixEnd_7834322 : Nat := 4983230072969 + 3 ^ 40 * 7834322 * 2
def baseEnd_7834322 : Nat := 49663861581397560652415

theorem tailTrace_7834322 : CollatzResearch.WordTrace tailWord_7834322 prefixEnd_7834322 49663861581397560652415 := by
  unfold tailWord_7834322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71435299480899216129858305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190494131949064576346288813 71435299480899216129858305)
  ·
    refine ⟨53576474610674412097393729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71435299480899216129858305 53576474610674412097393729)
    ·
      refine ⟨40182355958005809073045297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53576474610674412097393729 40182355958005809073045297)
      ·
        refine ⟨30136766968504356804783973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40182355958005809073045297 30136766968504356804783973)
        ·
          refine ⟨5650643806594566900896995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30136766968504356804783973 5650643806594566900896995)
          ·
            refine ⟨8475965709891850351345493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650643806594566900896995 8475965709891850351345493)
            ·
              refine ⟨49663861581397560652415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8475965709891850351345493 49663861581397560652415)
              ·
                rfl

theorem cell23_7834322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 9].length) (baseStart_7834322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834322 prefixEnd_7834322 := by exact prefixLift 7834322
  have htrace : WordTrace (prefixWord ++ tailWord_7834322) baseStart_7834322 baseEnd_7834322 := by
    simpa [prefixWord, tailWord_7834322, baseEnd_7834322] using wordTrace_append hprefix tailTrace_7834322
  have hstable : (prefixWord ++ tailWord_7834322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834322).length < 2 ^ (prefixWord ++ tailWord_7834322).sum := by decide
  have hdescent : baseEnd_7834322 < baseStart_7834322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834348 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_7834348 : Nat := 118140960795 + 7834348 * 2 ^ 59
def prefixEnd_7834348 : Nat := 4983230072969 + 3 ^ 40 * 7834348 * 2
def baseEnd_7834348 : Nat := 1340928712863406437040165

theorem tailTrace_7834348 : CollatzResearch.WordTrace tailWord_7834348 prefixEnd_7834348 1340928712863406437040165 := by
  unfold tailWord_7834348
  simp only [CollatzResearch.WordTrace]
  refine ⟨142871073110751335479939849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190494764147668447306586465 142871073110751335479939849)
  ·
    refine ⟨107153304833063501609954887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142871073110751335479939849 107153304833063501609954887)
    ·
      refine ⟨160729957249595252414932331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107153304833063501609954887 160729957249595252414932331)
      ·
        refine ⟨241094935874392878622398497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160729957249595252414932331 241094935874392878622398497)
        ·
          refine ⟨180821201905794658966798873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241094935874392878622398497 180821201905794658966798873)
          ·
            refine ⟨135615901429345994225099155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180821201905794658966798873 135615901429345994225099155)
            ·
              refine ⟨203423852144018991337648733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135615901429345994225099155 203423852144018991337648733)
              ·
                refine ⟨76283944554007121751618275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203423852144018991337648733 76283944554007121751618275)
                ·
                  refine ⟨114425916831010682627427413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76283944554007121751618275 114425916831010682627427413)
                  ·
                    refine ⟨1340928712863406437040165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114425916831010682627427413 1340928712863406437040165)
                    ·
                      rfl

theorem cell23_7834348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_7834348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834348 prefixEnd_7834348 := by exact prefixLift 7834348
  have htrace : WordTrace (prefixWord ++ tailWord_7834348) baseStart_7834348 baseEnd_7834348 := by
    simpa [prefixWord, tailWord_7834348, baseEnd_7834348] using wordTrace_append hprefix tailTrace_7834348
  have hstable : (prefixWord ++ tailWord_7834348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834348).length < 2 ^ (prefixWord ++ tailWord_7834348).sum := by decide
  have hdescent : baseEnd_7834348 < baseStart_7834348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834349 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7834349 : Nat := 118140960795 + 7834349 * 2 ^ 59
def prefixEnd_7834349 : Nat := 4983230072969 + 3 ^ 40 * 7834349 * 2
def baseEnd_7834349 : Nat := 4022786652070873807207991

theorem tailTrace_7834349 : CollatzResearch.WordTrace tailWord_7834349 prefixEnd_7834349 4022786652070873807207991 := by
  unfold tailWord_7834349
  simp only [CollatzResearch.WordTrace]
  refine ⟨285742182694499048130666101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190494788462999365420444067 285742182694499048130666101)
  ·
    refine ⟨26788329627609285762249947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285742182694499048130666101 26788329627609285762249947)
    ·
      refine ⟨40182494441413928643374921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26788329627609285762249947 40182494441413928643374921)
      ·
        refine ⟨30136870831060446482531191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40182494441413928643374921 30136870831060446482531191)
        ·
          refine ⟨45205306246590669723796787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30136870831060446482531191 45205306246590669723796787)
          ·
            refine ⟨67807959369886004585695181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45205306246590669723796787 67807959369886004585695181)
            ·
              refine ⟨25427984763707251719635693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67807959369886004585695181 25427984763707251719635693)
              ·
                refine ⟨9535494286390219394863385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25427984763707251719635693 9535494286390219394863385)
                ·
                  refine ⟨7151620714792664546147539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9535494286390219394863385 7151620714792664546147539)
                  ·
                    refine ⟨10727431072188996819221309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7151620714792664546147539 10727431072188996819221309)
                    ·
                      refine ⟨4022786652070873807207991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10727431072188996819221309 4022786652070873807207991)
                      ·
                        rfl

theorem cell23_7834349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7834349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834349 prefixEnd_7834349 := by exact prefixLift 7834349
  have htrace : WordTrace (prefixWord ++ tailWord_7834349) baseStart_7834349 baseEnd_7834349 := by
    simpa [prefixWord, tailWord_7834349, baseEnd_7834349] using wordTrace_append hprefix tailTrace_7834349
  have hstable : (prefixWord ++ tailWord_7834349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834349).length < 2 ^ (prefixWord ++ tailWord_7834349).sum := by decide
  have hdescent : baseEnd_7834349 < baseStart_7834349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834376 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_7834376 : Nat := 118140960795 + 7834376 * 2 ^ 59
def prefixEnd_7834376 : Nat := 4983230072969 + 3 ^ 40 * 7834376 * 2
def baseEnd_7834376 : Nat := 4022800516048545201570367

theorem tailTrace_7834376 : CollatzResearch.WordTrace tailWord_7834376 prefixEnd_7834376 4022800516048545201570367 := by
  unfold tailWord_7834376
  simp only [CollatzResearch.WordTrace]
  refine ⟨142871583732700615870949491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190495444976934154494599321 142871583732700615870949491)
  ·
    refine ⟨214307375599050923806424237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142871583732700615870949491 214307375599050923806424237)
    ·
      refine ⟨80365265849644096427409089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214307375599050923806424237 80365265849644096427409089)
      ·
        refine ⟨60273949387233072320556817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80365265849644096427409089 60273949387233072320556817)
        ·
          refine ⟨45205462040424804240417613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60273949387233072320556817 45205462040424804240417613)
          ·
            refine ⟨16952048265159301590156605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45205462040424804240417613 16952048265159301590156605)
            ·
              refine ⟨6357018099434738096308727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16952048265159301590156605 6357018099434738096308727)
              ·
                refine ⟨9535527149152107144463091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357018099434738096308727 9535527149152107144463091)
                ·
                  refine ⟨14303290723728160716694637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9535527149152107144463091 14303290723728160716694637)
                  ·
                    refine ⟨5363734021398060268760489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14303290723728160716694637 5363734021398060268760489)
                    ·
                      refine ⟨4022800516048545201570367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363734021398060268760489 4022800516048545201570367)
                      ·
                        rfl

theorem cell23_7834376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_7834376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834376 prefixEnd_7834376 := by exact prefixLift 7834376
  have htrace : WordTrace (prefixWord ++ tailWord_7834376) baseStart_7834376 baseEnd_7834376 := by
    simpa [prefixWord, tailWord_7834376, baseEnd_7834376] using wordTrace_append hprefix tailTrace_7834376
  have hstable : (prefixWord ++ tailWord_7834376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834376).length < 2 ^ (prefixWord ++ tailWord_7834376).sum := by decide
  have hdescent : baseEnd_7834376 < baseStart_7834376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834402 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7834402 : Nat := 118140960795 + 7834402 * 2 ^ 59
def prefixEnd_7834402 : Nat := 4983230072969 + 3 ^ 40 * 7834402 * 2
def baseEnd_7834402 : Nat := 4022813866545562099845247

theorem tailTrace_7834402 : CollatzResearch.WordTrace tailWord_7834402 prefixEnd_7834402 4022813866545562099845247 := by
  unfold tailWord_7834402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71436028940826759545586365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190496077175538025454896973 71436028940826759545586365)
  ·
    refine ⟨26788510852810034829594887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71436028940826759545586365 26788510852810034829594887)
    ·
      refine ⟨40182766279215052244392331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26788510852810034829594887 40182766279215052244392331)
      ·
        refine ⟨60274149418822578366588497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40182766279215052244392331 60274149418822578366588497)
        ·
          refine ⟨45205612064116933774941373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60274149418822578366588497 45205612064116933774941373)
          ·
            refine ⟨16952104524043850165603015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45205612064116933774941373 16952104524043850165603015)
            ·
              refine ⟨25428156786065775248404523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952104524043850165603015 25428156786065775248404523)
              ·
                refine ⟨38142235179098662872606785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25428156786065775248404523 38142235179098662872606785)
                ·
                  refine ⟨28606676384323997154455089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38142235179098662872606785 28606676384323997154455089)
                  ·
                    refine ⟨21455007288242997865841317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28606676384323997154455089 21455007288242997865841317)
                    ·
                      refine ⟨4022813866545562099845247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21455007288242997865841317 4022813866545562099845247)
                      ·
                        rfl

theorem cell23_7834402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7834402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834402 prefixEnd_7834402 := by exact prefixLift 7834402
  have htrace : WordTrace (prefixWord ++ tailWord_7834402) baseStart_7834402 baseEnd_7834402 := by
    simpa [prefixWord, tailWord_7834402, baseEnd_7834402] using wordTrace_append hprefix tailTrace_7834402
  have hstable : (prefixWord ++ tailWord_7834402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834402).length < 2 ^ (prefixWord ++ tailWord_7834402).sum := by decide
  have hdescent : baseEnd_7834402 < baseStart_7834402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834482 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7834482 : Nat := 118140960795 + 7834482 * 2 ^ 59
def prefixEnd_7834482 : Nat := 4983230072969 + 3 ^ 40 * 7834482 * 2
def baseEnd_7834482 : Nat := 4022854944997921786844879

theorem tailTrace_7834482 : CollatzResearch.WordTrace tailWord_7834482 prefixEnd_7834482 4022854944997921786844879 := by
  unfold tailWord_7834482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71436758400754302961314425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190498022402011474563505133 71436758400754302961314425)
  ·
    refine ⟨53577568800565727220985819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71436758400754302961314425 53577568800565727220985819)
    ·
      refine ⟨80366353200848590831478729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53577568800565727220985819 80366353200848590831478729)
      ·
        refine ⟨60274764900636443123609047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80366353200848590831478729 60274764900636443123609047)
        ·
          refine ⟨90412147350954664685413571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60274764900636443123609047 90412147350954664685413571)
          ·
            refine ⟨135618221026431997028120357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90412147350954664685413571 135618221026431997028120357)
            ·
              refine ⟨25428416442455999442772567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135618221026431997028120357 25428416442455999442772567)
              ·
                refine ⟨38142624663683999164158851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25428416442455999442772567 38142624663683999164158851)
                ·
                  refine ⟨57213936995525998746238277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38142624663683999164158851 57213936995525998746238277)
                  ·
                    refine ⟨10727613186661124764919677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57213936995525998746238277 10727613186661124764919677)
                    ·
                      refine ⟨4022854944997921786844879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10727613186661124764919677 4022854944997921786844879)
                      ·
                        rfl

theorem cell23_7834482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7834482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834482 prefixEnd_7834482 := by exact prefixLift 7834482
  have htrace : WordTrace (prefixWord ++ tailWord_7834482) baseStart_7834482 baseEnd_7834482 := by
    simpa [prefixWord, tailWord_7834482, baseEnd_7834482] using wordTrace_append hprefix tailTrace_7834482
  have hstable : (prefixWord ++ tailWord_7834482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834482).length < 2 ^ (prefixWord ++ tailWord_7834482).sum := by decide
  have hdescent : baseEnd_7834482 < baseStart_7834482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834506 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_7834506 : Nat := 118140960795 + 7834506 * 2 ^ 59
def prefixEnd_7834506 : Nat := 4983230072969 + 3 ^ 40 * 7834506 * 2
def baseEnd_7834506 : Nat := 1340955756177876564314923

theorem tailTrace_7834506 : CollatzResearch.WordTrace tailWord_7834506 prefixEnd_7834506 1340955756177876564314923 := by
  unfold tailWord_7834506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71436977238732565986032843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190498605969953509296087581 71436977238732565986032843)
  ·
    refine ⟨107155465858098848979049265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71436977238732565986032843 107155465858098848979049265)
    ·
      refine ⟨80366599393574136734286949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107155465858098848979049265 80366599393574136734286949)
      ·
        refine ⟨15068737386295150637678803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80366599393574136734286949 15068737386295150637678803)
        ·
          refine ⟨22603106079442725956518205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15068737386295150637678803 22603106079442725956518205)
          ·
            refine ⟨8476164779791022233694327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22603106079442725956518205 8476164779791022233694327)
            ·
              refine ⟨12714247169686533350541491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476164779791022233694327 12714247169686533350541491)
              ·
                refine ⟨19071370754529800025812237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12714247169686533350541491 19071370754529800025812237)
                ·
                  refine ⟨7151764032948675009679589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19071370754529800025812237 7151764032948675009679589)
                  ·
                    refine ⟨1340955756177876564314923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151764032948675009679589 1340955756177876564314923)
                    ·
                      rfl

theorem cell23_7834506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_7834506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834506 prefixEnd_7834506 := by exact prefixLift 7834506
  have htrace : WordTrace (prefixWord ++ tailWord_7834506) baseStart_7834506 baseEnd_7834506 := by
    simpa [prefixWord, tailWord_7834506, baseEnd_7834506] using wordTrace_append hprefix tailTrace_7834506
  have hstable : (prefixWord ++ tailWord_7834506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834506).length < 2 ^ (prefixWord ++ tailWord_7834506).sum := by decide
  have hdescent : baseEnd_7834506 < baseStart_7834506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834532 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7834532 : Nat := 118140960795 + 7834532 * 2 ^ 59
def prefixEnd_7834532 : Nat := 4983230072969 + 3 ^ 40 * 7834532 * 2
def baseEnd_7834532 : Nat := 1340960206343548863739883

theorem tailTrace_7834532 : CollatzResearch.WordTrace tailWord_7834532 prefixEnd_7834532 1340960206343548863739883 := by
  unfold tailWord_7834532
  simp only [CollatzResearch.WordTrace]
  refine ⟨142874428626418035192288925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190499238168557380256385233 142874428626418035192288925)
  ·
    refine ⟨53577910734906763197108347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142874428626418035192288925 53577910734906763197108347)
    ·
      refine ⟨80366866102360144795662521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53577910734906763197108347 80366866102360144795662521)
      ·
        refine ⟨60275149576770108596746891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80366866102360144795662521 60275149576770108596746891)
        ·
          refine ⟨90412724365155162895120337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60275149576770108596746891 90412724365155162895120337)
          ·
            refine ⟨67809543273866372171340253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90412724365155162895120337 67809543273866372171340253)
            ·
              refine ⟨25428578727699889564252595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67809543273866372171340253 25428578727699889564252595)
              ·
                refine ⟨38142868091549834346378893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25428578727699889564252595 38142868091549834346378893)
                ·
                  refine ⟨14303575534331187879892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38142868091549834346378893 14303575534331187879892085)
                  ·
                    refine ⟨1340960206343548863739883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14303575534331187879892085 1340960206343548863739883)
                    ·
                      rfl

theorem cell23_7834532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7834532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834532 prefixEnd_7834532 := by exact prefixLift 7834532
  have htrace : WordTrace (prefixWord ++ tailWord_7834532) baseStart_7834532 baseEnd_7834532 := by
    simpa [prefixWord, tailWord_7834532, baseEnd_7834532] using wordTrace_append hprefix tailTrace_7834532
  have hstable : (prefixWord ++ tailWord_7834532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834532).length < 2 ^ (prefixWord ++ tailWord_7834532).sum := by decide
  have hdescent : baseEnd_7834532 < baseStart_7834532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834572 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7834572 : Nat := 118140960795 + 7834572 * 2 ^ 59
def prefixEnd_7834572 : Nat := 4983230072969 + 3 ^ 40 * 7834572 * 2
def baseEnd_7834572 : Nat := 4022901158256826434719465

theorem tailTrace_7834572 : CollatzResearch.WordTrace tailWord_7834572 prefixEnd_7834572 4022901158256826434719465 := by
  unfold tailWord_7834572
  simp only [CollatzResearch.WordTrace]
  refine ⟨142875158086345578608016985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190500210781794104810689313 142875158086345578608016985)
  ·
    refine ⟨107156368564759183956012739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142875158086345578608016985 107156368564759183956012739)
    ·
      refine ⟨160734552847138775934019109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107156368564759183956012739 160734552847138775934019109)
      ·
        refine ⟨30137728658838520487628583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160734552847138775934019109 30137728658838520487628583)
        ·
          refine ⟨45206592988257780731442875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30137728658838520487628583 45206592988257780731442875)
          ·
            refine ⟨67809889482386671097164313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45206592988257780731442875 67809889482386671097164313)
            ·
              refine ⟨50857417111790003322873235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67809889482386671097164313 50857417111790003322873235)
              ·
                refine ⟨76286125667685004984309853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50857417111790003322873235 76286125667685004984309853)
                ·
                  refine ⟨28607297125381876869116195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76286125667685004984309853 28607297125381876869116195)
                  ·
                    refine ⟨42910945688072815303674293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28607297125381876869116195 42910945688072815303674293)
                    ·
                      refine ⟨4022901158256826434719465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42910945688072815303674293 4022901158256826434719465)
                      ·
                        rfl

theorem cell23_7834572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7834572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834572 prefixEnd_7834572 := by exact prefixLift 7834572
  have htrace : WordTrace (prefixWord ++ tailWord_7834572) baseStart_7834572 baseEnd_7834572 := by
    simpa [prefixWord, tailWord_7834572, baseEnd_7834572] using wordTrace_append hprefix tailTrace_7834572
  have hstable : (prefixWord ++ tailWord_7834572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834572).length < 2 ^ (prefixWord ++ tailWord_7834572).sum := by decide
  have hdescent : baseEnd_7834572 < baseStart_7834572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834586 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_7834586 : Nat := 118140960795 + 7834586 * 2 ^ 59
def prefixEnd_7834586 : Nat := 4983230072969 + 3 ^ 40 * 7834586 * 2
def baseEnd_7834586 : Nat := 4022908346985989379944401

theorem tailTrace_7834586 : CollatzResearch.WordTrace tailWord_7834586 prefixEnd_7834586 4022908346985989379944401 := by
  unfold tailWord_7834586
  simp only [CollatzResearch.WordTrace]
  refine ⟨71437706698660109401760903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190500551196426958404695741 71437706698660109401760903)
  ·
    refine ⟨107156560047990164102641355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71437706698660109401760903 107156560047990164102641355)
    ·
      refine ⟨160734840071985246153962033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107156560047990164102641355 160734840071985246153962033)
      ·
        refine ⟨120551130053988934615471525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160734840071985246153962033 120551130053988934615471525)
        ·
          refine ⟨22603336885122925240400911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120551130053988934615471525 22603336885122925240400911)
          ·
            refine ⟨33905005327684387860601367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603336885122925240400911 33905005327684387860601367)
            ·
              refine ⟨50857507991526581790902051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33905005327684387860601367 50857507991526581790902051)
              ·
                refine ⟨76286261987289872686353077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50857507991526581790902051 76286261987289872686353077)
                ·
                  refine ⟨7151837061308425564345601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76286261987289872686353077 7151837061308425564345601)
                  ·
                    refine ⟨5363877795981319173259201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7151837061308425564345601 5363877795981319173259201)
                    ·
                      refine ⟨4022908346985989379944401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5363877795981319173259201 4022908346985989379944401)
                      ·
                        rfl

theorem cell23_7834586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_7834586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834586 prefixEnd_7834586 := by exact prefixLift 7834586
  have htrace : WordTrace (prefixWord ++ tailWord_7834586) baseStart_7834586 baseEnd_7834586 := by
    simpa [prefixWord, tailWord_7834586, baseEnd_7834586] using wordTrace_append hprefix tailTrace_7834586
  have hstable : (prefixWord ++ tailWord_7834586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834586).length < 2 ^ (prefixWord ++ tailWord_7834586).sum := by decide
  have hdescent : baseEnd_7834586 < baseStart_7834586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834599 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7834599 : Nat := 118140960795 + 7834599 * 2 ^ 59
def prefixEnd_7834599 : Nat := 4983230072969 + 3 ^ 40 * 7834599 * 2
def baseEnd_7834599 : Nat := 4022915022234497829081841

theorem tailTrace_7834599 : CollatzResearch.WordTrace tailWord_7834599 prefixEnd_7834599 4022915022234497829081841 := by
  unfold tailWord_7834599
  simp only [CollatzResearch.WordTrace]
  refine ⟨285751300943593340827266851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190500867295728893884844567 285751300943593340827266851)
  ·
    refine ⟨428626951415390011240900277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285751300943593340827266851 428626951415390011240900277)
    ·
      refine ⟨40183776695192813553834401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 428626951415390011240900277 40183776695192813553834401)
      ·
        refine ⟨30137832521394610165375801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40183776695192813553834401 30137832521394610165375801)
        ·
          refine ⟨22603374391045957624031851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30137832521394610165375801 22603374391045957624031851)
          ·
            refine ⟨33905061586568936436047777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603374391045957624031851 33905061586568936436047777)
            ·
              refine ⟨25428796189926702327035833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33905061586568936436047777 25428796189926702327035833)
              ·
                refine ⟨19071597142445026745276875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25428796189926702327035833 19071597142445026745276875)
                ·
                  refine ⟨28607395713667540117915313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19071597142445026745276875 28607395713667540117915313)
                  ·
                    refine ⟨21455546785250655088436485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28607395713667540117915313 21455546785250655088436485)
                    ·
                      refine ⟨4022915022234497829081841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21455546785250655088436485 4022915022234497829081841)
                      ·
                        rfl

theorem cell23_7834599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7834599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834599 prefixEnd_7834599 := by exact prefixLift 7834599
  have htrace : WordTrace (prefixWord ++ tailWord_7834599) baseStart_7834599 baseEnd_7834599 := by
    simpa [prefixWord, tailWord_7834599, baseEnd_7834599] using wordTrace_append hprefix tailTrace_7834599
  have hstable : (prefixWord ++ tailWord_7834599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834599).length < 2 ^ (prefixWord ++ tailWord_7834599).sum := by decide
  have hdescent : baseEnd_7834599 < baseStart_7834599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834613 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7834613 : Nat := 118140960795 + 7834613 * 2 ^ 59
def prefixEnd_7834613 : Nat := 4983230072969 + 3 ^ 40 * 7834613 * 2
def baseEnd_7834613 : Nat := 1340974070321220258102259

theorem tailTrace_7834613 : CollatzResearch.WordTrace tailWord_7834613 prefixEnd_7834613 1340974070321220258102259 := by
  unfold tailWord_7834613
  simp only [CollatzResearch.WordTrace]
  refine ⟨285751811565542621218276493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190501207710361747478850995 285751811565542621218276493)
  ·
    refine ⟨107156929337078482956853685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285751811565542621218276493 107156929337078482956853685)
    ·
      refine ⟨10045962125351107777205033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107156929337078482956853685 10045962125351107777205033)
      ·
        refine ⟨7534471594013330832903775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10045962125351107777205033 7534471594013330832903775)
        ·
          refine ⟨11301707391019996249355663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534471594013330832903775 11301707391019996249355663)
          ·
            refine ⟨16952561086529994374033495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301707391019996249355663 16952561086529994374033495)
            ·
              refine ⟨25428841629794991561050243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952561086529994374033495 25428841629794991561050243)
              ·
                refine ⟨38143262444692487341575365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25428841629794991561050243 38143262444692487341575365)
                ·
                  refine ⟨7151861708379841376545381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38143262444692487341575365 7151861708379841376545381)
                  ·
                    refine ⟨1340974070321220258102259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151861708379841376545381 1340974070321220258102259)
                    ·
                      rfl

theorem cell23_7834613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7834613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834613 prefixEnd_7834613 := by exact prefixLift 7834613
  have htrace : WordTrace (prefixWord ++ tailWord_7834613) baseStart_7834613 baseEnd_7834613 := by
    simpa [prefixWord, tailWord_7834613, baseEnd_7834613] using wordTrace_append hprefix tailTrace_7834613
  have hstable : (prefixWord ++ tailWord_7834613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834613).length < 2 ^ (prefixWord ++ tailWord_7834613).sum := by decide
  have hdescent : baseEnd_7834613 < baseStart_7834613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834636 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_7834636 : Nat := 118140960795 + 7834636 * 2 ^ 59
def prefixEnd_7834636 : Nat := 4983230072969 + 3 ^ 40 * 7834636 * 2
def baseEnd_7834636 : Nat := 4022934021018714184319171

theorem tailTrace_7834636 : CollatzResearch.WordTrace tailWord_7834636 prefixEnd_7834636 4022934021018714184319171 := by
  unfold tailWord_7834636
  simp only [CollatzResearch.WordTrace]
  refine ⟨142876325222229648073181881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190501766962972864097575841 142876325222229648073181881)
  ·
    refine ⟨107157243916672236054886411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142876325222229648073181881 107157243916672236054886411)
    ·
      refine ⟨160735865875008354082329617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107157243916672236054886411 160735865875008354082329617)
      ·
        refine ⟨120551899406256265561747213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160735865875008354082329617 120551899406256265561747213)
        ·
          refine ⟨45206962277346099585655205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120551899406256265561747213 45206962277346099585655205)
          ·
            refine ⟨8476305427002393672310351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45206962277346099585655205 8476305427002393672310351)
            ·
              refine ⟨12714458140503590508465527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476305427002393672310351 12714458140503590508465527)
              ·
                refine ⟨19071687210755385762698291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12714458140503590508465527 19071687210755385762698291)
                ·
                  refine ⟨28607530816133078644047437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19071687210755385762698291 28607530816133078644047437)
                  ·
                    refine ⟨10727824056049904491517789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28607530816133078644047437 10727824056049904491517789)
                    ·
                      refine ⟨4022934021018714184319171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10727824056049904491517789 4022934021018714184319171)
                      ·
                        rfl

theorem cell23_7834636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_7834636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834636 prefixEnd_7834636 := by exact prefixLift 7834636
  have htrace : WordTrace (prefixWord ++ tailWord_7834636) baseStart_7834636 baseEnd_7834636 := by
    simpa [prefixWord, tailWord_7834636, baseEnd_7834636] using wordTrace_append hprefix tailTrace_7834636
  have hstable : (prefixWord ++ tailWord_7834636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834636).length < 2 ^ (prefixWord ++ tailWord_7834636).sum := by decide
  have hdescent : baseEnd_7834636 < baseStart_7834636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834716 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 5]
def baseStart_7834716 : Nat := 118140960795 + 7834716 * 2 ^ 59
def prefixEnd_7834716 : Nat := 4983230072969 + 3 ^ 40 * 7834716 * 2
def baseEnd_7834716 : Nat := 446997233274563763479867

theorem tailTrace_7834716 : CollatzResearch.WordTrace tailWord_7834716 prefixEnd_7834716 446997233274563763479867 := by
  unfold tailWord_7834716
  simp only [CollatzResearch.WordTrace]
  refine ⟨142877784142084734904638001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190503712189446313206184001 142877784142084734904638001)
  ·
    refine ⟨107158338106563551178478501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142877784142084734904638001 107158338106563551178478501)
    ·
      refine ⟨20092188394980665845964719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107158338106563551178478501 20092188394980665845964719)
      ·
        refine ⟨30138282592470998768947079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20092188394980665845964719 30138282592470998768947079)
        ·
          refine ⟨45207423888706498153420619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30138282592470998768947079 45207423888706498153420619)
          ·
            refine ⟨67811135833059747230130929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45207423888706498153420619 67811135833059747230130929)
            ·
              refine ⟨50858351874794810422598197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67811135833059747230130929 50858351874794810422598197)
              ·
                refine ⟨4767970488262013477118581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50858351874794810422598197 4767970488262013477118581)
                ·
                  refine ⟨446997233274563763479867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767970488262013477118581 446997233274563763479867)
                  ·
                    rfl

theorem cell23_7834716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_7834716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834716 prefixEnd_7834716 := by exact prefixLift 7834716
  have htrace : WordTrace (prefixWord ++ tailWord_7834716) baseStart_7834716 baseEnd_7834716 := by
    simpa [prefixWord, tailWord_7834716, baseEnd_7834716] using wordTrace_append hprefix tailTrace_7834716
  have hstable : (prefixWord ++ tailWord_7834716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834716).length < 2 ^ (prefixWord ++ tailWord_7834716).sum := by decide
  have hdescent : baseEnd_7834716 < baseStart_7834716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834729 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_7834729 : Nat := 118140960795 + 7834729 * 2 ^ 59
def prefixEnd_7834729 : Nat := 4983230072969 + 3 ^ 40 * 7834729 * 2
def baseEnd_7834729 : Nat := 1340993924906527440152081

theorem tailTrace_7834729 : CollatzResearch.WordTrace tailWord_7834729 prefixEnd_7834729 1340993924906527440152081 := by
  unfold tailWord_7834729
  simp only [CollatzResearch.WordTrace]
  refine ⟨285756042433122373029499241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190504028288748248686332827 285756042433122373029499241)
  ·
    refine ⟨214317031824841779772124431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285756042433122373029499241 214317031824841779772124431)
    ·
      refine ⟨321475547737262669658186647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214317031824841779772124431 321475547737262669658186647)
      ·
        refine ⟨482213321605894004487279971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321475547737262669658186647 482213321605894004487279971)
        ·
          refine ⟨723319982408841006730919957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482213321605894004487279971 723319982408841006730919957)
          ·
            refine ⟨33905624175414422190511873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 723319982408841006730919957 33905624175414422190511873)
            ·
              refine ⟨25429218131560816642883905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33905624175414422190511873 25429218131560816642883905)
              ·
                refine ⟨19071913598670612482162929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25429218131560816642883905 19071913598670612482162929)
                ·
                  refine ⟨14303935199002959361622197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19071913598670612482162929 14303935199002959361622197)
                  ·
                    refine ⟨1340993924906527440152081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14303935199002959361622197 1340993924906527440152081)
                    ·
                      rfl

theorem cell23_7834729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_7834729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834729 prefixEnd_7834729 := by exact prefixLift 7834729
  have htrace : WordTrace (prefixWord ++ tailWord_7834729) baseStart_7834729 baseEnd_7834729 := by
    simpa [prefixWord, tailWord_7834729, baseEnd_7834729] using wordTrace_append hprefix tailTrace_7834729
  have hstable : (prefixWord ++ tailWord_7834729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834729).length < 2 ^ (prefixWord ++ tailWord_7834729).sum := by decide
  have hdescent : baseEnd_7834729 < baseStart_7834729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834733 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 5]
def baseStart_7834733 : Nat := 118140960795 + 7834733 * 2 ^ 59
def prefixEnd_7834733 : Nat := 4983230072969 + 3 ^ 40 * 7834733 * 2
def baseEnd_7834733 : Nat := 446998203182466700534025

theorem tailTrace_7834733 : CollatzResearch.WordTrace tailWord_7834733 prefixEnd_7834733 446998203182466700534025 := by
  unfold tailWord_7834733
  simp only [CollatzResearch.WordTrace]
  refine ⟨285756188325107881712644853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190504125550071921141763235 285756188325107881712644853)
  ·
    refine ⟨26789642655478863910560455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285756188325107881712644853 26789642655478863910560455)
    ·
      refine ⟨40184463983218295865840683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26789642655478863910560455 40184463983218295865840683)
      ·
        refine ⟨60276695974827443798761025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40184463983218295865840683 60276695974827443798761025)
        ·
          refine ⟨45207521981120582849070769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60276695974827443798761025 45207521981120582849070769)
          ·
            refine ⟨33905641485840437136803077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45207521981120582849070769 33905641485840437136803077)
            ·
              refine ⟨6357307778595081963150577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33905641485840437136803077 6357307778595081963150577)
              ·
                refine ⟨4767980833946311472362933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357307778595081963150577 4767980833946311472362933)
                ·
                  refine ⟨446998203182466700534025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767980833946311472362933 446998203182466700534025)
                  ·
                    rfl

theorem cell23_7834733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_7834733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834733 prefixEnd_7834733 := by exact prefixLift 7834733
  have htrace : WordTrace (prefixWord ++ tailWord_7834733) baseStart_7834733 baseEnd_7834733 := by
    simpa [prefixWord, tailWord_7834733, baseEnd_7834733] using wordTrace_append hprefix tailTrace_7834733
  have hstable : (prefixWord ++ tailWord_7834733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834733).length < 2 ^ (prefixWord ++ tailWord_7834733).sum := by decide
  have hdescent : baseEnd_7834733 < baseStart_7834733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834749 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7834749 : Nat := 118140960795 + 7834749 * 2 ^ 59
def prefixEnd_7834749 : Nat := 4983230072969 + 3 ^ 40 * 7834749 * 2
def baseEnd_7834749 : Nat := 4022992044332672242206151

theorem tailTrace_7834749 : CollatzResearch.WordTrace tailWord_7834749 prefixEnd_7834749 4022992044332672242206151 := by
  unfold tailWord_7834749
  simp only [CollatzResearch.WordTrace]
  refine ⟨285756771893049916445227301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190504514595366610963484867 285756771893049916445227301)
  ·
    refine ⟨53579394729946859333480119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285756771893049916445227301 53579394729946859333480119)
    ·
      refine ⟨80369092094920289000220179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53579394729946859333480119 80369092094920289000220179)
      ·
        refine ⟨120553638142380433500330269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80369092094920289000220179 120553638142380433500330269)
        ·
          refine ⟨45207614303392662562623851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120553638142380433500330269 45207614303392662562623851)
          ·
            refine ⟨67811421455088993843935777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45207614303392662562623851 67811421455088993843935777)
            ·
              refine ⟨50858566091316745382951833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67811421455088993843935777 50858566091316745382951833)
              ·
                refine ⟨38143924568487559037213875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50858566091316745382951833 38143924568487559037213875)
                ·
                  refine ⟨57215886852731338555820813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38143924568487559037213875 57215886852731338555820813)
                  ·
                    refine ⟨21455957569774251958432805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57215886852731338555820813 21455957569774251958432805)
                    ·
                      refine ⟨4022992044332672242206151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21455957569774251958432805 4022992044332672242206151)
                      ·
                        rfl

theorem cell23_7834749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7834749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834749 prefixEnd_7834749 := by exact prefixLift 7834749
  have htrace : WordTrace (prefixWord ++ tailWord_7834749) baseStart_7834749 baseEnd_7834749 := by
    simpa [prefixWord, tailWord_7834749, baseEnd_7834749] using wordTrace_append hprefix tailTrace_7834749
  have hstable : (prefixWord ++ tailWord_7834749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834749).length < 2 ^ (prefixWord ++ tailWord_7834749).sum := by decide
  have hdescent : baseEnd_7834749 < baseStart_7834749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834750 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_7834750 : Nat := 118140960795 + 7834750 * 2 ^ 59
def prefixEnd_7834750 : Nat := 4983230072969 + 3 ^ 40 * 7834750 * 2
def baseEnd_7834750 : Nat := 446999173090369637588183

theorem tailTrace_7834750 : CollatzResearch.WordTrace tailWord_7834750 prefixEnd_7834750 446999173090369637588183 := by
  unfold tailWord_7834750
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719601045755786702001713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190504538910697529077342469 35719601045755786702001713)
  ·
    refine ⟨26789700784316840026501285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35719601045755786702001713 26789700784316840026501285)
    ·
      refine ⟨5023068897059407504968991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26789700784316840026501285 5023068897059407504968991)
      ·
        refine ⟨7534603345589111257453487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023068897059407504968991 7534603345589111257453487)
        ·
          refine ⟨11301905018383666886180231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534603345589111257453487 11301905018383666886180231)
          ·
            refine ⟨16952857527575500329270347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301905018383666886180231 16952857527575500329270347)
            ·
              refine ⟨25429286291363250493905521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952857527575500329270347 25429286291363250493905521)
              ·
                refine ⟨19071964718522437870429141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25429286291363250493905521 19071964718522437870429141)
                ·
                  refine ⟨446999173090369637588183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19071964718522437870429141 446999173090369637588183)
                  ·
                    rfl

theorem cell23_7834750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_7834750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834750 prefixEnd_7834750 := by exact prefixLift 7834750
  have htrace : WordTrace (prefixWord ++ tailWord_7834750) baseStart_7834750 baseEnd_7834750 := by
    simpa [prefixWord, tailWord_7834750, baseEnd_7834750] using wordTrace_append hprefix tailTrace_7834750
  have hstable : (prefixWord ++ tailWord_7834750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834750).length < 2 ^ (prefixWord ++ tailWord_7834750).sum := by decide
  have hdescent : baseEnd_7834750 < baseStart_7834750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834766 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7834766 : Nat := 118140960795 + 7834766 * 2 ^ 59
def prefixEnd_7834766 : Nat := 4983230072969 + 3 ^ 40 * 7834766 * 2
def baseEnd_7834766 : Nat := 4023000773503798675693573

theorem tailTrace_7834766 : CollatzResearch.WordTrace tailWord_7834766 prefixEnd_7834766 4023000773503798675693573 := by
  unfold tailWord_7834766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719673991748541043574519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190504927955992218899064101 35719673991748541043574519)
  ·
    refine ⟨53579510987622811565361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35719673991748541043574519 53579510987622811565361779)
    ·
      refine ⟨80369266481434217348042669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53579510987622811565361779 80369266481434217348042669)
      ·
        refine ⟨30138474930537831505516001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80369266481434217348042669 30138474930537831505516001)
        ·
          refine ⟨22603856197903373629137001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30138474930537831505516001 22603856197903373629137001)
          ·
            refine ⟨16952892148427530221852751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22603856197903373629137001 16952892148427530221852751)
            ·
              refine ⟨25429338222641295332779127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952892148427530221852751 25429338222641295332779127)
              ·
                refine ⟨38144007333961942999168691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25429338222641295332779127 38144007333961942999168691)
                ·
                  refine ⟨57216011000942914498753037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38144007333961942999168691 57216011000942914498753037)
                  ·
                    refine ⟨21456004125353592937032389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57216011000942914498753037 21456004125353592937032389)
                    ·
                      refine ⟨4023000773503798675693573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21456004125353592937032389 4023000773503798675693573)
                      ·
                        rfl

theorem cell23_7834766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7834766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834766 prefixEnd_7834766 := by exact prefixLift 7834766
  have htrace : WordTrace (prefixWord ++ tailWord_7834766) baseStart_7834766 baseEnd_7834766 := by
    simpa [prefixWord, tailWord_7834766, baseEnd_7834766] using wordTrace_append hprefix tailTrace_7834766
  have hstable : (prefixWord ++ tailWord_7834766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834766).length < 2 ^ (prefixWord ++ tailWord_7834766).sum := by decide
  have hdescent : baseEnd_7834766 < baseStart_7834766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834789 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 8]
def baseStart_7834789 : Nat := 118140960795 + 7834789 * 2 ^ 59
def prefixEnd_7834789 : Nat := 4983230072969 + 3 ^ 40 * 7834789 * 2
def baseEnd_7834789 : Nat := 447001398173205787300663

theorem tailTrace_7834789 : CollatzResearch.WordTrace tailWord_7834789 prefixEnd_7834789 447001398173205787300663 := by
  unfold tailWord_7834789
  simp only [CollatzResearch.WordTrace]
  refine ⟨285758230812905003276683421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190505487208603335517788947 285758230812905003276683421)
  ·
    refine ⟨107159336554839376228756283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285758230812905003276683421 107159336554839376228756283)
    ·
      refine ⟨160739004832259064343134425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107159336554839376228756283 160739004832259064343134425)
      ·
        refine ⟨120554253624194298257350819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160739004832259064343134425 120554253624194298257350819)
        ·
          refine ⟨180831380436291447386026229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120554253624194298257350819 180831380436291447386026229)
          ·
            refine ⟨16952941915902323192439959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180831380436291447386026229 16952941915902323192439959)
            ·
              refine ⟨25429412873853484788659939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16952941915902323192439959 25429412873853484788659939)
              ·
                refine ⟨38144119310780227182989909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25429412873853484788659939 38144119310780227182989909)
                ·
                  refine ⟨447001398173205787300663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38144119310780227182989909 447001398173205787300663)
                  ·
                    rfl

theorem cell23_7834789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_7834789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834789 prefixEnd_7834789 := by exact prefixLift 7834789
  have htrace : WordTrace (prefixWord ++ tailWord_7834789) baseStart_7834789 baseEnd_7834789 := by
    simpa [prefixWord, tailWord_7834789, baseEnd_7834789] using wordTrace_append hprefix tailTrace_7834789
  have hstable : (prefixWord ++ tailWord_7834789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834789).length < 2 ^ (prefixWord ++ tailWord_7834789).sum := by decide
  have hdescent : baseEnd_7834789 < baseStart_7834789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834856 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7834856 : Nat := 118140960795 + 7834856 * 2 ^ 59
def prefixEnd_7834856 : Nat := 4983230072969 + 3 ^ 40 * 7834856 * 2
def baseEnd_7834856 : Nat := 4023046986762703323568159

theorem tailTrace_7834856 : CollatzResearch.WordTrace tailWord_7834856 prefixEnd_7834856 4023046986762703323568159 := by
  unfold tailWord_7834856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142880337251831136859686211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190507116335774849146248281 142880337251831136859686211)
  ·
    refine ⟨214320505877746705289529317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142880337251831136859686211 214320505877746705289529317)
    ·
      refine ⟨40185094852077507241786747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214320505877746705289529317 40185094852077507241786747)
      ·
        refine ⟨60277642278116260862680121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40185094852077507241786747 60277642278116260862680121)
        ·
          refine ⟨45208231708587195647010091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60277642278116260862680121 45208231708587195647010091)
          ·
            refine ⟨67812347562880793470515137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45208231708587195647010091 67812347562880793470515137)
            ·
              refine ⟨50859260672160595102886353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67812347562880793470515137 50859260672160595102886353)
              ·
                refine ⟨38144445504120446327164765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50859260672160595102886353 38144445504120446327164765)
                ·
                  refine ⟨14304167064045167372686787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38144445504120446327164765 14304167064045167372686787)
                  ·
                    refine ⟨21456250596067751059030181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14304167064045167372686787 21456250596067751059030181)
                    ·
                      refine ⟨4023046986762703323568159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21456250596067751059030181 4023046986762703323568159)
                      ·
                        rfl

theorem cell23_7834856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7834856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834856 prefixEnd_7834856 := by exact prefixLift 7834856
  have htrace : WordTrace (prefixWord ++ tailWord_7834856) baseStart_7834856 baseEnd_7834856 := by
    simpa [prefixWord, tailWord_7834856, baseEnd_7834856] using wordTrace_append hprefix tailTrace_7834856
  have hstable : (prefixWord ++ tailWord_7834856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834856).length < 2 ^ (prefixWord ++ tailWord_7834856).sum := by decide
  have hdescent : baseEnd_7834856 < baseStart_7834856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834873 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 5, 2, 2]
def baseStart_7834873 : Nat := 118140960795 + 7834873 * 2 ^ 59
def prefixEnd_7834873 : Nat := 4983230072969 + 3 ^ 40 * 7834873 * 2
def baseEnd_7834873 : Nat := 4023055715933829757055581

theorem tailTrace_7834873 : CollatzResearch.WordTrace tailWord_7834873 prefixEnd_7834873 4023055715933829757055581 := by
  unfold tailWord_7834873
  simp only [CollatzResearch.WordTrace]
  refine ⟨285761294544600685622741273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190507529696400457081827515 285761294544600685622741273)
  ·
    refine ⟨214320970908450514217055955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285761294544600685622741273 214320970908450514217055955)
    ·
      refine ⟨321481456362675771325583933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214320970908450514217055955 321481456362675771325583933)
      ·
        refine ⟨120555546136003414247093975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321481456362675771325583933 120555546136003414247093975)
        ·
          refine ⟨180833319204005121370640963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120555546136003414247093975 180833319204005121370640963)
          ·
            refine ⟨271249978806007682055961445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180833319204005121370640963 271249978806007682055961445)
            ·
              refine ⟨50859371026126440385492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271249978806007682055961445 50859371026126440385492771)
              ·
                refine ⟨76289056539189660578239157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50859371026126440385492771 76289056539189660578239157)
                ·
                  refine ⟨7152099050549030679209921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76289056539189660578239157 7152099050549030679209921)
                  ·
                    refine ⟨5364074287911773009407441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152099050549030679209921 5364074287911773009407441)
                    ·
                      refine ⟨4023055715933829757055581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364074287911773009407441 4023055715933829757055581)
                      ·
                        rfl

theorem cell23_7834873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_7834873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834873 prefixEnd_7834873 := by exact prefixLift 7834873
  have htrace : WordTrace (prefixWord ++ tailWord_7834873) baseStart_7834873 baseEnd_7834873 := by
    simpa [prefixWord, tailWord_7834873, baseEnd_7834873] using wordTrace_append hprefix tailTrace_7834873
  have hstable : (prefixWord ++ tailWord_7834873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834873).length < 2 ^ (prefixWord ++ tailWord_7834873).sum := by decide
  have hdescent : baseEnd_7834873 < baseStart_7834873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834879 : List Nat := [1, 1, 2, 2, 1, 5, 2, 9]
def baseStart_7834879 : Nat := 118140960795 + 7834879 * 2 ^ 59
def prefixEnd_7834879 : Nat := 4983230072969 + 3 ^ 40 * 7834879 * 2
def baseEnd_7834879 : Nat := 149002177659916916058539

theorem tailTrace_7834879 : CollatzResearch.WordTrace tailWord_7834879 prefixEnd_7834879 149002177659916916058539 := by
  unfold tailWord_7834879
  simp only [CollatzResearch.WordTrace]
  refine ⟨285761513382578948647459691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190507675588385965764973127 285761513382578948647459691)
  ·
    refine ⟨428642270073868422971189537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285761513382578948647459691 428642270073868422971189537)
    ·
      refine ⟨321481702555401317228392153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428642270073868422971189537 321481702555401317228392153)
      ·
        refine ⟨241111276916550987921294115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321481702555401317228392153 241111276916550987921294115)
        ·
          refine ⟨361666915374826481881941173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241111276916550987921294115 361666915374826481881941173)
          ·
            refine ⟨33906273316389982676431985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361666915374826481881941173 33906273316389982676431985)
            ·
              refine ⟨25429704987292487007323989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33906273316389982676431985 25429704987292487007323989)
              ·
                refine ⟨149002177659916916058539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25429704987292487007323989 149002177659916916058539)
                ·
                  rfl

theorem cell23_7834879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 9].length) (baseStart_7834879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834879 prefixEnd_7834879 := by exact prefixLift 7834879
  have htrace : WordTrace (prefixWord ++ tailWord_7834879) baseStart_7834879 baseEnd_7834879 := by
    simpa [prefixWord, tailWord_7834879, baseEnd_7834879] using wordTrace_append hprefix tailTrace_7834879
  have hstable : (prefixWord ++ tailWord_7834879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834879).length < 2 ^ (prefixWord ++ tailWord_7834879).sum := by decide
  have hdescent : baseEnd_7834879 < baseStart_7834879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834941 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7834941 : Nat := 118140960795 + 7834941 * 2 ^ 59
def prefixEnd_7834941 : Nat := 4983230072969 + 3 ^ 40 * 7834941 * 2
def baseEnd_7834941 : Nat := 4023090632618335491005269

theorem tailTrace_7834941 : CollatzResearch.WordTrace tailWord_7834941 prefixEnd_7834941 4023090632618335491005269 := by
  unfold tailWord_7834941
  simp only [CollatzResearch.WordTrace]
  refine ⟨285763774708354333236216677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190509183138902888824144451 285763774708354333236216677)
  ·
    refine ⟨53580707757816437481790627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285763774708354333236216677 53580707757816437481790627)
    ·
      refine ⟨80371061636724656222685941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53580707757816437481790627 80371061636724656222685941)
      ·
        refine ⟨7534787028442936520876807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80371061636724656222685941 7534787028442936520876807)
        ·
          refine ⟨11302180542664404781315211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7534787028442936520876807 11302180542664404781315211)
          ·
            refine ⟨16953270813996607171972817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302180542664404781315211 16953270813996607171972817)
            ·
              refine ⟨12714953110497455378979613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16953270813996607171972817 12714953110497455378979613)
              ·
                refine ⟨4768107416436545767117355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12714953110497455378979613 4768107416436545767117355)
                ·
                  refine ⟨7152161124654818650676033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768107416436545767117355 7152161124654818650676033)
                  ·
                    refine ⟨5364120843491113988007025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152161124654818650676033 5364120843491113988007025)
                    ·
                      refine ⟨4023090632618335491005269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364120843491113988007025 4023090632618335491005269)
                      ·
                        rfl

theorem cell23_7834941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7834941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834941 prefixEnd_7834941 := by exact prefixLift 7834941
  have htrace : WordTrace (prefixWord ++ tailWord_7834941) baseStart_7834941 baseEnd_7834941 := by
    simpa [prefixWord, tailWord_7834941, baseEnd_7834941] using wordTrace_append hprefix tailTrace_7834941
  have hstable : (prefixWord ++ tailWord_7834941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834941).length < 2 ^ (prefixWord ++ tailWord_7834941).sum := by decide
  have hdescent : baseEnd_7834941 < baseStart_7834941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834956 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_7834956 : Nat := 118140960795 + 7834956 * 2 ^ 59
def prefixEnd_7834956 : Nat := 4983230072969 + 3 ^ 40 * 7834956 * 2
def baseEnd_7834956 : Nat := 1341032778276050977439233

theorem tailTrace_7834956 : CollatzResearch.WordTrace tailWord_7834956 prefixEnd_7834956 1341032778276050977439233 := by
  unfold tailWord_7834956
  simp only [CollatzResearch.WordTrace]
  refine ⟨142882160901649995399006361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190509547868866660532008481 142882160901649995399006361)
  ·
    refine ⟨107161620676237496549254771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142882160901649995399006361 107161620676237496549254771)
    ·
      refine ⟨160742431014356244823882157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107161620676237496549254771 160742431014356244823882157)
      ·
        refine ⟨60278411630383591808955809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160742431014356244823882157 60278411630383591808955809)
        ·
          refine ⟨45208808722787693856716857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60278411630383591808955809 45208808722787693856716857)
          ·
            refine ⟨33906606542090770392537643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45208808722787693856716857 33906606542090770392537643)
            ·
              refine ⟨50859909813136155588806465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33906606542090770392537643 50859909813136155588806465)
              ·
                refine ⟨38144932359852116691604849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50859909813136155588806465 38144932359852116691604849)
                ·
                  refine ⟨28608699269889087518703637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38144932359852116691604849 28608699269889087518703637)
                  ·
                    refine ⟨1341032778276050977439233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28608699269889087518703637 1341032778276050977439233)
                    ·
                      rfl

theorem cell23_7834956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_7834956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834956 prefixEnd_7834956 := by exact prefixLift 7834956
  have htrace : WordTrace (prefixWord ++ tailWord_7834956) baseStart_7834956 baseEnd_7834956 := by
    simpa [prefixWord, tailWord_7834956, baseEnd_7834956] using wordTrace_append hprefix tailTrace_7834956
  have hstable : (prefixWord ++ tailWord_7834956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834956).length < 2 ^ (prefixWord ++ tailWord_7834956).sum := by decide
  have hdescent : baseEnd_7834956 < baseStart_7834956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7834980 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_7834980 : Nat := 118140960795 + 7834980 * 2 ^ 59
def prefixEnd_7834980 : Nat := 4983230072969 + 3 ^ 40 * 7834980 * 2
def baseEnd_7834980 : Nat := 4023110658363860838417589

theorem tailTrace_7834980 : CollatzResearch.WordTrace tailWord_7834980 prefixEnd_7834980 4023110658363860838417589 := by
  unfold tailWord_7834980
  simp only [CollatzResearch.WordTrace]
  refine ⟨142882598577606521448443197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190510131436808695264590929 142882598577606521448443197)
  ·
    refine ⟨53580974466602445543166199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142882598577606521448443197 53580974466602445543166199)
    ·
      refine ⟨80371461699903668314749299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53580974466602445543166199 80371461699903668314749299)
      ·
        refine ⟨120557192549855502472123949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80371461699903668314749299 120557192549855502472123949)
        ·
          refine ⟨45208947206195813427046481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120557192549855502472123949 45208947206195813427046481)
          ·
            refine ⟨33906710404646860070284861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45208947206195813427046481 33906710404646860070284861)
            ·
              refine ⟨12715016401742572526356823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33906710404646860070284861 12715016401742572526356823)
              ·
                refine ⟨19072524602613858789535235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715016401742572526356823 19072524602613858789535235)
                ·
                  refine ⟨28608786903920788184302853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19072524602613858789535235 28608786903920788184302853)
                  ·
                    refine ⟨5364147544485147784556785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28608786903920788184302853 5364147544485147784556785)
                    ·
                      refine ⟨4023110658363860838417589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364147544485147784556785 4023110658363860838417589)
                      ·
                        rfl

theorem cell23_7834980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_7834980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7834980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7834980 prefixEnd_7834980 := by exact prefixLift 7834980
  have htrace : WordTrace (prefixWord ++ tailWord_7834980) baseStart_7834980 baseEnd_7834980 := by
    simpa [prefixWord, tailWord_7834980, baseEnd_7834980] using wordTrace_append hprefix tailTrace_7834980
  have hstable : (prefixWord ++ tailWord_7834980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7834980).length < 2 ^ (prefixWord ++ tailWord_7834980).sum := by decide
  have hdescent : baseEnd_7834980 < baseStart_7834980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7834980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835020 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 5]
def baseStart_7835020 : Nat := 118140960795 + 7835020 * 2 ^ 59
def prefixEnd_7835020 : Nat := 4983230072969 + 3 ^ 40 * 7835020 * 2
def baseEnd_7835020 : Nat := 447014577510004520213045

theorem tailTrace_7835020 : CollatzResearch.WordTrace tailWord_7835020 prefixEnd_7835020 447014577510004520213045 := by
  unfold tailWord_7835020
  simp only [CollatzResearch.WordTrace]
  refine ⟨142883328037534064864171257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190511104050045419818895009 142883328037534064864171257)
  ·
    refine ⟨107162496028150548648128443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142883328037534064864171257 107162496028150548648128443)
    ·
      refine ⟨160743744042225822972192665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107162496028150548648128443 160743744042225822972192665)
      ·
        refine ⟨120557808031669367229144499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160743744042225822972192665 120557808031669367229144499)
        ·
          refine ⟨180836712047504050843716749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120557808031669367229144499 180836712047504050843716749)
          ·
            refine ⟨67813767017814019066393781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180836712047504050843716749 67813767017814019066393781)
            ·
              refine ⟨6357540657920064287474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67813767017814019066393781 6357540657920064287474417)
              ·
                refine ⟨4768155493440048215605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357540657920064287474417 4768155493440048215605813)
                ·
                  refine ⟨447014577510004520213045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768155493440048215605813 447014577510004520213045)
                  ·
                    rfl

theorem cell23_7835020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_7835020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835020 prefixEnd_7835020 := by exact prefixLift 7835020
  have htrace : WordTrace (prefixWord ++ tailWord_7835020) baseStart_7835020 baseEnd_7835020 := by
    simpa [prefixWord, tailWord_7835020, baseEnd_7835020] using wordTrace_append hprefix tailTrace_7835020
  have hstable : (prefixWord ++ tailWord_7835020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835020).length < 2 ^ (prefixWord ++ tailWord_7835020).sum := by decide
  have hdescent : baseEnd_7835020 < baseStart_7835020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835070 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7835070 : Nat := 118140960795 + 7835070 * 2 ^ 59
def prefixEnd_7835070 : Nat := 4983230072969 + 3 ^ 40 * 7835070 * 2
def baseEnd_7835070 : Nat := 4023156871622765486292175

theorem tailTrace_7835070 : CollatzResearch.WordTrace tailWord_7835070 prefixEnd_7835070 4023156871622765486292175 := by
  unfold tailWord_7835070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721059965610873533457833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190512319816591325511775109 35721059965610873533457833)
  ·
    refine ⟨26790794974208155150093375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35721059965610873533457833 26790794974208155150093375)
    ·
      refine ⟨40186192461312232725140063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26790794974208155150093375 40186192461312232725140063)
      ·
        refine ⟨60279288691968349087710095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40186192461312232725140063 60279288691968349087710095)
        ·
          refine ⟨90418933037952523631565143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60279288691968349087710095 90418933037952523631565143)
          ·
            refine ⟨135628399556928785447347715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90418933037952523631565143 135628399556928785447347715)
            ·
              refine ⟨203442599335393178171021573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135628399556928785447347715 203442599335393178171021573)
              ·
                refine ⟨38145487375386220907066545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203442599335393178171021573 38145487375386220907066545)
                ·
                  refine ⟨28609115531539665680299909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38145487375386220907066545 28609115531539665680299909)
                  ·
                    refine ⟨5364209162163687315056233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28609115531539665680299909 5364209162163687315056233)
                    ·
                      refine ⟨4023156871622765486292175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364209162163687315056233 4023156871622765486292175)
                      ·
                        rfl

theorem cell23_7835070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7835070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835070 prefixEnd_7835070 := by exact prefixLift 7835070
  have htrace : WordTrace (prefixWord ++ tailWord_7835070) baseStart_7835070 baseEnd_7835070 := by
    simpa [prefixWord, tailWord_7835070, baseEnd_7835070] using wordTrace_append hprefix tailTrace_7835070
  have hstable : (prefixWord ++ tailWord_7835070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835070).length < 2 ^ (prefixWord ++ tailWord_7835070).sum := by decide
  have hdescent : baseEnd_7835070 < baseStart_7835070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835093 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 6]
def baseStart_7835093 : Nat := 118140960795 + 7835093 * 2 ^ 59
def prefixEnd_7835093 : Nat := 4983230072969 + 3 ^ 40 * 7835093 * 2
def baseEnd_7835093 : Nat := 447018742408646544033841

theorem tailTrace_7835093 : CollatzResearch.WordTrace tailWord_7835093 prefixEnd_7835093 447018742408646544033841 := by
  unfold tailWord_7835093
  simp only [CollatzResearch.WordTrace]
  refine ⟨285769318603803663195749933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190512879069202442130499955 285769318603803663195749933)
  ·
    refine ⟨107163494476426373698406225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285769318603803663195749933 107163494476426373698406225)
    ·
      refine ⟨80372620857319780273804669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107163494476426373698406225 80372620857319780273804669)
      ·
        refine ⟨30139732821494917602676751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80372620857319780273804669 30139732821494917602676751)
        ·
          refine ⟨45209599232242376404015127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30139732821494917602676751 45209599232242376404015127)
          ·
            refine ⟨67814398848363564606022691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45209599232242376404015127 67814398848363564606022691)
            ·
              refine ⟨101721598272545346909034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67814398848363564606022691 101721598272545346909034037)
              ·
                refine ⟨9536399838051126272721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101721598272545346909034037 9536399838051126272721941)
                ·
                  refine ⟨447018742408646544033841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9536399838051126272721941 447018742408646544033841)
                  ·
                    rfl

theorem cell23_7835093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_7835093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835093 prefixEnd_7835093 := by exact prefixLift 7835093
  have htrace : WordTrace (prefixWord ++ tailWord_7835093) baseStart_7835093 baseEnd_7835093 := by
    simpa [prefixWord, tailWord_7835093, baseEnd_7835093] using wordTrace_append hprefix tailTrace_7835093
  have hstable : (prefixWord ++ tailWord_7835093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835093).length < 2 ^ (prefixWord ++ tailWord_7835093).sum := by decide
  have hdescent : baseEnd_7835093 < baseStart_7835093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835107 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7835107 : Nat := 118140960795 + 7835107 * 2 ^ 59
def prefixEnd_7835107 : Nat := 4983230072969 + 3 ^ 40 * 7835107 * 2
def baseEnd_7835107 : Nat := 4023175870406981841529505

theorem tailTrace_7835107 : CollatzResearch.WordTrace tailWord_7835107 prefixEnd_7835107 4023175870406981841529505 := by
  unfold tailWord_7835107
  simp only [CollatzResearch.WordTrace]
  refine ⟨285769829225752943586759575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190513219483835295724506383 285769829225752943586759575)
  ·
    refine ⟨428654743838629415380139363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285769829225752943586759575 428654743838629415380139363)
    ·
      refine ⟨642982115757944123070209045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428654743838629415380139363 642982115757944123070209045)
      ·
        refine ⟨30139786676153630768916049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 642982115757944123070209045 30139786676153630768916049)
        ·
          refine ⟨22604840007115223076687037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30139786676153630768916049 22604840007115223076687037)
          ·
            refine ⟨8476815002668208653757639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22604840007115223076687037 8476815002668208653757639)
            ·
              refine ⟨12715222504002312980636459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476815002668208653757639 12715222504002312980636459)
              ·
                refine ⟨19072833756003469470954689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715222504002312980636459 19072833756003469470954689)
                ·
                  refine ⟨14304625317002602103216017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19072833756003469470954689 14304625317002602103216017)
                  ·
                    refine ⟨10728468987751951577412013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14304625317002602103216017 10728468987751951577412013)
                    ·
                      refine ⟨4023175870406981841529505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10728468987751951577412013 4023175870406981841529505)
                      ·
                        rfl

theorem cell23_7835107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7835107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835107 prefixEnd_7835107 := by exact prefixLift 7835107
  have htrace : WordTrace (prefixWord ++ tailWord_7835107) baseStart_7835107 baseEnd_7835107 := by
    simpa [prefixWord, tailWord_7835107, baseEnd_7835107] using wordTrace_append hprefix tailTrace_7835107
  have hstable : (prefixWord ++ tailWord_7835107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835107).length < 2 ^ (prefixWord ++ tailWord_7835107).sum := by decide
  have hdescent : baseEnd_7835107 < baseStart_7835107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835114 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_7835114 : Nat := 118140960795 + 7835114 * 2 ^ 59
def prefixEnd_7835114 : Nat := 4983230072969 + 3 ^ 40 * 7835114 * 2
def baseEnd_7835114 : Nat := 1341059821590521104713991

theorem tailTrace_7835114 : CollatzResearch.WordTrace tailWord_7835114 prefixEnd_7835114 1341059821590521104713991 := by
  unfold tailWord_7835114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71442521134181895945566099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190513389691151722521509597 71442521134181895945566099)
  ·
    refine ⟨107163781701272843918349149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71442521134181895945566099 107163781701272843918349149)
    ·
      refine ⟨40186418137977316469380931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107163781701272843918349149 40186418137977316469380931)
      ·
        refine ⟨60279627206965974704071397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40186418137977316469380931 60279627206965974704071397)
        ·
          refine ⟨11302430101306120257013387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60279627206965974704071397 11302430101306120257013387)
          ·
            refine ⟨16953645151959180385520081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302430101306120257013387 16953645151959180385520081)
            ·
              refine ⟨12715233863969385289140061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16953645151959180385520081 12715233863969385289140061)
              ·
                refine ⟨4768212698988519483427523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12715233863969385289140061 4768212698988519483427523)
                ·
                  refine ⟨7152319048482779225141285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768212698988519483427523 7152319048482779225141285)
                  ·
                    refine ⟨1341059821590521104713991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152319048482779225141285 1341059821590521104713991)
                    ·
                      rfl

theorem cell23_7835114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_7835114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835114 prefixEnd_7835114 := by exact prefixLift 7835114
  have htrace : WordTrace (prefixWord ++ tailWord_7835114) baseStart_7835114 baseEnd_7835114 := by
    simpa [prefixWord, tailWord_7835114, baseEnd_7835114] using wordTrace_append hprefix tailTrace_7835114
  have hstable : (prefixWord ++ tailWord_7835114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835114).length < 2 ^ (prefixWord ++ tailWord_7835114).sum := by decide
  have hdescent : baseEnd_7835114 < baseStart_7835114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835130 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_7835130 : Nat := 118140960795 + 7835130 * 2 ^ 59
def prefixEnd_7835130 : Nat := 4983230072969 + 3 ^ 40 * 7835130 * 2
def baseEnd_7835130 : Nat := 4023187680462035251541899

theorem tailTrace_7835130 : CollatzResearch.WordTrace tailWord_7835130 prefixEnd_7835130 4023187680462035251541899 := by
  unfold tailWord_7835130
  simp only [CollatzResearch.WordTrace]
  refine ⟨71442667026167404628711711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190513778736446412343231229 71442667026167404628711711)
  ·
    refine ⟨107164000539251106943067567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71442667026167404628711711 107164000539251106943067567)
    ·
      refine ⟨160746000808876660414601351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107164000539251106943067567 160746000808876660414601351)
      ·
        refine ⟨241119001213314990621902027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160746000808876660414601351 241119001213314990621902027)
        ·
          refine ⟨361678501819972485932853041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241119001213314990621902027 361678501819972485932853041)
          ·
            refine ⟨271258876364979364449639781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361678501819972485932853041 271258876364979364449639781)
            ·
              refine ⟨50861039318433630834307459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271258876364979364449639781 50861039318433630834307459)
              ·
                refine ⟨76291558977650446251461189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50861039318433630834307459 76291558977650446251461189)
                ·
                  refine ⟨14304667308309458672148973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76291558977650446251461189 14304667308309458672148973)
                  ·
                    refine ⟨5364250240616047002055865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14304667308309458672148973 5364250240616047002055865)
                    ·
                      refine ⟨4023187680462035251541899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364250240616047002055865 4023187680462035251541899)
                      ·
                        rfl

theorem cell23_7835130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_7835130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835130 prefixEnd_7835130 := by exact prefixLift 7835130
  have htrace : WordTrace (prefixWord ++ tailWord_7835130) baseStart_7835130 baseEnd_7835130 := by
    simpa [prefixWord, tailWord_7835130, baseEnd_7835130] using wordTrace_append hprefix tailTrace_7835130
  have hstable : (prefixWord ++ tailWord_7835130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835130).length < 2 ^ (prefixWord ++ tailWord_7835130).sum := by decide
  have hdescent : baseEnd_7835130 < baseStart_7835130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_7835136 : Nat := 118140960795 + 7835136 * 2 ^ 59
def prefixEnd_7835136 : Nat := 4983230072969 + 3 ^ 40 * 7835136 * 2
def baseEnd_7835136 : Nat := 1341063587115320742688957

theorem tailTrace_7835136 : CollatzResearch.WordTrace tailWord_7835136 prefixEnd_7835136 1341063587115320742688957 := by
  unfold tailWord_7835136
  simp only [CollatzResearch.WordTrace]
  refine ⟨142885443471323940769782631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190513924628431921026376841 142885443471323940769782631)
  ·
    refine ⟨214328165206985911154673947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142885443471323940769782631 214328165206985911154673947)
    ·
      refine ⟨321492247810478866732010921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214328165206985911154673947 321492247810478866732010921)
      ·
        refine ⟨241119185857859150049008191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321492247810478866732010921 241119185857859150049008191)
        ·
          refine ⟨361678778786788725073512287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241119185857859150049008191 361678778786788725073512287)
          ·
            refine ⟨542518168180183087610268431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361678778786788725073512287 542518168180183087610268431)
            ·
              refine ⟨813777252270274631415402647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542518168180183087610268431 813777252270274631415402647)
              ·
                refine ⟨1220665878405411947123103971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813777252270274631415402647 1220665878405411947123103971)
                ·
                  refine ⟨1830998817608117920684655957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220665878405411947123103971 1830998817608117920684655957)
                  ·
                    refine ⟨1341063587115320742688957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1830998817608117920684655957 1341063587115320742688957)
                    ·
                      rfl

theorem cell23_7835136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_7835136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835136 prefixEnd_7835136 := by exact prefixLift 7835136
  have htrace : WordTrace (prefixWord ++ tailWord_7835136) baseStart_7835136 baseEnd_7835136 := by
    simpa [prefixWord, tailWord_7835136, baseEnd_7835136] using wordTrace_append hprefix tailTrace_7835136
  have hstable : (prefixWord ++ tailWord_7835136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835136).length < 2 ^ (prefixWord ++ tailWord_7835136).sum := by decide
  have hdescent : baseEnd_7835136 < baseStart_7835136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835170 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_7835170 : Nat := 118140960795 + 7835170 * 2 ^ 59
def prefixEnd_7835170 : Nat := 4983230072969 + 3 ^ 40 * 7835170 * 2
def baseEnd_7835170 : Nat := 1341069406562738365013905

theorem tailTrace_7835170 : CollatzResearch.WordTrace tailWord_7835170 prefixEnd_7835170 1341069406562738365013905 := by
  unfold tailWord_7835170
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443031756131176336575741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190514751349683136897535309 71443031756131176336575741)
  ·
    refine ⟨26791136908549191126215903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71443031756131176336575741 26791136908549191126215903)
    ·
      refine ⟨40186705362823786689323855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791136908549191126215903 40186705362823786689323855)
      ·
        refine ⟨60280058044235680033985783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40186705362823786689323855 60280058044235680033985783)
        ·
          refine ⟨90420087066353520050978675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60280058044235680033985783 90420087066353520050978675)
          ·
            refine ⟨135630130599530280076468013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90420087066353520050978675 135630130599530280076468013)
            ·
              refine ⟨50861298974823855028675505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135630130599530280076468013 50861298974823855028675505)
              ·
                refine ⟨38145974231117891271506629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50861298974823855028675505 38145974231117891271506629)
                ·
                  refine ⟨7152370168334604613407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38145974231117891271506629 7152370168334604613407493)
                  ·
                    refine ⟨1341069406562738365013905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152370168334604613407493 1341069406562738365013905)
                    ·
                      rfl

theorem cell23_7835170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_7835170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835170 prefixEnd_7835170 := by exact prefixLift 7835170
  have htrace : WordTrace (prefixWord ++ tailWord_7835170) baseStart_7835170 baseEnd_7835170 := by
    simpa [prefixWord, tailWord_7835170, baseEnd_7835170] using wordTrace_append hprefix tailTrace_7835170
  have hstable : (prefixWord ++ tailWord_7835170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835170).length < 2 ^ (prefixWord ++ tailWord_7835170).sum := by decide
  have hdescent : baseEnd_7835170 < baseStart_7835170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835171 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 1, 1, 3]
def baseStart_7835171 : Nat := 118140960795 + 7835171 * 2 ^ 59
def prefixEnd_7835171 : Nat := 4983230072969 + 3 ^ 40 * 7835171 * 2
def baseEnd_7835171 : Nat := 4023208733168869591129211

theorem tailTrace_7835171 : CollatzResearch.WordTrace tailWord_7835171 prefixEnd_7835171 4023208733168869591129211 := by
  unfold tailWord_7835171
  simp only [CollatzResearch.WordTrace]
  refine ⟨285772163497521082517089367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190514775665014055011392911 285772163497521082517089367)
  ·
    refine ⟨428658245246281623775634051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285772163497521082517089367 428658245246281623775634051)
    ·
      refine ⟨642987367869422435663451077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428658245246281623775634051 642987367869422435663451077)
      ·
        refine ⟨120560131475516706686897077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 642987367869422435663451077 120560131475516706686897077)
        ·
          refine ⟨11302512325829691251896601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120560131475516706686897077 11302512325829691251896601)
          ·
            refine ⟨8476884244372268438922451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11302512325829691251896601 8476884244372268438922451)
            ·
              refine ⟨12715326366558402658383677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476884244372268438922451 12715326366558402658383677)
              ·
                refine ⟨4768247387459400996893879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12715326366558402658383677 4768247387459400996893879)
                ·
                  refine ⟨7152371081189101495340819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768247387459400996893879 7152371081189101495340819)
                  ·
                    refine ⟨10728556621783652243011229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152371081189101495340819 10728556621783652243011229)
                    ·
                      refine ⟨4023208733168869591129211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10728556621783652243011229 4023208733168869591129211)
                      ·
                        rfl

theorem cell23_7835171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_7835171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835171 prefixEnd_7835171 := by exact prefixLift 7835171
  have htrace : WordTrace (prefixWord ++ tailWord_7835171) baseStart_7835171 baseEnd_7835171 := by
    simpa [prefixWord, tailWord_7835171, baseEnd_7835171] using wordTrace_append hprefix tailTrace_7835171
  have hstable : (prefixWord ++ tailWord_7835171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835171).length < 2 ^ (prefixWord ++ tailWord_7835171).sum := by decide
  have hdescent : baseEnd_7835171 < baseStart_7835171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835173 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_7835173 : Nat := 118140960795 + 7835173 * 2 ^ 59
def prefixEnd_7835173 : Nat := 4983230072969 + 3 ^ 40 * 7835173 * 2
def baseEnd_7835173 : Nat := 4023209760130178583304201

theorem tailTrace_7835173 : CollatzResearch.WordTrace tailWord_7835173 prefixEnd_7835173 4023209760130178583304201 := by
  unfold tailWord_7835173
  simp only [CollatzResearch.WordTrace]
  refine ⟨285772236443513836858662173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190514824295675891239108115 285772236443513836858662173)
  ·
    refine ⟨107164588666317688821998315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285772236443513836858662173 107164588666317688821998315)
    ·
      refine ⟨160746882999476533232997473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107164588666317688821998315 160746882999476533232997473)
      ·
        refine ⟨120560162249607399924748105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160746882999476533232997473 120560162249607399924748105)
        ·
          refine ⟨90420121687205549943561079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120560162249607399924748105 90420121687205549943561079)
          ·
            refine ⟨135630182530808324915341619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90420121687205549943561079 135630182530808324915341619)
            ·
              refine ⟨203445273796212487373012429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135630182530808324915341619 203445273796212487373012429)
              ·
                refine ⟨76291977673579682764879661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203445273796212487373012429 76291977673579682764879661)
                ·
                  refine ⟨28609491627592381036829873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76291977673579682764879661 28609491627592381036829873)
                  ·
                    refine ⟨21457118720694285777622405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28609491627592381036829873 21457118720694285777622405)
                    ·
                      refine ⟨4023209760130178583304201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21457118720694285777622405 4023209760130178583304201)
                      ·
                        rfl

theorem cell23_7835173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_7835173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835173 prefixEnd_7835173 := by exact prefixLift 7835173
  have htrace : WordTrace (prefixWord ++ tailWord_7835173) baseStart_7835173 baseEnd_7835173 := by
    simpa [prefixWord, tailWord_7835173, baseEnd_7835173] using wordTrace_append hprefix tailTrace_7835173
  have hstable : (prefixWord ++ tailWord_7835173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835173).length < 2 ^ (prefixWord ++ tailWord_7835173).sum := by decide
  have hdescent : baseEnd_7835173 < baseStart_7835173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835210 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_7835210 : Nat := 118140960795 + 7835210 * 2 ^ 59
def prefixEnd_7835210 : Nat := 4983230072969 + 3 ^ 40 * 7835210 * 2
def baseEnd_7835210 : Nat := 4023228758914394938541531

theorem tailTrace_7835210 : CollatzResearch.WordTrace tailWord_7835210 prefixEnd_7835210 4023228758914394938541531 := by
  unfold tailWord_7835210
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443396486094948044439771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190515723962919861451839389 71443396486094948044439771)
  ·
    refine ⟨107165094729142422066659657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71443396486094948044439771 107165094729142422066659657)
    ·
      refine ⟨80373821046856816549994743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107165094729142422066659657 80373821046856816549994743)
      ·
        refine ⟨120560731570285224824992115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80373821046856816549994743 120560731570285224824992115)
        ·
          refine ⟨180841097355427837237488173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120560731570285224824992115 180841097355427837237488173)
          ·
            refine ⟨67815411508285438964058065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180841097355427837237488173 67815411508285438964058065)
            ·
              refine ⟨50861558631214079223043549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67815411508285438964058065 50861558631214079223043549)
              ·
                refine ⟨19073084486705279708641331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50861558631214079223043549 19073084486705279708641331)
                ·
                  refine ⟨28609626730057919562961997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19073084486705279708641331 28609626730057919562961997)
                  ·
                    refine ⟨10728610023771719836110749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28609626730057919562961997 10728610023771719836110749)
                    ·
                      refine ⟨4023228758914394938541531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10728610023771719836110749 4023228758914394938541531)
                      ·
                        rfl

theorem cell23_7835210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_7835210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835210 prefixEnd_7835210 := by exact prefixLift 7835210
  have htrace : WordTrace (prefixWord ++ tailWord_7835210) baseStart_7835210 baseEnd_7835210 := by
    simpa [prefixWord, tailWord_7835210, baseEnd_7835210] using wordTrace_append hprefix tailTrace_7835210
  have hstable : (prefixWord ++ tailWord_7835210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835210).length < 2 ^ (prefixWord ++ tailWord_7835210).sum := by decide
  have hdescent : baseEnd_7835210 < baseStart_7835210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835245 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_7835245 : Nat := 118140960795 + 7835245 * 2 ^ 59
def prefixEnd_7835245 : Nat := 4983230072969 + 3 ^ 40 * 7835245 * 2
def baseEnd_7835245 : Nat := 4023246730737302301603871

theorem tailTrace_7835245 : CollatzResearch.WordTrace tailWord_7835245 prefixEnd_7835245 4023246730737302301603871 := by
  unfold tailWord_7835245
  simp only [CollatzResearch.WordTrace]
  refine ⟨285774862499252993155283189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190516574999501995436855459 285774862499252993155283189)
  ·
    refine ⟨26791393359304968108307799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285774862499252993155283189 26791393359304968108307799)
    ·
      refine ⟨40187090038957452162461699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791393359304968108307799 40187090038957452162461699)
      ·
        refine ⟨60280635058436178243692549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40187090038957452162461699 60280635058436178243692549)
        ·
          refine ⟨11302619073456783420692353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60280635058436178243692549 11302619073456783420692353)
          ·
            refine ⟨8476964305092587565519265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11302619073456783420692353 8476964305092587565519265)
            ·
              refine ⟨6357723228819440674139449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476964305092587565519265 6357723228819440674139449)
              ·
                refine ⟨4768292421614580505604587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357723228819440674139449 4768292421614580505604587)
                ·
                  refine ⟨7152438632421870758406881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768292421614580505604587 7152438632421870758406881)
                  ·
                    refine ⟨5364328974316403068805161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152438632421870758406881 5364328974316403068805161)
                    ·
                      refine ⟨4023246730737302301603871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364328974316403068805161 4023246730737302301603871)
                      ·
                        rfl

theorem cell23_7835245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_7835245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835245 prefixEnd_7835245 := by exact prefixLift 7835245
  have htrace : WordTrace (prefixWord ++ tailWord_7835245) baseStart_7835245 baseEnd_7835245 := by
    simpa [prefixWord, tailWord_7835245, baseEnd_7835245] using wordTrace_append hprefix tailTrace_7835245
  have hstable : (prefixWord ++ tailWord_7835245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835245).length < 2 ^ (prefixWord ++ tailWord_7835245).sum := by decide
  have hdescent : baseEnd_7835245 < baseStart_7835245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835250 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7835250 : Nat := 118140960795 + 7835250 * 2 ^ 59
def prefixEnd_7835250 : Nat := 4983230072969 + 3 ^ 40 * 7835250 * 2
def baseEnd_7835250 : Nat := 4023249298140574782041347

theorem tailTrace_7835250 : CollatzResearch.WordTrace tailWord_7835250 prefixEnd_7835250 4023249298140574782041347 := by
  unfold tailWord_7835250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443761216058719752303801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190516696576156586006143469 71443761216058719752303801)
  ·
    refine ⟨53582820912044039814227851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71443761216058719752303801 53582820912044039814227851)
    ·
      refine ⟨80374231368066059721341777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53582820912044039814227851 80374231368066059721341777)
      ·
        refine ⟨60280673526049544791006333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80374231368066059721341777 60280673526049544791006333)
        ·
          refine ⟨22605252572268579296627375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60280673526049544791006333 22605252572268579296627375)
          ·
            refine ⟨33907878858402868944941063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605252572268579296627375 33907878858402868944941063)
            ·
              refine ⟨50861818287604303417411595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33907878858402868944941063 50861818287604303417411595)
              ·
                refine ⟨76292727431406455126117393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50861818287604303417411595 76292727431406455126117393)
                ·
                  refine ⟨57219545573554841344588045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76292727431406455126117393 57219545573554841344588045)
                  ·
                    refine ⟨21457329590083065504220517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57219545573554841344588045 21457329590083065504220517)
                    ·
                      refine ⟨4023249298140574782041347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21457329590083065504220517 4023249298140574782041347)
                      ·
                        rfl

theorem cell23_7835250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7835250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835250 prefixEnd_7835250 := by exact prefixLift 7835250
  have htrace : WordTrace (prefixWord ++ tailWord_7835250) baseStart_7835250 baseEnd_7835250 := by
    simpa [prefixWord, tailWord_7835250, baseEnd_7835250] using wordTrace_append hprefix tailTrace_7835250
  have hstable : (prefixWord ++ tailWord_7835250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835250).length < 2 ^ (prefixWord ++ tailWord_7835250).sum := by decide
  have hdescent : baseEnd_7835250 < baseStart_7835250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835254 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7835254 : Nat := 118140960795 + 7835254 * 2 ^ 59
def prefixEnd_7835254 : Nat := 4983230072969 + 3 ^ 40 * 7835254 * 2
def baseEnd_7835254 : Nat := 4023251352063192766391329

theorem tailTrace_7835254 : CollatzResearch.WordTrace tailWord_7835254 prefixEnd_7835254 4023251352063192766391329 := by
  unfold tailWord_7835254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860949422263774230772551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190516793837480258461573877 17860949422263774230772551)
  ·
    refine ⟨26791424133395661346158827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860949422263774230772551 26791424133395661346158827)
    ·
      refine ⟨40187136200093492019238241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791424133395661346158827 40187136200093492019238241)
      ·
        refine ⟨30140352150070119014428681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40187136200093492019238241 30140352150070119014428681)
        ·
          refine ⟨22605264112552589260821511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30140352150070119014428681 22605264112552589260821511)
          ·
            refine ⟨33907896168828883891232267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605264112552589260821511 33907896168828883891232267)
            ·
              refine ⟨50861844253243325836848401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33907896168828883891232267 50861844253243325836848401)
              ·
                refine ⟨38146383189932494377636301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50861844253243325836848401 38146383189932494377636301)
                ·
                  refine ⟨14304893696224685391613613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38146383189932494377636301 14304893696224685391613613)
                  ·
                    refine ⟨5364335136084257021855105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14304893696224685391613613 5364335136084257021855105)
                    ·
                      refine ⟨4023251352063192766391329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364335136084257021855105 4023251352063192766391329)
                      ·
                        rfl

theorem cell23_7835254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7835254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835254 prefixEnd_7835254 := by exact prefixLift 7835254
  have htrace : WordTrace (prefixWord ++ tailWord_7835254) baseStart_7835254 baseEnd_7835254 := by
    simpa [prefixWord, tailWord_7835254, baseEnd_7835254] using wordTrace_append hprefix tailTrace_7835254
  have hstable : (prefixWord ++ tailWord_7835254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835254).length < 2 ^ (prefixWord ++ tailWord_7835254).sum := by decide
  have hdescent : baseEnd_7835254 < baseStart_7835254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835267 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 6, 2, 2]
def baseStart_7835267 : Nat := 118140960795 + 7835267 * 2 ^ 59
def prefixEnd_7835267 : Nat := 4983230072969 + 3 ^ 40 * 7835267 * 2
def baseEnd_7835267 : Nat := 4023258027311701215528769

theorem tailTrace_7835267 : CollatzResearch.WordTrace tailWord_7835267 prefixEnd_7835267 4023258027311701215528769 := by
  unfold tailWord_7835267
  simp only [CollatzResearch.WordTrace]
  refine ⟨285775664905173290912584055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190517109936782193941722703 285775664905173290912584055)
  ·
    refine ⟨428663497357759936368876083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285775664905173290912584055 428663497357759936368876083)
    ·
      refine ⟨642995246036639904553314125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428663497357759936368876083 642995246036639904553314125)
      ·
        refine ⟨241123217263739964207492797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642995246036639904553314125 241123217263739964207492797)
        ·
          refine ⟨90421206473902486577809799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241123217263739964207492797 90421206473902486577809799)
          ·
            refine ⟨135631809710853729866714699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90421206473902486577809799 135631809710853729866714699)
            ·
              refine ⟨203447714566280594800072049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135631809710853729866714699 203447714566280594800072049)
              ·
                refine ⟨152585785924710446100054037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203447714566280594800072049 152585785924710446100054037)
                ·
                  refine ⟨7152458715220802160940033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152585785924710446100054037 7152458715220802160940033)
                  ·
                    refine ⟨5364344036415601620705025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152458715220802160940033 5364344036415601620705025)
                    ·
                      refine ⟨4023258027311701215528769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364344036415601620705025 4023258027311701215528769)
                      ·
                        rfl

theorem cell23_7835267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_7835267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835267 prefixEnd_7835267 := by exact prefixLift 7835267
  have htrace : WordTrace (prefixWord ++ tailWord_7835267) baseStart_7835267 baseEnd_7835267 := by
    simpa [prefixWord, tailWord_7835267, baseEnd_7835267] using wordTrace_append hprefix tailTrace_7835267
  have hstable : (prefixWord ++ tailWord_7835267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835267).length < 2 ^ (prefixWord ++ tailWord_7835267).sum := by decide
  have hdescent : baseEnd_7835267 < baseStart_7835267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835273 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 9]
def baseStart_7835273 : Nat := 118140960795 + 7835273 * 2 ^ 59
def prefixEnd_7835273 : Nat := 4983230072969 + 3 ^ 40 * 7835273 * 2
def baseEnd_7835273 : Nat := 447029012021736465783749

theorem tailTrace_7835273 : CollatzResearch.WordTrace tailWord_7835273 prefixEnd_7835273 447029012021736465783749 := by
  unfold tailWord_7835273
  simp only [CollatzResearch.WordTrace]
  refine ⟨285775883743151553937302473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190517255828767702624868315 285775883743151553937302473)
  ·
    refine ⟨214331912807363665452976855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285775883743151553937302473 214331912807363665452976855)
    ·
      refine ⟨321497869211045498179465283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214331912807363665452976855 321497869211045498179465283)
      ·
        refine ⟨482246803816568247269197925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321497869211045498179465283 482246803816568247269197925)
        ·
          refine ⟨90421275715606546362974611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482246803816568247269197925 90421275715606546362974611)
          ·
            refine ⟨135631913573409819544461917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90421275715606546362974611 135631913573409819544461917)
            ·
              refine ⟨50861967590028682329173219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135631913573409819544461917 50861967590028682329173219)
              ·
                refine ⟨76292951385043023493759829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50861967590028682329173219 76292951385043023493759829)
                ·
                  refine ⟨447029012021736465783749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76292951385043023493759829 447029012021736465783749)
                  ·
                    rfl

theorem cell23_7835273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_7835273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835273 prefixEnd_7835273 := by exact prefixLift 7835273
  have htrace : WordTrace (prefixWord ++ tailWord_7835273) baseStart_7835273 baseEnd_7835273 := by
    simpa [prefixWord, tailWord_7835273, baseEnd_7835273] using wordTrace_append hprefix tailTrace_7835273
  have hstable : (prefixWord ++ tailWord_7835273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835273).length < 2 ^ (prefixWord ++ tailWord_7835273).sum := by decide
  have hdescent : baseEnd_7835273 < baseStart_7835273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835318 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7835318 : Nat := 118140960795 + 7835318 * 2 ^ 59
def prefixEnd_7835318 : Nat := 4983230072969 + 3 ^ 40 * 7835318 * 2
def baseEnd_7835318 : Nat := 4023284214825080515991035

theorem tailTrace_7835318 : CollatzResearch.WordTrace tailWord_7835318 prefixEnd_7835318 4023284214825080515991035 := by
  unfold tailWord_7835318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861095314249282913918163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190518350018659017748460405 17861095314249282913918163)
  ·
    refine ⟨26791642971373924370877245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17861095314249282913918163 26791642971373924370877245)
    ·
      refine ⟨10046866114265221639078967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26791642971373924370877245 10046866114265221639078967)
      ·
        refine ⟨15070299171397832458618451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046866114265221639078967 15070299171397832458618451)
        ·
          refine ⟨22605448757096748687927677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070299171397832458618451 22605448757096748687927677)
          ·
            refine ⟨8477043283911280757972879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22605448757096748687927677 8477043283911280757972879)
            ·
              refine ⟨12715564925866921136959319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477043283911280757972879 12715564925866921136959319)
              ·
                refine ⟨19073347388800381705438979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715564925866921136959319 19073347388800381705438979)
                ·
                  refine ⟨28610021083200572558158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19073347388800381705438979 28610021083200572558158469)
                  ·
                    refine ⟨5364378953100107354654713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28610021083200572558158469 5364378953100107354654713)
                    ·
                      refine ⟨4023284214825080515991035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364378953100107354654713 4023284214825080515991035)
                      ·
                        rfl

theorem cell23_7835318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7835318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835318 prefixEnd_7835318 := by exact prefixLift 7835318
  have htrace : WordTrace (prefixWord ++ tailWord_7835318) baseStart_7835318 baseEnd_7835318 := by
    simpa [prefixWord, tailWord_7835318, baseEnd_7835318] using wordTrace_append hprefix tailTrace_7835318
  have hstable : (prefixWord ++ tailWord_7835318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835318).length < 2 ^ (prefixWord ++ tailWord_7835318).sum := by decide
  have hdescent : baseEnd_7835318 < baseStart_7835318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835341 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7835341 : Nat := 118140960795 + 7835341 * 2 ^ 59
def prefixEnd_7835341 : Nat := 4983230072969 + 3 ^ 40 * 7835341 * 2
def baseEnd_7835341 : Nat := 447032891653348214000381

theorem tailTrace_7835341 : CollatzResearch.WordTrace tailWord_7835341 prefixEnd_7835341 447032891653348214000381 := by
  unfold tailWord_7835341
  simp only [CollatzResearch.WordTrace]
  refine ⟨285778363906905201550777877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190518909271270134367185251 285778363906905201550777877)
  ·
    refine ⟨13395860808136181322692713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285778363906905201550777877 13395860808136181322692713)
    ·
      refine ⟨10046895606102135992019535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13395860808136181322692713 10046895606102135992019535)
      ·
        refine ⟨15070343409153203988029303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10046895606102135992019535 15070343409153203988029303)
        ·
          refine ⟨22605515113729805982043955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070343409153203988029303 22605515113729805982043955)
          ·
            refine ⟨33908272670594708973065933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605515113729805982043955 33908272670594708973065933)
            ·
              refine ⟨12715602251473015864899725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33908272670594708973065933 12715602251473015864899725)
              ·
                refine ⟨4768350844302380949337397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12715602251473015864899725 4768350844302380949337397)
                ·
                  refine ⟨447032891653348214000381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768350844302380949337397 447032891653348214000381)
                  ·
                    rfl

theorem cell23_7835341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7835341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835341 prefixEnd_7835341 := by exact prefixLift 7835341
  have htrace : WordTrace (prefixWord ++ tailWord_7835341) baseStart_7835341 baseEnd_7835341 := by
    simpa [prefixWord, tailWord_7835341, baseEnd_7835341] using wordTrace_append hprefix tailTrace_7835341
  have hstable : (prefixWord ++ tailWord_7835341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835341).length < 2 ^ (prefixWord ++ tailWord_7835341).sum := by decide
  have hdescent : baseEnd_7835341 < baseStart_7835341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835370 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7835370 : Nat := 118140960795 + 7835370 * 2 ^ 59
def prefixEnd_7835370 : Nat := 4983230072969 + 3 ^ 40 * 7835370 * 2
def baseEnd_7835370 : Nat := 4023310915819114312540795

theorem tailTrace_7835370 : CollatzResearch.WordTrace tailWord_7835370 prefixEnd_7835370 4023310915819114312540795 := by
  unfold tailWord_7835370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71444855405950034875895891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190519614415866759669055709 71444855405950034875895891)
  ·
    refine ⟨107167283108925052313843837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71444855405950034875895891 107167283108925052313843837)
    ·
      refine ⟨40187731165846894617691439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107167283108925052313843837 40187731165846894617691439)
      ·
        refine ⟨60281596748770341926537159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40187731165846894617691439 60281596748770341926537159)
        ·
          refine ⟨90422395123155512889805739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60281596748770341926537159 90422395123155512889805739)
          ·
            refine ⟨135633592684733269334708609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90422395123155512889805739 135633592684733269334708609)
            ·
              refine ⟨101725194513549952001031457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135633592684733269334708609 101725194513549952001031457)
              ·
                refine ⟨76293895885162464000773593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101725194513549952001031457 76293895885162464000773593)
                ·
                  refine ⟨57220421913871848000580195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76293895885162464000773593 57220421913871848000580195)
                  ·
                    refine ⟨85830632870807772000870293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57220421913871848000580195 85830632870807772000870293)
                    ·
                      refine ⟨4023310915819114312540795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85830632870807772000870293 4023310915819114312540795)
                      ·
                        rfl

theorem cell23_7835370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7835370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835370 prefixEnd_7835370 := by exact prefixLift 7835370
  have htrace : WordTrace (prefixWord ++ tailWord_7835370) baseStart_7835370 baseEnd_7835370 := by
    simpa [prefixWord, tailWord_7835370, baseEnd_7835370] using wordTrace_append hprefix tailTrace_7835370
  have hstable : (prefixWord ++ tailWord_7835370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835370).length < 2 ^ (prefixWord ++ tailWord_7835370).sum := by decide
  have hdescent : baseEnd_7835370 < baseStart_7835370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835407 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 3]
def baseStart_7835407 : Nat := 118140960795 + 7835407 * 2 ^ 59
def prefixEnd_7835407 : Nat := 4983230072969 + 3 ^ 40 * 7835407 * 2
def baseEnd_7835407 : Nat := 4023329914603330667778125

theorem tailTrace_7835407 : CollatzResearch.WordTrace tailWord_7835407 prefixEnd_7835407 4023329914603330667778125 := by
  unfold tailWord_7835407
  simp only [CollatzResearch.WordTrace]
  refine ⟨285780771124666094822680475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190520514083110729881786983 285780771124666094822680475)
  ·
    refine ⟨428671156686999142234020713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285780771124666094822680475 428671156686999142234020713)
    ·
      refine ⟨321503367515249356675515535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428671156686999142234020713 321503367515249356675515535)
      ·
        refine ⟨482255051272874035013273303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321503367515249356675515535 482255051272874035013273303)
        ·
          refine ⟨723382576909311052519909955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482255051272874035013273303 723382576909311052519909955)
          ·
            refine ⟨1085073865363966578779864933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723382576909311052519909955 1085073865363966578779864933)
            ·
              refine ⟨203451349755743733521224675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1085073865363966578779864933 203451349755743733521224675)
              ·
                refine ⟨305177024633615600281837013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203451349755743733521224675 305177024633615600281837013)
                ·
                  refine ⟨7152586514850365631605555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305177024633615600281837013 7152586514850365631605555)
                  ·
                    refine ⟨10728879772275548447408333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152586514850365631605555 10728879772275548447408333)
                    ·
                      refine ⟨4023329914603330667778125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10728879772275548447408333 4023329914603330667778125)
                      ·
                        rfl

theorem cell23_7835407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_7835407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835407 prefixEnd_7835407 := by exact prefixLift 7835407
  have htrace : WordTrace (prefixWord ++ tailWord_7835407) baseStart_7835407 baseEnd_7835407 := by
    simpa [prefixWord, tailWord_7835407, baseEnd_7835407] using wordTrace_append hprefix tailTrace_7835407
  have hstable : (prefixWord ++ tailWord_7835407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835407).length < 2 ^ (prefixWord ++ tailWord_7835407).sum := by decide
  have hdescent : baseEnd_7835407 < baseStart_7835407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835418 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_7835418 : Nat := 118140960795 + 7835418 * 2 ^ 59
def prefixEnd_7835418 : Nat := 4983230072969 + 3 ^ 40 * 7835418 * 2
def baseEnd_7835418 : Nat := 1341111854296843374913525

theorem tailTrace_7835418 : CollatzResearch.WordTrace tailWord_7835418 prefixEnd_7835418 1341111854296843374913525 := by
  unfold tailWord_7835418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71445293081906560925332727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190520781551750829134220605 71445293081906560925332727)
  ·
    refine ⟨107167939622859841387999091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71445293081906560925332727 107167939622859841387999091)
    ·
      refine ⟨160751909434289762081998637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107167939622859841387999091 160751909434289762081998637)
      ·
        refine ⟨60281966037858660780749489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160751909434289762081998637 60281966037858660780749489)
        ·
          refine ⟨45211474528393995585562117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60281966037858660780749489 45211474528393995585562117)
          ·
            refine ⟨8477151474073874172292897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45211474528393995585562117 8477151474073874172292897)
            ·
              refine ⟨6357863605555405629219673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477151474073874172292897 6357863605555405629219673)
              ·
                refine ⟨4768397704166554221914755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357863605555405629219673 4768397704166554221914755)
                ·
                  refine ⟨7152596556249831332872133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768397704166554221914755 7152596556249831332872133)
                  ·
                    refine ⟨1341111854296843374913525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152596556249831332872133 1341111854296843374913525)
                    ·
                      rfl

theorem cell23_7835418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_7835418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835418 prefixEnd_7835418 := by exact prefixLift 7835418
  have htrace : WordTrace (prefixWord ++ tailWord_7835418) baseStart_7835418 baseEnd_7835418 := by
    simpa [prefixWord, tailWord_7835418, baseEnd_7835418] using wordTrace_append hprefix tailTrace_7835418
  have hstable : (prefixWord ++ tailWord_7835418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835418).length < 2 ^ (prefixWord ++ tailWord_7835418).sum := by decide
  have hdescent : baseEnd_7835418 < baseStart_7835418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835424 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7835424 : Nat := 118140960795 + 7835424 * 2 ^ 59
def prefixEnd_7835424 : Nat := 4983230072969 + 3 ^ 40 * 7835424 * 2
def baseEnd_7835424 : Nat := 4023338643774457101265547

theorem tailTrace_7835424 : CollatzResearch.WordTrace tailWord_7835424 prefixEnd_7835424 4023338643774457101265547 := by
  unfold tailWord_7835424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142890695582802253363024663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190520927443736337817366217 142890695582802253363024663)
  ·
    refine ⟨214336043374203380044536995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142890695582802253363024663 214336043374203380044536995)
    ·
      refine ⟨321504065061305070066805493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214336043374203380044536995 321504065061305070066805493)
      ·
        refine ⟨30141006099497350318763015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321504065061305070066805493 30141006099497350318763015)
        ·
          refine ⟨45211509149246025478144523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30141006099497350318763015 45211509149246025478144523)
          ·
            refine ⟨67817263723869038217216785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45211509149246025478144523 67817263723869038217216785)
            ·
              refine ⟨50862947792901778662912589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67817263723869038217216785 50862947792901778662912589)
              ·
                refine ⟨19073605422338166998592221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50862947792901778662912589 19073605422338166998592221)
                ·
                  refine ⟨7152602033376812624472083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19073605422338166998592221 7152602033376812624472083)
                  ·
                    refine ⟨10728903050065218936708125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152602033376812624472083 10728903050065218936708125)
                    ·
                      refine ⟨4023338643774457101265547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10728903050065218936708125 4023338643774457101265547)
                      ·
                        rfl

theorem cell23_7835424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7835424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835424 prefixEnd_7835424 := by exact prefixLift 7835424
  have htrace : WordTrace (prefixWord ++ tailWord_7835424) baseStart_7835424 baseEnd_7835424 := by
    simpa [prefixWord, tailWord_7835424, baseEnd_7835424] using wordTrace_append hprefix tailTrace_7835424
  have hstable : (prefixWord ++ tailWord_7835424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835424).length < 2 ^ (prefixWord ++ tailWord_7835424).sum := by decide
  have hdescent : baseEnd_7835424 < baseStart_7835424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835444 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_7835444 : Nat := 118140960795 + 7835444 * 2 ^ 59
def prefixEnd_7835444 : Nat := 4983230072969 + 3 ^ 40 * 7835444 * 2
def baseEnd_7835444 : Nat := 1341116304462515674338485

theorem tailTrace_7835444 : CollatzResearch.WordTrace tailWord_7835444 prefixEnd_7835444 1341116304462515674338485 := by
  unfold tailWord_7835444
  simp only [CollatzResearch.WordTrace]
  refine ⟨142891060312766025070888693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190521413750354700094518257 142891060312766025070888693)
  ·
    refine ⟨13396036904321814850395815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142891060312766025070888693 13396036904321814850395815)
    ·
      refine ⟨20094055356482722275593723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13396036904321814850395815 20094055356482722275593723)
      ·
        refine ⟨30141083034724083413390585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20094055356482722275593723 30141083034724083413390585)
        ·
          refine ⟨22605812276043062560042939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30141083034724083413390585 22605812276043062560042939)
          ·
            refine ⟨33908718414064593840064409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605812276043062560042939 33908718414064593840064409)
            ·
              refine ⟨25431538810548445380048307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33908718414064593840064409 25431538810548445380048307)
              ·
                refine ⟨38147308215822668070072461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25431538810548445380048307 38147308215822668070072461)
                ·
                  refine ⟨14305240580933500526277173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38147308215822668070072461 14305240580933500526277173)
                  ·
                    refine ⟨1341116304462515674338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14305240580933500526277173 1341116304462515674338485)
                    ·
                      rfl

theorem cell23_7835444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_7835444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835444 prefixEnd_7835444 := by exact prefixLift 7835444
  have htrace : WordTrace (prefixWord ++ tailWord_7835444) baseStart_7835444 baseEnd_7835444 := by
    simpa [prefixWord, tailWord_7835444, baseEnd_7835444] using wordTrace_append hprefix tailTrace_7835444
  have hstable : (prefixWord ++ tailWord_7835444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835444).length < 2 ^ (prefixWord ++ tailWord_7835444).sum := by decide
  have hdescent : baseEnd_7835444 < baseStart_7835444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835447 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 8, 2]
def baseStart_7835447 : Nat := 118140960795 + 7835447 * 2 ^ 59
def prefixEnd_7835447 : Nat := 4983230072969 + 3 ^ 40 * 7835447 * 2
def baseEnd_7835447 : Nat := 4023350453829510511277941

theorem tailTrace_7835447 : CollatzResearch.WordTrace tailWord_7835447 prefixEnd_7835447 4023350453829510511277941 := by
  unfold tailWord_7835447
  simp only [CollatzResearch.WordTrace]
  refine ⟨285782230044521181654136595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190521486696347454436091063 285782230044521181654136595)
  ·
    refine ⟨428673345066781772481204893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285782230044521181654136595 428673345066781772481204893)
    ·
      refine ⟨160752504400043164680451835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428673345066781772481204893 160752504400043164680451835)
      ·
        refine ⟨241128756600064747020677753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160752504400043164680451835 241128756600064747020677753)
        ·
          refine ⟨180846567450048560265508315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241128756600064747020677753 180846567450048560265508315)
          ·
            refine ⟨271269851175072840398262473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180846567450048560265508315 271269851175072840398262473)
            ·
              refine ⟨203452388381304630298696855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271269851175072840398262473 203452388381304630298696855)
              ·
                refine ⟨305178582571956945448045283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203452388381304630298696855 305178582571956945448045283)
                ·
                  refine ⟨457767873857935418172067925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305178582571956945448045283 457767873857935418172067925)
                  ·
                    refine ⟨5364467271772680681703921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 457767873857935418172067925 5364467271772680681703921)
                    ·
                      refine ⟨4023350453829510511277941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364467271772680681703921 4023350453829510511277941)
                      ·
                        rfl

theorem cell23_7835447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_7835447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835447 prefixEnd_7835447 := by exact prefixLift 7835447
  have htrace : WordTrace (prefixWord ++ tailWord_7835447) baseStart_7835447 baseEnd_7835447 := by
    simpa [prefixWord, tailWord_7835447, baseEnd_7835447] using wordTrace_append hprefix tailTrace_7835447
  have hstable : (prefixWord ++ tailWord_7835447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835447).length < 2 ^ (prefixWord ++ tailWord_7835447).sum := by decide
  have hdescent : baseEnd_7835447 < baseStart_7835447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835464 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_7835464 : Nat := 118140960795 + 7835464 * 2 ^ 59
def prefixEnd_7835464 : Nat := 4983230072969 + 3 ^ 40 * 7835464 * 2
def baseEnd_7835464 : Nat := 4023359183000636944765363

theorem tailTrace_7835464 : CollatzResearch.WordTrace tailWord_7835464 prefixEnd_7835464 4023359183000636944765363 := by
  unfold tailWord_7835464
  simp only [CollatzResearch.WordTrace]
  refine ⟨142891425042729796778752723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190521900056973062371670297 142891425042729796778752723)
  ·
    refine ⟨214337137564094695168129085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142891425042729796778752723 214337137564094695168129085)
    ·
      refine ⟨80376426586535510688048407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214337137564094695168129085 80376426586535510688048407)
      ·
        refine ⟨120564639879803266032072611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80376426586535510688048407 120564639879803266032072611)
        ·
          refine ⟨180846959819704899048108917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120564639879803266032072611 180846959819704899048108917)
          ·
            refine ⟨16954402483097334285760211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180846959819704899048108917 16954402483097334285760211)
            ·
              refine ⟨25431603724646001428640317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16954402483097334285760211 25431603724646001428640317)
              ·
                refine ⟨9536851396742250535740119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25431603724646001428640317 9536851396742250535740119)
                ·
                  refine ⟨14305277095113375803610179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9536851396742250535740119 14305277095113375803610179)
                  ·
                    refine ⟨21457915642670063705415269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14305277095113375803610179 21457915642670063705415269)
                    ·
                      refine ⟨4023359183000636944765363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21457915642670063705415269 4023359183000636944765363)
                      ·
                        rfl

theorem cell23_7835464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_7835464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835464 prefixEnd_7835464 := by exact prefixLift 7835464
  have htrace : WordTrace (prefixWord ++ tailWord_7835464) baseStart_7835464 baseEnd_7835464 := by
    simpa [prefixWord, tailWord_7835464, baseEnd_7835464] using wordTrace_append hprefix tailTrace_7835464
  have hstable : (prefixWord ++ tailWord_7835464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835464).length < 2 ^ (prefixWord ++ tailWord_7835464).sum := by decide
  have hdescent : baseEnd_7835464 < baseStart_7835464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835474 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_7835474 : Nat := 118140960795 + 7835474 * 2 ^ 59
def prefixEnd_7835474 : Nat := 4983230072969 + 3 ^ 40 * 7835474 * 2
def baseEnd_7835474 : Nat := 1341121439269060635213439

theorem tailTrace_7835474 : CollatzResearch.WordTrace tailWord_7835474 prefixEnd_7835474 1341121439269060635213439 := by
  unfold tailWord_7835474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71445803703855841316342369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190522143210282243510246317 71445803703855841316342369)
  ·
    refine ⟨53584352777891880987256777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71445803703855841316342369 53584352777891880987256777)
    ·
      refine ⟨40188264583418910740442583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53584352777891880987256777 40188264583418910740442583)
      ·
        refine ⟨60282396875128366110663875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40188264583418910740442583 60282396875128366110663875)
        ·
          refine ⟨90423595312692549165995813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60282396875128366110663875 90423595312692549165995813)
          ·
            refine ⟨16954424121129852968624215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90423595312692549165995813 16954424121129852968624215)
            ·
              refine ⟨25431636181694779452936323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16954424121129852968624215 25431636181694779452936323)
              ·
                refine ⟨38147454272542169179404485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25431636181694779452936323 38147454272542169179404485)
                ·
                  refine ⟨7152647676101656721138341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38147454272542169179404485 7152647676101656721138341)
                  ·
                    refine ⟨1341121439269060635213439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152647676101656721138341 1341121439269060635213439)
                    ·
                      rfl

theorem cell23_7835474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_7835474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835474 prefixEnd_7835474 := by exact prefixLift 7835474
  have htrace : WordTrace (prefixWord ++ tailWord_7835474) baseStart_7835474 baseEnd_7835474 := by
    simpa [prefixWord, tailWord_7835474, baseEnd_7835474] using wordTrace_append hprefix tailTrace_7835474
  have hstable : (prefixWord ++ tailWord_7835474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835474).length < 2 ^ (prefixWord ++ tailWord_7835474).sum := by decide
  have hdescent : baseEnd_7835474 < baseStart_7835474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835480 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_7835480 : Nat := 118140960795 + 7835480 * 2 ^ 59
def prefixEnd_7835480 : Nat := 4983230072969 + 3 ^ 40 * 7835480 * 2
def baseEnd_7835480 : Nat := 4023367398691108882165289

theorem tailTrace_7835480 : CollatzResearch.WordTrace tailWord_7835480 prefixEnd_7835480 4023367398691108882165289 := by
  unfold tailWord_7835480
  simp only [CollatzResearch.WordTrace]
  refine ⟨142891716826700814145043947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190522289102267752193391929 142891716826700814145043947)
  ·
    refine ⟨214337575240051221217565921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142891716826700814145043947 214337575240051221217565921)
    ·
      refine ⟨160753181430038415913174441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214337575240051221217565921 160753181430038415913174441)
      ·
        refine ⟨120564886072528811934880831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160753181430038415913174441 120564886072528811934880831)
        ·
          refine ⟨180847329108793217902321247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120564886072528811934880831 180847329108793217902321247)
          ·
            refine ⟨271270993663189826853481871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180847329108793217902321247 271270993663189826853481871)
            ·
              refine ⟨406906490494784740280222807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271270993663189826853481871 406906490494784740280222807)
              ·
                refine ⟨610359735742177110420334211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406906490494784740280222807 610359735742177110420334211)
                ·
                  refine ⟨915539603613265665630501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610359735742177110420334211 915539603613265665630501317)
                  ·
                    refine ⟨171663675677487312305718997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915539603613265665630501317 171663675677487312305718997)
                    ·
                      refine ⟨4023367398691108882165289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171663675677487312305718997 4023367398691108882165289)
                      ·
                        rfl

theorem cell23_7835480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_7835480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835480 prefixEnd_7835480 := by exact prefixLift 7835480
  have htrace : WordTrace (prefixWord ++ tailWord_7835480) baseStart_7835480 baseEnd_7835480 := by
    simpa [prefixWord, tailWord_7835480, baseEnd_7835480] using wordTrace_append hprefix tailTrace_7835480
  have hstable : (prefixWord ++ tailWord_7835480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835480).length < 2 ^ (prefixWord ++ tailWord_7835480).sum := by decide
  have hdescent : baseEnd_7835480 < baseStart_7835480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835481 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 3, 2, 2]
def baseStart_7835481 : Nat := 118140960795 + 7835481 * 2 ^ 59
def prefixEnd_7835481 : Nat := 4983230072969 + 3 ^ 40 * 7835481 * 2
def baseEnd_7835481 : Nat := 4023367912171763378252785

theorem tailTrace_7835481 : CollatzResearch.WordTrace tailWord_7835481 prefixEnd_7835481 4023367912171763378252785 := by
  unfold tailWord_7835481
  simp only [CollatzResearch.WordTrace]
  refine ⟨285783470126398005460874297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190522313417598670307249531 285783470126398005460874297)
  ·
    refine ⟨214337602594798504095655723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285783470126398005460874297 214337602594798504095655723)
    ·
      refine ⟨321506403892197756143483585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214337602594798504095655723 321506403892197756143483585)
      ·
        refine ⟨241129802919148317107612689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321506403892197756143483585 241129802919148317107612689)
        ·
          refine ⟨180847352189361237830709517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241129802919148317107612689 180847352189361237830709517)
          ·
            refine ⟨67817757071010464186516069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180847352189361237830709517 67817757071010464186516069)
            ·
              refine ⟨12715829450814462034971763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67817757071010464186516069 12715829450814462034971763)
              ·
                refine ⟨19073744176221693052457645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715829450814462034971763 19073744176221693052457645)
                ·
                  refine ⟨7152654066083134894671617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19073744176221693052457645 7152654066083134894671617)
                  ·
                    refine ⟨5364490549562351171003713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152654066083134894671617 5364490549562351171003713)
                    ·
                      refine ⟨4023367912171763378252785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364490549562351171003713 4023367912171763378252785)
                      ·
                        rfl

theorem cell23_7835481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_7835481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835481 prefixEnd_7835481 := by exact prefixLift 7835481
  have htrace : WordTrace (prefixWord ++ tailWord_7835481) baseStart_7835481 baseEnd_7835481 := by
    simpa [prefixWord, tailWord_7835481, baseEnd_7835481] using wordTrace_append hprefix tailTrace_7835481
  have hstable : (prefixWord ++ tailWord_7835481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835481).length < 2 ^ (prefixWord ++ tailWord_7835481).sum := by decide
  have hdescent : baseEnd_7835481 < baseStart_7835481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835491 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 6]
def baseStart_7835491 : Nat := 118140960795 + 7835491 * 2 ^ 59
def prefixEnd_7835491 : Nat := 4983230072969 + 3 ^ 40 * 7835491 * 2
def baseEnd_7835491 : Nat := 1341124348992769446375913

theorem tailTrace_7835491 : CollatzResearch.WordTrace tailWord_7835491 prefixEnd_7835491 1341124348992769446375913 := by
  unfold tailWord_7835491
  simp only [CollatzResearch.WordTrace]
  refine ⟨285783834856361777168738327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190522556570907851445825551 285783834856361777168738327)
  ·
    refine ⟨428675752284542665753107491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285783834856361777168738327 428675752284542665753107491)
    ·
      refine ⟨643013628426813998629661237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428675752284542665753107491 643013628426813998629661237)
      ·
        refine ⟨60282527665013812371530741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 643013628426813998629661237 60282527665013812371530741)
        ·
          refine ⟨5651486968595044909831007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60282527665013812371530741 5651486968595044909831007)
          ·
            refine ⟨8477230452892567364746511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651486968595044909831007 8477230452892567364746511)
            ·
              refine ⟨12715845679338851047119767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477230452892567364746511 12715845679338851047119767)
              ·
                refine ⟨19073768519008276570679651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12715845679338851047119767 19073768519008276570679651)
                ·
                  refine ⟨28610652778512414856019477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19073768519008276570679651 28610652778512414856019477)
                  ·
                    refine ⟨1341124348992769446375913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28610652778512414856019477 1341124348992769446375913)
                    ·
                      rfl

theorem cell23_7835491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 6].length) (baseStart_7835491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835491 prefixEnd_7835491 := by exact prefixLift 7835491
  have htrace : WordTrace (prefixWord ++ tailWord_7835491) baseStart_7835491 baseEnd_7835491 := by
    simpa [prefixWord, tailWord_7835491, baseEnd_7835491] using wordTrace_append hprefix tailTrace_7835491
  have hstable : (prefixWord ++ tailWord_7835491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835491).length < 2 ^ (prefixWord ++ tailWord_7835491).sum := by decide
  have hdescent : baseEnd_7835491 < baseStart_7835491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835498 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7835498 : Nat := 118140960795 + 7835498 * 2 ^ 59
def prefixEnd_7835498 : Nat := 4983230072969 + 3 ^ 40 * 7835498 * 2
def baseEnd_7835498 : Nat := 4023376641342889811740207

theorem tailTrace_7835498 : CollatzResearch.WordTrace tailWord_7835498 prefixEnd_7835498 4023376641342889811740207 := by
  unfold tailWord_7835498
  simp only [CollatzResearch.WordTrace]
  refine ⟨71446022541834104341060787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190522726778224278242828765 71446022541834104341060787)
  ·
    refine ⟨107169033812751156511591181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71446022541834104341060787 107169033812751156511591181)
    ·
      refine ⟨40188387679781683691846693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107169033812751156511591181 40188387679781683691846693)
      ·
        refine ⟨7535322689959065692221255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40188387679781683691846693 7535322689959065692221255)
        ·
          refine ⟨11302984034938598538331883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535322689959065692221255 11302984034938598538331883)
          ·
            refine ⟨16954476052407897807497825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302984034938598538331883 16954476052407897807497825)
            ·
              refine ⟨12715857039305923355623369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16954476052407897807497825 12715857039305923355623369)
              ·
                refine ⟨9536892779479442516717527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12715857039305923355623369 9536892779479442516717527)
                ·
                  refine ⟨14305339169219163775076291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9536892779479442516717527 14305339169219163775076291)
                  ·
                    refine ⟨21458008753828745662614437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14305339169219163775076291 21458008753828745662614437)
                    ·
                      refine ⟨4023376641342889811740207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21458008753828745662614437 4023376641342889811740207)
                      ·
                        rfl

theorem cell23_7835498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7835498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835498 prefixEnd_7835498 := by exact prefixLift 7835498
  have htrace : WordTrace (prefixWord ++ tailWord_7835498) baseStart_7835498 baseEnd_7835498 := by
    simpa [prefixWord, tailWord_7835498, baseEnd_7835498] using wordTrace_append hprefix tailTrace_7835498
  have hstable : (prefixWord ++ tailWord_7835498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835498).length < 2 ^ (prefixWord ++ tailWord_7835498).sum := by decide
  have hdescent : baseEnd_7835498 < baseStart_7835498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835514 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_7835514 : Nat := 118140960795 + 7835514 * 2 ^ 59
def prefixEnd_7835514 : Nat := 4983230072969 + 3 ^ 40 * 7835514 * 2
def baseEnd_7835514 : Nat := 4023384857033361749140133

theorem tailTrace_7835514 : CollatzResearch.WordTrace tailWord_7835514 prefixEnd_7835514 4023384857033361749140133 := by
  unfold tailWord_7835514
  simp only [CollatzResearch.WordTrace]
  refine ⟨71446168433819613024206399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190523115823518968064550397 71446168433819613024206399)
  ·
    refine ⟨107169252650729419536309599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71446168433819613024206399 107169252650729419536309599)
    ·
      refine ⟨160753878976094129304464399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107169252650729419536309599 160753878976094129304464399)
      ·
        refine ⟨241130818464141193956696599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160753878976094129304464399 241130818464141193956696599)
        ·
          refine ⟨361696227696211790935044899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241130818464141193956696599 361696227696211790935044899)
          ·
            refine ⟨542544341544317686402567349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361696227696211790935044899 542544341544317686402567349)
            ·
              refine ⟨50863532019779783100240689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542544341544317686402567349 50863532019779783100240689)
              ·
                refine ⟨38147649014834837325180517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50863532019779783100240689 38147649014834837325180517)
                ·
                  refine ⟨7152684190281531998471347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38147649014834837325180517 7152684190281531998471347)
                  ·
                    refine ⟨10729026285422297997707021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152684190281531998471347 10729026285422297997707021)
                    ·
                      refine ⟨4023384857033361749140133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729026285422297997707021 4023384857033361749140133)
                      ·
                        rfl

theorem cell23_7835514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_7835514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835514 prefixEnd_7835514 := by exact prefixLift 7835514
  have htrace : WordTrace (prefixWord ++ tailWord_7835514) baseStart_7835514 baseEnd_7835514 := by
    simpa [prefixWord, tailWord_7835514, baseEnd_7835514] using wordTrace_append hprefix tailTrace_7835514
  have hstable : (prefixWord ++ tailWord_7835514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835514).length < 2 ^ (prefixWord ++ tailWord_7835514).sum := by decide
  have hdescent : baseEnd_7835514 < baseStart_7835514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835518 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7835518 : Nat := 118140960795 + 7835518 * 2 ^ 59
def prefixEnd_7835518 : Nat := 4983230072969 + 3 ^ 40 * 7835518 * 2
def baseEnd_7835518 : Nat := 4023386910955979733490115

theorem tailTrace_7835518 : CollatzResearch.WordTrace tailWord_7835518 prefixEnd_7835518 4023386910955979733490115 := by
  unfold tailWord_7835518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35723102453407995097496401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190523213084842640519980805 35723102453407995097496401)
  ·
    refine ⟨26792326840055996323122301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35723102453407995097496401 26792326840055996323122301)
    ·
      refine ⟨10047122565020998621170863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26792326840055996323122301 10047122565020998621170863)
      ·
        refine ⟨15070683847531497931756295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047122565020998621170863 15070683847531497931756295)
        ·
          refine ⟨22606025771297246897634443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070683847531497931756295 22606025771297246897634443)
          ·
            refine ⟨33909038656945870346451665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22606025771297246897634443 33909038656945870346451665)
            ·
              refine ⟨25431778992709402759838749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33909038656945870346451665 25431778992709402759838749)
              ·
                refine ⟨9536917122266026034939531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25431778992709402759838749 9536917122266026034939531)
                ·
                  refine ⟨14305375683399039052409297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9536917122266026034939531 14305375683399039052409297)
                  ·
                    refine ⟨10729031762549279289306973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14305375683399039052409297 10729031762549279289306973)
                    ·
                      refine ⟨4023386910955979733490115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729031762549279289306973 4023386910955979733490115)
                      ·
                        rfl

theorem cell23_7835518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7835518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835518 prefixEnd_7835518 := by exact prefixLift 7835518
  have htrace : WordTrace (prefixWord ++ tailWord_7835518) baseStart_7835518 baseEnd_7835518 := by
    simpa [prefixWord, tailWord_7835518, baseEnd_7835518] using wordTrace_append hprefix tailTrace_7835518
  have hstable : (prefixWord ++ tailWord_7835518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835518).length < 2 ^ (prefixWord ++ tailWord_7835518).sum := by decide
  have hdescent : baseEnd_7835518 < baseStart_7835518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835521 : List Nat := [1, 2, 4, 4, 2, 1, 9]
def baseStart_7835521 : Nat := 118140960795 + 7835521 * 2 ^ 59
def prefixEnd_7835521 : Nat := 4983230072969 + 3 ^ 40 * 7835521 * 2
def baseEnd_7835521 : Nat := 49671462362937570638921

theorem tailTrace_7835521 : CollatzResearch.WordTrace tailWord_7835521 prefixEnd_7835521 49671462362937570638921 := by
  unfold tailWord_7835521
  simp only [CollatzResearch.WordTrace]
  refine ⟨285784929046253092292330417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190523286030835394861553611 285784929046253092292330417)
  ·
    refine ⟨214338696784689819219247813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285784929046253092292330417 214338696784689819219247813)
    ·
      refine ⟨40188505647129341103608965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214338696784689819219247813 40188505647129341103608965)
      ·
        refine ⟨7535344808836751456926681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40188505647129341103608965 7535344808836751456926681)
        ·
          refine ⟨5651508606627563592695011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535344808836751456926681 5651508606627563592695011)
          ·
            refine ⟨8477262909941345389042517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651508606627563592695011 8477262909941345389042517)
            ·
              refine ⟨49671462362937570638921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8477262909941345389042517 49671462362937570638921)
              ·
                rfl

theorem cell23_7835521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 9].length) (baseStart_7835521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835521 prefixEnd_7835521 := by exact prefixLift 7835521
  have htrace : WordTrace (prefixWord ++ tailWord_7835521) baseStart_7835521 baseEnd_7835521 := by
    simpa [prefixWord, tailWord_7835521, baseEnd_7835521] using wordTrace_append hprefix tailTrace_7835521
  have hstable : (prefixWord ++ tailWord_7835521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835521).length < 2 ^ (prefixWord ++ tailWord_7835521).sum := by decide
  have hdescent : baseEnd_7835521 < baseStart_7835521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835548 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7835548 : Nat := 118140960795 + 7835548 * 2 ^ 59
def prefixEnd_7835548 : Nat := 4983230072969 + 3 ^ 40 * 7835548 * 2
def baseEnd_7835548 : Nat := 4023402315375614616114977

theorem tailTrace_7835548 : CollatzResearch.WordTrace tailWord_7835548 prefixEnd_7835548 4023402315375614616114977 := by
  unfold tailWord_7835548
  simp only [CollatzResearch.WordTrace]
  refine ⟨142892956908577637951781649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190523942544770183935708865 142892956908577637951781649)
  ·
    refine ⟨107169717681433228463836237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142892956908577637951781649 107169717681433228463836237)
    ·
      refine ⟨40188644130537460673938589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107169717681433228463836237 40188644130537460673938589)
      ·
        refine ⟨15070741548951547752726971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40188644130537460673938589 15070741548951547752726971)
        ·
          refine ⟨22606112323427321629090457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070741548951547752726971 22606112323427321629090457)
          ·
            refine ⟨16954584242570491221817843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22606112323427321629090457 16954584242570491221817843)
            ·
              refine ⟨25431876363855736832726765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16954584242570491221817843 25431876363855736832726765)
              ·
                refine ⟨9536953636445901312272537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25431876363855736832726765 9536953636445901312272537)
                ·
                  refine ⟨7152715227334425984204403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536953636445901312272537 7152715227334425984204403)
                  ·
                    refine ⟨10729072841001638976306605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152715227334425984204403 10729072841001638976306605)
                    ·
                      refine ⟨4023402315375614616114977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729072841001638976306605 4023402315375614616114977)
                      ·
                        rfl

theorem cell23_7835548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7835548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835548 prefixEnd_7835548 := by exact prefixLift 7835548
  have htrace : WordTrace (prefixWord ++ tailWord_7835548) baseStart_7835548 baseEnd_7835548 := by
    simpa [prefixWord, tailWord_7835548, baseEnd_7835548] using wordTrace_append hprefix tailTrace_7835548
  have hstable : (prefixWord ++ tailWord_7835548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835548).length < 2 ^ (prefixWord ++ tailWord_7835548).sum := by decide
  have hdescent : baseEnd_7835548 < baseStart_7835548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835607 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 7]
def baseStart_7835607 : Nat := 118140960795 + 7835607 * 2 ^ 59
def prefixEnd_7835607 : Nat := 4983230072969 + 3 ^ 40 * 7835607 * 2
def baseEnd_7835607 : Nat := 1341144203578076628425735

theorem tailTrace_7835607 : CollatzResearch.WordTrace tailWord_7835607 prefixEnd_7835607 1341144203578076628425735 := by
  unfold tailWord_7835607
  simp only [CollatzResearch.WordTrace]
  refine ⟨285788065723941528979961075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190525377149294352653307383 285788065723941528979961075)
  ·
    refine ⟨428682098585912293469941613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285788065723941528979961075 428682098585912293469941613)
    ·
      refine ⟨160755786969717110051228105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428682098585912293469941613 160755786969717110051228105)
      ·
        refine ⟨120566840227287832538421079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160755786969717110051228105 120566840227287832538421079)
        ·
          refine ⟨180850260340931748807631619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120566840227287832538421079 180850260340931748807631619)
          ·
            refine ⟨271275390511397623211447429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180850260340931748807631619 271275390511397623211447429)
            ·
              refine ⟨50864135720887054352146393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271275390511397623211447429 50864135720887054352146393)
              ·
                refine ⟨38148101790665290764109795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50864135720887054352146393 38148101790665290764109795)
                ·
                  refine ⟨57222152685997936146164693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38148101790665290764109795 57222152685997936146164693)
                  ·
                    refine ⟨1341144203578076628425735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57222152685997936146164693 1341144203578076628425735)
                    ·
                      rfl

theorem cell23_7835607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_7835607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835607 prefixEnd_7835607 := by exact prefixLift 7835607
  have htrace : WordTrace (prefixWord ++ tailWord_7835607) baseStart_7835607 baseEnd_7835607 := by
    simpa [prefixWord, tailWord_7835607, baseEnd_7835607] using wordTrace_append hprefix tailTrace_7835607
  have hstable : (prefixWord ++ tailWord_7835607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835607).length < 2 ^ (prefixWord ++ tailWord_7835607).sum := by decide
  have hdescent : baseEnd_7835607 < baseStart_7835607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835617 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7835617 : Nat := 118140960795 + 7835617 * 2 ^ 59
def prefixEnd_7835617 : Nat := 4983230072969 + 3 ^ 40 * 7835617 * 2
def baseEnd_7835617 : Nat := 4023437745540774846152159

theorem tailTrace_7835617 : CollatzResearch.WordTrace tailWord_7835617 prefixEnd_7835617 4023437745540774846152159 := by
  unfold tailWord_7835617
  simp only [CollatzResearch.WordTrace]
  refine ⟨285788430453905300687825105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190525620302603533791883403 285788430453905300687825105)
  ·
    refine ⟨214341322840428975515868829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285788430453905300687825105 214341322840428975515868829)
    ·
      refine ⟨80377996065160865818450811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214341322840428975515868829 80377996065160865818450811)
      ·
        refine ⟨120566994097741298727676217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80377996065160865818450811 120566994097741298727676217)
        ·
          refine ⟨90425245573305974045757163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120566994097741298727676217 90425245573305974045757163)
          ·
            refine ⟨135637868359958961068635745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90425245573305974045757163 135637868359958961068635745)
            ·
              refine ⟨101728401269969220801476809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135637868359958961068635745 101728401269969220801476809)
              ·
                refine ⟨76296300952476915601107607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101728401269969220801476809 76296300952476915601107607)
                ·
                  refine ⟨114444451428715373401661411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76296300952476915601107607 114444451428715373401661411)
                  ·
                    refine ⟨171666677143073060102492117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114444451428715373401661411 171666677143073060102492117)
                    ·
                      refine ⟨4023437745540774846152159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171666677143073060102492117 4023437745540774846152159)
                      ·
                        rfl

theorem cell23_7835617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7835617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835617 prefixEnd_7835617 := by exact prefixLift 7835617
  have htrace : WordTrace (prefixWord ++ tailWord_7835617) baseStart_7835617 baseEnd_7835617 := by
    simpa [prefixWord, tailWord_7835617, baseEnd_7835617] using wordTrace_append hprefix tailTrace_7835617
  have hstable : (prefixWord ++ tailWord_7835617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835617).length < 2 ^ (prefixWord ++ tailWord_7835617).sum := by decide
  have hdescent : baseEnd_7835617 < baseStart_7835617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835644 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_7835644 : Nat := 118140960795 + 7835644 * 2 ^ 59
def prefixEnd_7835644 : Nat := 4983230072969 + 3 ^ 40 * 7835644 * 2
def baseEnd_7835644 : Nat := 4023451609518446240514535

theorem tailTrace_7835644 : CollatzResearch.WordTrace tailWord_7835644 prefixEnd_7835644 4023451609518446240514535 := by
  unfold tailWord_7835644
  simp only [CollatzResearch.WordTrace]
  refine ⟨142894707612403742149528993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190526276816538322866038657 142894707612403742149528993)
  ·
    refine ⟨107171030709302806612146745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142894707612403742149528993 107171030709302806612146745)
    ·
      refine ⟨80378273031977104959110059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107171030709302806612146745 80378273031977104959110059)
      ·
        refine ⟨120567409547965657438665089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80378273031977104959110059 120567409547965657438665089)
        ·
          refine ⟨90425557160974243078998817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120567409547965657438665089 90425557160974243078998817)
          ·
            refine ⟨67819167870730682309249113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90425557160974243078998817 67819167870730682309249113)
            ·
              refine ⟨50864375903048011731936835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67819167870730682309249113 50864375903048011731936835)
              ·
                refine ⟨76296563854572017597905253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50864375903048011731936835 76296563854572017597905253)
                ·
                  refine ⟨14305605722732253299607235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76296563854572017597905253 14305605722732253299607235)
                  ·
                    refine ⟨21458408584098379949410853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14305605722732253299607235 21458408584098379949410853)
                    ·
                      refine ⟨4023451609518446240514535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21458408584098379949410853 4023451609518446240514535)
                      ·
                        rfl

theorem cell23_7835644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_7835644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835644 prefixEnd_7835644 := by exact prefixLift 7835644
  have htrace : WordTrace (prefixWord ++ tailWord_7835644) baseStart_7835644 baseEnd_7835644 := by
    simpa [prefixWord, tailWord_7835644, baseEnd_7835644] using wordTrace_append hprefix tailTrace_7835644
  have hstable : (prefixWord ++ tailWord_7835644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835644).length < 2 ^ (prefixWord ++ tailWord_7835644).sum := by decide
  have hdescent : baseEnd_7835644 < baseStart_7835644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835647 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_7835647 : Nat := 118140960795 + 7835647 * 2 ^ 59
def prefixEnd_7835647 : Nat := 4983230072969 + 3 ^ 40 * 7835647 * 2
def baseEnd_7835647 : Nat := 4023453149960409728777021

theorem tailTrace_7835647 : CollatzResearch.WordTrace tailWord_7835647 prefixEnd_7835647 4023453149960409728777021 := by
  unfold tailWord_7835647
  simp only [CollatzResearch.WordTrace]
  refine ⟨285789524643796615811417195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190526349762531077207611463 285789524643796615811417195)
  ·
    refine ⟨428684286965694923717125793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285789524643796615811417195 428684286965694923717125793)
    ·
      refine ⟨321513215224271192787844345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428684286965694923717125793 321513215224271192787844345)
      ·
        refine ⟨241134911418203394590883259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321513215224271192787844345 241134911418203394590883259)
        ·
          refine ⟨361702367127305091886324889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241134911418203394590883259 361702367127305091886324889)
          ·
            refine ⟨271276775345478818914743667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361702367127305091886324889 271276775345478818914743667)
            ·
              refine ⟨406915163018218228372115501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271276775345478818914743667 406915163018218228372115501)
              ·
                refine ⟨152593186131831835639543313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406915163018218228372115501 152593186131831835639543313)
                ·
                  refine ⟨114444889598873876729657485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152593186131831835639543313 114444889598873876729657485)
                  ·
                    refine ⟨42916833599577703773621557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114444889598873876729657485 42916833599577703773621557)
                    ·
                      refine ⟨4023453149960409728777021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42916833599577703773621557 4023453149960409728777021)
                      ·
                        rfl

theorem cell23_7835647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_7835647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835647 prefixEnd_7835647 := by exact prefixLift 7835647
  have htrace : WordTrace (prefixWord ++ tailWord_7835647) baseStart_7835647 baseEnd_7835647 := by
    simpa [prefixWord, tailWord_7835647, baseEnd_7835647] using wordTrace_append hprefix tailTrace_7835647
  have hstable : (prefixWord ++ tailWord_7835647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835647).length < 2 ^ (prefixWord ++ tailWord_7835647).sum := by decide
  have hdescent : baseEnd_7835647 < baseStart_7835647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_7835664 : Nat := 118140960795 + 7835664 * 2 ^ 59
def prefixEnd_7835664 : Nat := 4983230072969 + 3 ^ 40 * 7835664 * 2
def baseEnd_7835664 : Nat := 4023461879131536162264443

theorem tailTrace_7835664 : CollatzResearch.WordTrace tailWord_7835664 prefixEnd_7835664 4023461879131536162264443 := by
  unfold tailWord_7835664
  simp only [CollatzResearch.WordTrace]
  refine ⟨142895072342367513857393023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190526763123156685143190697 142895072342367513857393023)
  ·
    refine ⟨214342608513551270786089535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142895072342367513857393023 214342608513551270786089535)
    ·
      refine ⟨321513912770326906179134303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214342608513551270786089535 321513912770326906179134303)
      ·
        refine ⟨482270869155490359268701455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321513912770326906179134303 482270869155490359268701455)
        ·
          refine ⟨723406303733235538903052183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482270869155490359268701455 723406303733235538903052183)
          ·
            refine ⟨1085109455599853308354578275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723406303733235538903052183 1085109455599853308354578275)
            ·
              refine ⟨1627664183399779962531867413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085109455599853308354578275 1627664183399779962531867413)
              ·
                refine ⟨76296758596864685743681285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627664183399779962531867413 76296758596864685743681285)
                ·
                  refine ⟨14305642236912128576940241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76296758596864685743681285 14305642236912128576940241)
                  ·
                    refine ⟨10729231677684096432705181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14305642236912128576940241 10729231677684096432705181)
                    ·
                      refine ⟨4023461879131536162264443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729231677684096432705181 4023461879131536162264443)
                      ·
                        rfl

theorem cell23_7835664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_7835664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835664 prefixEnd_7835664 := by exact prefixLift 7835664
  have htrace : WordTrace (prefixWord ++ tailWord_7835664) baseStart_7835664 baseEnd_7835664 := by
    simpa [prefixWord, tailWord_7835664, baseEnd_7835664] using wordTrace_append hprefix tailTrace_7835664
  have hstable : (prefixWord ++ tailWord_7835664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835664).length < 2 ^ (prefixWord ++ tailWord_7835664).sum := by decide
  have hdescent : baseEnd_7835664 < baseStart_7835664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835705 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_7835705 : Nat := 118140960795 + 7835705 * 2 ^ 59
def prefixEnd_7835705 : Nat := 4983230072969 + 3 ^ 40 * 7835705 * 2
def baseEnd_7835705 : Nat := 1341160977279456833950585

theorem tailTrace_7835705 : CollatzResearch.WordTrace tailWord_7835705 prefixEnd_7835705 1341160977279456833950585 := by
  unfold tailWord_7835705
  simp only [CollatzResearch.WordTrace]
  refine ⟨285791640077586491717028569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190527760051724327811352379 285791640077586491717028569)
  ·
    refine ⟨214343730058189868787771427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285791640077586491717028569 214343730058189868787771427)
    ·
      refine ⟨321515595087284803181657141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214343730058189868787771427 321515595087284803181657141)
      ·
        refine ⟨30142087039432950298280357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321515595087284803181657141 30142087039432950298280357)
        ·
          refine ⟨5651641319893678180927567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30142087039432950298280357 5651641319893678180927567)
          ·
            refine ⟨8477461979840517271391351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651641319893678180927567 8477461979840517271391351)
            ·
              refine ⟨12716192969760775907087027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477461979840517271391351 12716192969760775907087027)
              ·
                refine ⟨19074289454641163860630541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716192969760775907087027 19074289454641163860630541)
                ·
                  refine ⟨7152858545490436447736453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19074289454641163860630541 7152858545490436447736453)
                  ·
                    refine ⟨1341160977279456833950585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152858545490436447736453 1341160977279456833950585)
                    ·
                      rfl

theorem cell23_7835705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_7835705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835705 prefixEnd_7835705 := by exact prefixLift 7835705
  have htrace : WordTrace (prefixWord ++ tailWord_7835705) baseStart_7835705 baseEnd_7835705 := by
    simpa [prefixWord, tailWord_7835705, baseEnd_7835705] using wordTrace_append hprefix tailTrace_7835705
  have hstable : (prefixWord ++ tailWord_7835705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835705).length < 2 ^ (prefixWord ++ tailWord_7835705).sum := by decide
  have hdescent : baseEnd_7835705 < baseStart_7835705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835718 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7835718 : Nat := 118140960795 + 7835718 * 2 ^ 59
def prefixEnd_7835718 : Nat := 4983230072969 + 3 ^ 40 * 7835718 * 2
def baseEnd_7835718 : Nat := 447054400787430994554355

theorem tailTrace_7835718 : CollatzResearch.WordTrace tailWord_7835718 prefixEnd_7835718 447054400787430994554355 := by
  unfold tailWord_7835718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931003569579356091789119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190528076151026263291501205 8931003569579356091789119)
  ·
    refine ⟨13396505354369034137683679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931003569579356091789119 13396505354369034137683679)
    ·
      refine ⟨20094758031553551206525519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13396505354369034137683679 20094758031553551206525519)
      ·
        refine ⟨30142137047330326809788279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20094758031553551206525519 30142137047330326809788279)
        ·
          refine ⟨45213205570995490214682419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30142137047330326809788279 45213205570995490214682419)
          ·
            refine ⟨67819808356493235322023629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45213205570995490214682419 67819808356493235322023629)
            ·
              refine ⟨25432428133684963245758861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67819808356493235322023629 25432428133684963245758861)
              ·
                refine ⟨9537160550131861217159573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25432428133684963245758861 9537160550131861217159573)
                ·
                  refine ⟨447054400787430994554355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9537160550131861217159573 447054400787430994554355)
                  ·
                    rfl

theorem cell23_7835718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7835718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835718 prefixEnd_7835718 := by exact prefixLift 7835718
  have htrace : WordTrace (prefixWord ++ tailWord_7835718) baseStart_7835718 baseEnd_7835718 := by
    simpa [prefixWord, tailWord_7835718, baseEnd_7835718] using wordTrace_append hprefix tailTrace_7835718
  have hstable : (prefixWord ++ tailWord_7835718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835718).length < 2 ^ (prefixWord ++ tailWord_7835718).sum := by decide
  have hdescent : baseEnd_7835718 < baseStart_7835718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835721 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 4, 3, 2]
def baseStart_7835721 : Nat := 118140960795 + 7835721 * 2 ^ 59
def prefixEnd_7835721 : Nat := 4983230072969 + 3 ^ 40 * 7835721 * 2
def baseEnd_7835721 : Nat := 4023491147528842439251681

theorem tailTrace_7835721 : CollatzResearch.WordTrace tailWord_7835721 prefixEnd_7835721 4023491147528842439251681 := by
  unfold tailWord_7835721
  simp only [CollatzResearch.WordTrace]
  refine ⟨285792223645528526449611017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190528149097019017633074011 285792223645528526449611017)
  ·
    refine ⟨214344167734146394837208263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285792223645528526449611017 214344167734146394837208263)
    ·
      refine ⟨321516251601219592255812395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214344167734146394837208263 321516251601219592255812395)
      ·
        refine ⟨482274377401829388383718593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321516251601219592255812395 482274377401829388383718593)
        ·
          refine ⟨361705783051372041287788945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482274377401829388383718593 361705783051372041287788945)
          ·
            refine ⟨271279337288529030965841709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361705783051372041287788945 271279337288529030965841709)
            ·
              refine ⟨101729751483198386612190641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271279337288529030965841709 101729751483198386612190641)
              ·
                refine ⟨76297313612398789959142981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101729751483198386612190641 76297313612398789959142981)
                ·
                  refine ⟨14305746302324773117339309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76297313612398789959142981 14305746302324773117339309)
                  ·
                    refine ⟨5364654863371789919002241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14305746302324773117339309 5364654863371789919002241)
                    ·
                      refine ⟨4023491147528842439251681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364654863371789919002241 4023491147528842439251681)
                      ·
                        rfl

theorem cell23_7835721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3, 2].length) (baseStart_7835721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835721 prefixEnd_7835721 := by exact prefixLift 7835721
  have htrace : WordTrace (prefixWord ++ tailWord_7835721) baseStart_7835721 baseEnd_7835721 := by
    simpa [prefixWord, tailWord_7835721, baseEnd_7835721] using wordTrace_append hprefix tailTrace_7835721
  have hstable : (prefixWord ++ tailWord_7835721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835721).length < 2 ^ (prefixWord ++ tailWord_7835721).sum := by decide
  have hdescent : baseEnd_7835721 < baseStart_7835721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835738 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_7835738 : Nat := 118140960795 + 7835738 * 2 ^ 59
def prefixEnd_7835738 : Nat := 4983230072969 + 3 ^ 40 * 7835738 * 2
def baseEnd_7835738 : Nat := 4023499876699968872739103

theorem tailTrace_7835738 : CollatzResearch.WordTrace tailWord_7835738 prefixEnd_7835738 4023499876699968872739103 := by
  unfold tailWord_7835738
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448210921616734588244967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190528562457644625568653245 71448210921616734588244967)
  ·
    refine ⟨107172316382425101882367451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71448210921616734588244967 107172316382425101882367451)
    ·
      refine ⟨160758474573637652823551177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107172316382425101882367451 160758474573637652823551177)
      ·
        refine ⟨120568855930228239617663383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160758474573637652823551177 120568855930228239617663383)
        ·
          refine ⟨180853283895342359426495075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120568855930228239617663383 180853283895342359426495075)
          ·
            refine ⟨271279925843013539139742613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180853283895342359426495075 271279925843013539139742613)
            ·
              refine ⟨12716246523891259647175435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271279925843013539139742613 12716246523891259647175435)
              ·
                refine ⟨19074369785836889470763153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716246523891259647175435 19074369785836889470763153)
                ·
                  refine ⟨14305777339377667103072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19074369785836889470763153 14305777339377667103072365)
                  ·
                    refine ⟨5364666502266625163652137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14305777339377667103072365 5364666502266625163652137)
                    ·
                      refine ⟨4023499876699968872739103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364666502266625163652137 4023499876699968872739103)
                      ·
                        rfl

theorem cell23_7835738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_7835738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835738 prefixEnd_7835738 := by exact prefixLift 7835738
  have htrace : WordTrace (prefixWord ++ tailWord_7835738) baseStart_7835738 baseEnd_7835738 := by
    simpa [prefixWord, tailWord_7835738, baseEnd_7835738] using wordTrace_append hprefix tailTrace_7835738
  have hstable : (prefixWord ++ tailWord_7835738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835738).length < 2 ^ (prefixWord ++ tailWord_7835738).sum := by decide
  have hdescent : baseEnd_7835738 < baseStart_7835738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835744 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_7835744 : Nat := 118140960795 + 7835744 * 2 ^ 59
def prefixEnd_7835744 : Nat := 4983230072969 + 3 ^ 40 * 7835744 * 2
def baseEnd_7835744 : Nat := 1341167652527965283088025

theorem tailTrace_7835744 : CollatzResearch.WordTrace tailWord_7835744 prefixEnd_7835744 1341167652527965283088025 := by
  unfold tailWord_7835744
  simp only [CollatzResearch.WordTrace]
  refine ⟨142896531262222600688849143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190528708349630134251798857 142896531262222600688849143)
  ·
    refine ⟨214344796893333901033273715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142896531262222600688849143 214344796893333901033273715)
    ·
      refine ⟨321517195340000851549910573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214344796893333901033273715 321517195340000851549910573)
      ·
        refine ⟨120568948252500319331216465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321517195340000851549910573 120568948252500319331216465)
        ·
          refine ⟨90426711189375239498412349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120568948252500319331216465 90426711189375239498412349)
          ·
            refine ⟨33910016696015714811904631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90426711189375239498412349 33910016696015714811904631)
            ·
              refine ⟨50865025044023572217856947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33910016696015714811904631 50865025044023572217856947)
              ·
                refine ⟨76297537566035358326785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50865025044023572217856947 76297537566035358326785421)
                ·
                  refine ⟨28611576587263259372544533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76297537566035358326785421 28611576587263259372544533)
                  ·
                    refine ⟨1341167652527965283088025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28611576587263259372544533 1341167652527965283088025)
                    ·
                      rfl

theorem cell23_7835744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_7835744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835744 prefixEnd_7835744 := by exact prefixLift 7835744
  have htrace : WordTrace (prefixWord ++ tailWord_7835744) baseStart_7835744 baseEnd_7835744 := by
    simpa [prefixWord, tailWord_7835744, baseEnd_7835744] using wordTrace_append hprefix tailTrace_7835744
  have hstable : (prefixWord ++ tailWord_7835744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835744).length < 2 ^ (prefixWord ++ tailWord_7835744).sum := by decide
  have hdescent : baseEnd_7835744 < baseStart_7835744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835762 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_7835762 : Nat := 118140960795 + 7835762 * 2 ^ 59
def prefixEnd_7835762 : Nat := 4983230072969 + 3 ^ 40 * 7835762 * 2
def baseEnd_7835762 : Nat := 4023512200235676778838993

theorem tailTrace_7835762 : CollatzResearch.WordTrace tailWord_7835762 prefixEnd_7835762 4023512200235676778838993 := by
  unfold tailWord_7835762
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448429759594997612963385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190529146025586660301235693 71448429759594997612963385)
  ·
    refine ⟨53586322319696248209722539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71448429759594997612963385 53586322319696248209722539)
    ·
      refine ⟨80379483479544372314583809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53586322319696248209722539 80379483479544372314583809)
      ·
        refine ⟨60284612609658279235937857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80379483479544372314583809 60284612609658279235937857)
        ·
          refine ⟨45213459457243709426953393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60284612609658279235937857 45213459457243709426953393)
          ·
            refine ⟨33910094592932782070215045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45213459457243709426953393 33910094592932782070215045)
            ·
              refine ⟨6358142736174896638165321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33910094592932782070215045 6358142736174896638165321)
              ·
                refine ⟨4768607052131172478623991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358142736174896638165321 4768607052131172478623991)
                ·
                  refine ⟨7152910578196758717935987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768607052131172478623991 7152910578196758717935987)
                  ·
                    refine ⟨10729365867295138076903981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152910578196758717935987 10729365867295138076903981)
                    ·
                      refine ⟨4023512200235676778838993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729365867295138076903981 4023512200235676778838993)
                      ·
                        rfl

theorem cell23_7835762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_7835762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835762 prefixEnd_7835762 := by exact prefixLift 7835762
  have htrace : WordTrace (prefixWord ++ tailWord_7835762) baseStart_7835762 baseEnd_7835762 := by
    simpa [prefixWord, tailWord_7835762, baseEnd_7835762] using wordTrace_append hprefix tailTrace_7835762
  have hstable : (prefixWord ++ tailWord_7835762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835762).length < 2 ^ (prefixWord ++ tailWord_7835762).sum := by decide
  have hdescent : baseEnd_7835762 < baseStart_7835762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835768 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_7835768 : Nat := 118140960795 + 7835768 * 2 ^ 59
def prefixEnd_7835768 : Nat := 4983230072969 + 3 ^ 40 * 7835768 * 2
def baseEnd_7835768 : Nat := 4023515281119603755363965

theorem tailTrace_7835768 : CollatzResearch.WordTrace tailWord_7835768 prefixEnd_7835768 4023515281119603755363965 := by
  unfold tailWord_7835768
  simp only [CollatzResearch.WordTrace]
  refine ⟨142896968938179126738285979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190529291917572168984381305 142896968938179126738285979)
  ·
    refine ⟨214345453407268690107428969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142896968938179126738285979 214345453407268690107428969)
    ·
      refine ⟨160759090055451517580571727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214345453407268690107428969 160759090055451517580571727)
      ·
        refine ⟨241138635083177276370857591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160759090055451517580571727 241138635083177276370857591)
        ·
          refine ⟨361707952624765914556286387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241138635083177276370857591 361707952624765914556286387)
          ·
            refine ⟨542561928937148871834429581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361707952624765914556286387 542561928937148871834429581)
            ·
              refine ⟨203460723351430826937911093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542561928937148871834429581 203460723351430826937911093)
              ·
                refine ⟨19074442814196640025429165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203460723351430826937911093 19074442814196640025429165)
                ·
                  refine ⟨7152916055323740009535937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19074442814196640025429165 7152916055323740009535937)
                  ·
                    refine ⟨5364687041492805007151953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152916055323740009535937 5364687041492805007151953)
                    ·
                      refine ⟨4023515281119603755363965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364687041492805007151953 4023515281119603755363965)
                      ·
                        rfl

theorem cell23_7835768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_7835768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835768 prefixEnd_7835768 := by exact prefixLift 7835768
  have htrace : WordTrace (prefixWord ++ tailWord_7835768) baseStart_7835768 baseEnd_7835768 := by
    simpa [prefixWord, tailWord_7835768, baseEnd_7835768] using wordTrace_append hprefix tailTrace_7835768
  have hstable : (prefixWord ++ tailWord_7835768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835768).length < 2 ^ (prefixWord ++ tailWord_7835768).sum := by decide
  have hdescent : baseEnd_7835768 < baseStart_7835768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835781 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_7835781 : Nat := 118140960795 + 7835781 * 2 ^ 59
def prefixEnd_7835781 : Nat := 4983230072969 + 3 ^ 40 * 7835781 * 2
def baseEnd_7835781 : Nat := 4023521956368112204501405

theorem tailTrace_7835781 : CollatzResearch.WordTrace tailWord_7835781 prefixEnd_7835781 4023521956368112204501405 := by
  unfold tailWord_7835781
  simp only [CollatzResearch.WordTrace]
  refine ⟨285794412025311156696795197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190529608016874104464530131 285794412025311156696795197)
  ·
    refine ⟨107172904509491683761298199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285794412025311156696795197 107172904509491683761298199)
    ·
      refine ⟨160759356764237525641947299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107172904509491683761298199 160759356764237525641947299)
      ·
        refine ⟨241139035146356288462920949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160759356764237525641947299 241139035146356288462920949)
        ·
          refine ⟨22606784544970902043398839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241139035146356288462920949 22606784544970902043398839)
          ·
            refine ⟨33910176817456353065098259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22606784544970902043398839 33910176817456353065098259)
            ·
              refine ⟨50865265226184529597647389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33910176817456353065098259 50865265226184529597647389)
              ·
                refine ⟨19074474459819198599117771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50865265226184529597647389 19074474459819198599117771)
                ·
                  refine ⟨28611711689728797898676657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19074474459819198599117771 28611711689728797898676657)
                  ·
                    refine ⟨21458783767296598424007493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28611711689728797898676657 21458783767296598424007493)
                    ·
                      refine ⟨4023521956368112204501405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21458783767296598424007493 4023521956368112204501405)
                      ·
                        rfl

theorem cell23_7835781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_7835781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835781 prefixEnd_7835781 := by exact prefixLift 7835781
  have htrace : WordTrace (prefixWord ++ tailWord_7835781) baseStart_7835781 baseEnd_7835781 := by
    simpa [prefixWord, tailWord_7835781, baseEnd_7835781] using wordTrace_append hprefix tailTrace_7835781
  have hstable : (prefixWord ++ tailWord_7835781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835781).length < 2 ^ (prefixWord ++ tailWord_7835781).sum := by decide
  have hdescent : baseEnd_7835781 < baseStart_7835781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835802 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7835802 : Nat := 118140960795 + 7835802 * 2 ^ 59
def prefixEnd_7835802 : Nat := 4983230072969 + 3 ^ 40 * 7835802 * 2
def baseEnd_7835802 : Nat := 4023532739461856622338809

theorem tailTrace_7835802 : CollatzResearch.WordTrace tailWord_7835802 prefixEnd_7835802 4023532739461856622338809 := by
  unfold tailWord_7835802
  simp only [CollatzResearch.WordTrace]
  refine ⟨71448794489558769320827415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190530118638823384855539773 71448794489558769320827415)
  ·
    refine ⟨107173191734338153981241123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71448794489558769320827415 107173191734338153981241123)
    ·
      refine ⟨160759787601507230971861685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107173191734338153981241123 160759787601507230971861685)
      ·
        refine ⟨15071230087641302903612033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160759787601507230971861685 15071230087641302903612033)
        ·
          refine ⟨11303422565730977177709025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15071230087641302903612033 11303422565730977177709025)
          ·
            refine ⟨8477566924298232883281769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11303422565730977177709025 8477566924298232883281769)
            ·
              refine ⟨6358175193223674662461327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477566924298232883281769 6358175193223674662461327)
              ·
                refine ⟨9537262789835511993691991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358175193223674662461327 9537262789835511993691991)
                ·
                  refine ⟨14305894184753267990537987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9537262789835511993691991 14305894184753267990537987)
                  ·
                    refine ⟨21458841277129901985806981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14305894184753267990537987 21458841277129901985806981)
                    ·
                      refine ⟨4023532739461856622338809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21458841277129901985806981 4023532739461856622338809)
                      ·
                        rfl

theorem cell23_7835802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7835802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835802 prefixEnd_7835802 := by exact prefixLift 7835802
  have htrace : WordTrace (prefixWord ++ tailWord_7835802) baseStart_7835802 baseEnd_7835802 := by
    simpa [prefixWord, tailWord_7835802, baseEnd_7835802] using wordTrace_append hprefix tailTrace_7835802
  have hstable : (prefixWord ++ tailWord_7835802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835802).length < 2 ^ (prefixWord ++ tailWord_7835802).sum := by decide
  have hdescent : baseEnd_7835802 < baseStart_7835802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835805 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_7835805 : Nat := 118140960795 + 7835805 * 2 ^ 59
def prefixEnd_7835805 : Nat := 4983230072969 + 3 ^ 40 * 7835805 * 2
def baseEnd_7835805 : Nat := 4023534279903820110601295

theorem tailTrace_7835805 : CollatzResearch.WordTrace tailWord_7835805 prefixEnd_7835805 4023534279903820110601295 := by
  unfold tailWord_7835805
  simp only [CollatzResearch.WordTrace]
  refine ⟨285795287377224208795668869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190530191584816139197112579 285795287377224208795668869)
  ·
    refine ⟨53586616383229539149187913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285795287377224208795668869 53586616383229539149187913)
    ·
      refine ⟨40189962287422154361890935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53586616383229539149187913 40189962287422154361890935)
      ·
        refine ⟨60284943431133231542836403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40189962287422154361890935 60284943431133231542836403)
        ·
          refine ⟨90427415146699847314254605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60284943431133231542836403 90427415146699847314254605)
          ·
            refine ⟨33910280680012442742845477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90427415146699847314254605 33910280680012442742845477)
            ·
              refine ⟨6358177627502333014283527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33910280680012442742845477 6358177627502333014283527)
              ·
                refine ⟨9537266441253499521425291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358177627502333014283527 9537266441253499521425291)
                ·
                  refine ⟨14305899661880249282137937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9537266441253499521425291 14305899661880249282137937)
                  ·
                    refine ⟨10729424746410186961603453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14305899661880249282137937 10729424746410186961603453)
                    ·
                      refine ⟨4023534279903820110601295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729424746410186961603453 4023534279903820110601295)
                      ·
                        rfl

theorem cell23_7835805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_7835805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835805 prefixEnd_7835805 := by exact prefixLift 7835805
  have htrace : WordTrace (prefixWord ++ tailWord_7835805) baseStart_7835805 baseEnd_7835805 := by
    simpa [prefixWord, tailWord_7835805, baseEnd_7835805] using wordTrace_append hprefix tailTrace_7835805
  have hstable : (prefixWord ++ tailWord_7835805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835805).length < 2 ^ (prefixWord ++ tailWord_7835805).sum := by decide
  have hdescent : baseEnd_7835805 < baseStart_7835805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835812 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_7835812 : Nat := 118140960795 + 7835812 * 2 ^ 59
def prefixEnd_7835812 : Nat := 4983230072969 + 3 ^ 40 * 7835812 * 2
def baseEnd_7835812 : Nat := 1341179291422800527737921

theorem tailTrace_7835812 : CollatzResearch.WordTrace tailWord_7835812 prefixEnd_7835812 1341179291422800527737921 := by
  unfold tailWord_7835812
  simp only [CollatzResearch.WordTrace]
  refine ⟨142897771344099424495586845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190530361792132565994115793 142897771344099424495586845)
  ·
    refine ⟨53586664254037284185845067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142897771344099424495586845 53586664254037284185845067)
    ·
      refine ⟨80379996381055926278767601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53586664254037284185845067 80379996381055926278767601)
      ·
        refine ⟨60284997285791944709075701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80379996381055926278767601 60284997285791944709075701)
        ·
          refine ⟨5651718495542994816475847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60284997285791944709075701 5651718495542994816475847)
          ·
            refine ⟨8477577743314492224713771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651718495542994816475847 8477577743314492224713771)
            ·
              refine ⟨12716366614971738337070657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477577743314492224713771 12716366614971738337070657)
              ·
                refine ⟨9537274961228803752802993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12716366614971738337070657 9537274961228803752802993)
                ·
                  refine ⟨7152956220921602814602245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537274961228803752802993 7152956220921602814602245)
                  ·
                    refine ⟨1341179291422800527737921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7152956220921602814602245 1341179291422800527737921)
                    ·
                      rfl

theorem cell23_7835812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_7835812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835812 prefixEnd_7835812 := by exact prefixLift 7835812
  have htrace : WordTrace (prefixWord ++ tailWord_7835812) baseStart_7835812 baseEnd_7835812 := by
    simpa [prefixWord, tailWord_7835812, baseEnd_7835812] using wordTrace_append hprefix tailTrace_7835812
  have hstable : (prefixWord ++ tailWord_7835812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835812).length < 2 ^ (prefixWord ++ tailWord_7835812).sum := by decide
  have hdescent : baseEnd_7835812 < baseStart_7835812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835835 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 2, 1, 3]
def baseStart_7835835 : Nat := 118140960795 + 7835835 * 2 ^ 59
def prefixEnd_7835835 : Nat := 4983230072969 + 3 ^ 40 * 7835835 * 2
def baseEnd_7835835 : Nat := 4023549684323454993226157

theorem tailTrace_7835835 : CollatzResearch.WordTrace tailWord_7835835 prefixEnd_7835835 4023549684323454993226157 := by
  unfold tailWord_7835835
  simp only [CollatzResearch.WordTrace]
  refine ⟨285796381567115523919260959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190530921044743682612840639 285796381567115523919260959)
  ·
    refine ⟨428694572350673285878891439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285796381567115523919260959 428694572350673285878891439)
    ·
      refine ⟨643041858526009928818337159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428694572350673285878891439 643041858526009928818337159)
      ·
        refine ⟨964562787789014893227505739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643041858526009928818337159 964562787789014893227505739)
        ·
          refine ⟨1446844181683522339841258609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964562787789014893227505739 1446844181683522339841258609)
          ·
            refine ⟨1085133136262641754880943957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446844181683522339841258609 1085133136262641754880943957)
            ·
              refine ⟨6358201970288916532505531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1085133136262641754880943957 6358201970288916532505531)
              ·
                refine ⟨9537302955433374798758297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358201970288916532505531 9537302955433374798758297)
                ·
                  refine ⟨7152977216575031099068723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537302955433374798758297 7152977216575031099068723)
                  ·
                    refine ⟨10729465824862546648603085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7152977216575031099068723 10729465824862546648603085)
                    ·
                      refine ⟨4023549684323454993226157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729465824862546648603085 4023549684323454993226157)
                      ·
                        rfl

theorem cell23_7835835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 1, 3].length) (baseStart_7835835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835835 prefixEnd_7835835 := by exact prefixLift 7835835
  have htrace : WordTrace (prefixWord ++ tailWord_7835835) baseStart_7835835 baseEnd_7835835 := by
    simpa [prefixWord, tailWord_7835835, baseEnd_7835835] using wordTrace_append hprefix tailTrace_7835835
  have hstable : (prefixWord ++ tailWord_7835835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835835).length < 2 ^ (prefixWord ++ tailWord_7835835).sum := by decide
  have hdescent : baseEnd_7835835 < baseStart_7835835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835842 : List Nat := [3, 5, 1, 1, 1, 3, 2, 7]
def baseStart_7835842 : Nat := 118140960795 + 7835842 * 2 ^ 59
def prefixEnd_7835842 : Nat := 4983230072969 + 3 ^ 40 * 7835842 * 2
def baseEnd_7835842 : Nat := 149020491803260609845875

theorem tailTrace_7835842 : CollatzResearch.WordTrace tailWord_7835842 prefixEnd_7835842 149020491803260609845875 := by
  unfold tailWord_7835842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71449159219522541028691445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190531091252060109409843853 71449159219522541028691445)
  ·
    refine ⟨6698358676830238221439823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71449159219522541028691445 6698358676830238221439823)
    ·
      refine ⟨10047538015245357332159735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6698358676830238221439823 10047538015245357332159735)
      ·
        refine ⟨15071307022868035998239603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047538015245357332159735 15071307022868035998239603)
        ·
          refine ⟨22606960534302053997359405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071307022868035998239603 22606960534302053997359405)
          ·
            refine ⟨8477610200363270249009777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22606960534302053997359405 8477610200363270249009777)
            ·
              refine ⟨6358207650272452686757333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477610200363270249009777 6358207650272452686757333)
              ·
                refine ⟨149020491803260609845875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6358207650272452686757333 149020491803260609845875)
                ·
                  rfl

theorem cell23_7835842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_7835842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835842 prefixEnd_7835842 := by exact prefixLift 7835842
  have htrace : WordTrace (prefixWord ++ tailWord_7835842) baseStart_7835842 baseEnd_7835842 := by
    simpa [prefixWord, tailWord_7835842, baseEnd_7835842] using wordTrace_append hprefix tailTrace_7835842
  have hstable : (prefixWord ++ tailWord_7835842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835842).length < 2 ^ (prefixWord ++ tailWord_7835842).sum := by decide
  have hdescent : baseEnd_7835842 < baseStart_7835842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835891 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3]
def baseStart_7835891 : Nat := 118140960795 + 7835891 * 2 ^ 59
def prefixEnd_7835891 : Nat := 4983230072969 + 3 ^ 40 * 7835891 * 2
def baseEnd_7835891 : Nat := 4023578439240106774125899

theorem tailTrace_7835891 : CollatzResearch.WordTrace tailWord_7835891 prefixEnd_7835891 4023578439240106774125899 := by
  unfold tailWord_7835891
  simp only [CollatzResearch.WordTrace]
  refine ⟨285798424054912645483299527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190532282703275096988866351 285798424054912645483299527)
  ·
    refine ⟨428697636082368968224949291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285798424054912645483299527 428697636082368968224949291)
    ·
      refine ⟨643046454123553452337423937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428697636082368968224949291 643046454123553452337423937)
      ·
        refine ⟨482284840592665089253067953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643046454123553452337423937 482284840592665089253067953)
        ·
          refine ⟨361713630444498816939800965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482284840592665089253067953 361713630444498816939800965)
          ·
            refine ⟨67821305708343528176212681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361713630444498816939800965 67821305708343528176212681)
            ·
              refine ⟨50865979281257646132159511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67821305708343528176212681 50865979281257646132159511)
              ·
                refine ⟨76298968921886469198239267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50865979281257646132159511 76298968921886469198239267)
                ·
                  refine ⟨114448453382829703797358901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76298968921886469198239267 114448453382829703797358901)
                  ·
                    refine ⟨10729542504640284731002397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114448453382829703797358901 10729542504640284731002397)
                    ·
                      refine ⟨4023578439240106774125899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729542504640284731002397 4023578439240106774125899)
                      ·
                        rfl

theorem cell23_7835891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_7835891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835891 prefixEnd_7835891 := by exact prefixLift 7835891
  have htrace : WordTrace (prefixWord ++ tailWord_7835891) baseStart_7835891 baseEnd_7835891 := by
    simpa [prefixWord, tailWord_7835891, baseEnd_7835891] using wordTrace_append hprefix tailTrace_7835891
  have hstable : (prefixWord ++ tailWord_7835891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835891).length < 2 ^ (prefixWord ++ tailWord_7835891).sum := by decide
  have hdescent : baseEnd_7835891 < baseStart_7835891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835921 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_7835921 : Nat := 118140960795 + 7835921 * 2 ^ 59
def prefixEnd_7835921 : Nat := 4983230072969 + 3 ^ 40 * 7835921 * 2
def baseEnd_7835921 : Nat := 4023593843659741656750761

theorem tailTrace_7835921 : CollatzResearch.WordTrace tailWord_7835921 prefixEnd_7835921 4023593843659741656750761 := by
  unfold tailWord_7835921
  simp only [CollatzResearch.WordTrace]
  refine ⟨285799518244803960606891617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190533012163202640404594411 285799518244803960606891617)
  ·
    refine ⟨214349638683602970455168713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285799518244803960606891617 214349638683602970455168713)
    ·
      refine ⟨160762229012702227841376535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214349638683602970455168713 160762229012702227841376535)
      ·
        refine ⟨241143343519053341762064803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160762229012702227841376535 241143343519053341762064803)
        ·
          refine ⟨361715015278580012643097205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241143343519053341762064803 361715015278580012643097205)
          ·
            refine ⟨33910782682366876185290363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361715015278580012643097205 33910782682366876185290363)
            ·
              refine ⟨50866174023550314277935545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33910782682366876185290363 50866174023550314277935545)
              ·
                refine ⟨38149630517662735708451659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50866174023550314277935545 38149630517662735708451659)
                ·
                  refine ⟨57224445776494103562677489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38149630517662735708451659 57224445776494103562677489)
                  ·
                    refine ⟨42918334332370577672008117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57224445776494103562677489 42918334332370577672008117)
                    ·
                      refine ⟨4023593843659741656750761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42918334332370577672008117 4023593843659741656750761)
                      ·
                        rfl

theorem cell23_7835921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_7835921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835921 prefixEnd_7835921 := by exact prefixLift 7835921
  have htrace : WordTrace (prefixWord ++ tailWord_7835921) baseStart_7835921 baseEnd_7835921 := by
    simpa [prefixWord, tailWord_7835921, baseEnd_7835921] using wordTrace_append hprefix tailTrace_7835921
  have hstable : (prefixWord ++ tailWord_7835921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835921).length < 2 ^ (prefixWord ++ tailWord_7835921).sum := by decide
  have hdescent : baseEnd_7835921 < baseStart_7835921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835938 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7835938 : Nat := 118140960795 + 7835938 * 2 ^ 59
def prefixEnd_7835938 : Nat := 4983230072969 + 3 ^ 40 * 7835938 * 2
def baseEnd_7835938 : Nat := 4023602572830868090238183

theorem tailTrace_7835938 : CollatzResearch.WordTrace tailWord_7835938 prefixEnd_7835938 4023602572830868090238183 := by
  unfold tailWord_7835938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71450034571435593127565117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190533425523828248340173645 71450034571435593127565117)
  ·
    refine ⟨26793762964288347422836919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71450034571435593127565117 26793762964288347422836919)
    ·
      refine ⟨40190644446432521134255379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793762964288347422836919 40190644446432521134255379)
      ·
        refine ⟨60285966669648781701383069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40190644446432521134255379 60285966669648781701383069)
        ·
          refine ⟨22607237501118293138018651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60285966669648781701383069 22607237501118293138018651)
          ·
            refine ⟨33910856251677439707027977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22607237501118293138018651 33910856251677439707027977)
            ·
              refine ⟨25433142188758079780270983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33910856251677439707027977 25433142188758079780270983)
              ·
                refine ⟨38149713283137119670406475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433142188758079780270983 38149713283137119670406475)
                ·
                  refine ⟨57224569924705679505609713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38149713283137119670406475 57224569924705679505609713)
                  ·
                    refine ⟨42918427443529259629207285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57224569924705679505609713 42918427443529259629207285)
                    ·
                      refine ⟨4023602572830868090238183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42918427443529259629207285 4023602572830868090238183)
                      ·
                        rfl

theorem cell23_7835938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7835938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835938 prefixEnd_7835938 := by exact prefixLift 7835938
  have htrace : WordTrace (prefixWord ++ tailWord_7835938) baseStart_7835938 baseEnd_7835938 := by
    simpa [prefixWord, tailWord_7835938, baseEnd_7835938] using wordTrace_append hprefix tailTrace_7835938
  have hstable : (prefixWord ++ tailWord_7835938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835938).length < 2 ^ (prefixWord ++ tailWord_7835938).sum := by decide
  have hdescent : baseEnd_7835938 < baseStart_7835938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835948 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_7835948 : Nat := 118140960795 + 7835948 * 2 ^ 59
def prefixEnd_7835948 : Nat := 4983230072969 + 3 ^ 40 * 7835948 * 2
def baseEnd_7835948 : Nat := 4023607707637413051113137

theorem tailTrace_7835948 : CollatzResearch.WordTrace tailWord_7835948 prefixEnd_7835948 4023607707637413051113137 := by
  unfold tailWord_7835948
  simp only [CollatzResearch.WordTrace]
  refine ⟨142900251507853072109062249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190533668677137429478749665 142900251507853072109062249)
  ·
    refine ⟨107175188630889804081796687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142900251507853072109062249 107175188630889804081796687)
    ·
      refine ⟨160762782946334706122695031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107175188630889804081796687 160762782946334706122695031)
      ·
        refine ⟨241144174419502059184042547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160762782946334706122695031 241144174419502059184042547)
        ·
          refine ⟨361716261629253088776063821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241144174419502059184042547 361716261629253088776063821)
          ·
            refine ⟨135643598110969908291023933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361716261629253088776063821 135643598110969908291023933)
            ·
              refine ⟨50866349291613715609133975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135643598110969908291023933 50866349291613715609133975)
              ·
                refine ⟨76299523937420573413700963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50866349291613715609133975 76299523937420573413700963)
                ·
                  refine ⟨114449285906130860120551445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76299523937420573413700963 114449285906130860120551445)
                  ·
                    refine ⟨5364810276849884068150849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114449285906130860120551445 5364810276849884068150849)
                    ·
                      refine ⟨4023607707637413051113137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364810276849884068150849 4023607707637413051113137)
                      ·
                        rfl

theorem cell23_7835948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_7835948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835948 prefixEnd_7835948 := by exact prefixLift 7835948
  have htrace : WordTrace (prefixWord ++ tailWord_7835948) baseStart_7835948 baseEnd_7835948 := by
    simpa [prefixWord, tailWord_7835948, baseEnd_7835948] using wordTrace_append hprefix tailTrace_7835948
  have hstable : (prefixWord ++ tailWord_7835948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835948).length < 2 ^ (prefixWord ++ tailWord_7835948).sum := by decide
  have hdescent : baseEnd_7835948 < baseStart_7835948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835968 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_7835968 : Nat := 118140960795 + 7835968 * 2 ^ 59
def prefixEnd_7835968 : Nat := 4983230072969 + 3 ^ 40 * 7835968 * 2
def baseEnd_7835968 : Nat := 4023617977250502972863045

theorem tailTrace_7835968 : CollatzResearch.WordTrace tailWord_7835968 prefixEnd_7835968 4023617977250502972863045 := by
  unfold tailWord_7835968
  simp only [CollatzResearch.WordTrace]
  refine ⟨142900616237816843816926279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190534154983755791755901705 142900616237816843816926279)
  ·
    refine ⟨214350924356725265725389419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142900616237816843816926279 214350924356725265725389419)
    ·
      refine ⟨321526386535087898588084129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214350924356725265725389419 321526386535087898588084129)
      ·
        refine ⟨241144789901315923941063097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321526386535087898588084129 241144789901315923941063097)
        ·
          refine ⟨180858592425986942955797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241144789901315923941063097 180858592425986942955797323)
          ·
            refine ⟨271287888638980414433695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180858592425986942955797323 271287888638980414433695985)
            ·
              refine ⟨203465916479235310825271989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271287888638980414433695985 203465916479235310825271989)
              ·
                refine ⟨19074929669928310389869249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203465916479235310825271989 19074929669928310389869249)
                ·
                  refine ⟨14306197252446232792401937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19074929669928310389869249 14306197252446232792401937)
                  ·
                    refine ⟨10729647939334674594301453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14306197252446232792401937 10729647939334674594301453)
                    ·
                      refine ⟨4023617977250502972863045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729647939334674594301453 4023617977250502972863045)
                      ·
                        rfl

theorem cell23_7835968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_7835968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835968 prefixEnd_7835968 := by exact prefixLift 7835968
  have htrace : WordTrace (prefixWord ++ tailWord_7835968) baseStart_7835968 baseEnd_7835968 := by
    simpa [prefixWord, tailWord_7835968, baseEnd_7835968] using wordTrace_append hprefix tailTrace_7835968
  have hstable : (prefixWord ++ tailWord_7835968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835968).length < 2 ^ (prefixWord ++ tailWord_7835968).sum := by decide
  have hdescent : baseEnd_7835968 < baseStart_7835968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835988 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 8]
def baseStart_7835988 : Nat := 118140960795 + 7835988 * 2 ^ 59
def prefixEnd_7835988 : Nat := 4983230072969 + 3 ^ 40 * 7835988 * 2
def baseEnd_7835988 : Nat := 447069805207065877179217

theorem tailTrace_7835988 : CollatzResearch.WordTrace tailWord_7835988 prefixEnd_7835988 447069805207065877179217 := by
  unfold tailWord_7835988
  simp only [CollatzResearch.WordTrace]
  refine ⟨142900980967780615524790309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190534641290374154033053745 142900980967780615524790309)
  ·
    refine ⟨26793933931458865410898183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142900980967780615524790309 26793933931458865410898183)
    ·
      refine ⟨40190900897188298116347275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793933931458865410898183 40190900897188298116347275)
      ·
        refine ⟨60286351345782447174520913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40190900897188298116347275 60286351345782447174520913)
        ·
          refine ⟨45214763509336835380890685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60286351345782447174520913 45214763509336835380890685)
          ·
            refine ⟨16955536316001313267834007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45214763509336835380890685 16955536316001313267834007)
            ·
              refine ⟨25433304474001969901751011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955536316001313267834007 25433304474001969901751011)
              ·
                refine ⟨38149956711002954852626517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433304474001969901751011 38149956711002954852626517)
                ·
                  refine ⟨447069805207065877179217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38149956711002954852626517 447069805207065877179217)
                  ·
                    rfl

theorem cell23_7835988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_7835988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835988 prefixEnd_7835988 := by exact prefixLift 7835988
  have htrace : WordTrace (prefixWord ++ tailWord_7835988) baseStart_7835988 baseEnd_7835988 := by
    simpa [prefixWord, tailWord_7835988, baseEnd_7835988] using wordTrace_append hprefix tailTrace_7835988
  have hstable : (prefixWord ++ tailWord_7835988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835988).length < 2 ^ (prefixWord ++ tailWord_7835988).sum := by decide
  have hdescent : baseEnd_7835988 < baseStart_7835988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7835991 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_7835991 : Nat := 118140960795 + 7835991 * 2 ^ 59
def prefixEnd_7835991 : Nat := 4983230072969 + 3 ^ 40 * 7835991 * 2
def baseEnd_7835991 : Nat := 4023629787305556382875439

theorem tailTrace_7835991 : CollatzResearch.WordTrace tailWord_7835991 prefixEnd_7835991 4023629787305556382875439 := by
  unfold tailWord_7835991
  simp only [CollatzResearch.WordTrace]
  refine ⟨285802071354550362561939827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190534714236366908374626551 285802071354550362561939827)
  ·
    refine ⟨428703107031825543842909741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285802071354550362561939827 428703107031825543842909741)
    ·
      refine ⟨160763665136934578941091153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428703107031825543842909741 160763665136934578941091153)
      ·
        refine ⟨120572748852700934205818365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160763665136934578941091153 120572748852700934205818365)
        ·
          refine ⟨45214780819762850327181887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120572748852700934205818365 45214780819762850327181887)
          ·
            refine ⟨67822171229644275490772831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45214780819762850327181887 67822171229644275490772831)
            ·
              refine ⟨101733256844466413236159247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67822171229644275490772831 101733256844466413236159247)
              ·
                refine ⟨152599885266699619854238871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101733256844466413236159247 152599885266699619854238871)
                ·
                  refine ⟨228899827900049429781358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152599885266699619854238871 228899827900049429781358307)
                  ·
                    refine ⟨343349741850074144672037461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228899827900049429781358307 343349741850074144672037461)
                    ·
                      refine ⟨4023629787305556382875439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343349741850074144672037461 4023629787305556382875439)
                      ·
                        rfl

theorem cell23_7835991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_7835991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7835991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7835991 prefixEnd_7835991 := by exact prefixLift 7835991
  have htrace : WordTrace (prefixWord ++ tailWord_7835991) baseStart_7835991 baseEnd_7835991 := by
    simpa [prefixWord, tailWord_7835991, baseEnd_7835991] using wordTrace_append hprefix tailTrace_7835991
  have hstable : (prefixWord ++ tailWord_7835991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7835991).length < 2 ^ (prefixWord ++ tailWord_7835991).sum := by decide
  have hdescent : baseEnd_7835991 < baseStart_7835991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7835991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836005 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 6]
def baseStart_7836005 : Nat := 118140960795 + 7836005 * 2 ^ 59
def prefixEnd_7836005 : Nat := 4983230072969 + 3 ^ 40 * 7836005 * 2
def baseEnd_7836005 : Nat := 447070775114968814233375

theorem tailTrace_7836005 : CollatzResearch.WordTrace tailWord_7836005 prefixEnd_7836005 447070775114968814233375 := by
  unfold tailWord_7836005
  simp only [CollatzResearch.WordTrace]
  refine ⟨285802581976499642952949469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190535054650999761968632979 285802581976499642952949469)
  ·
    refine ⟨107175968241187366107356051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285802581976499642952949469 107175968241187366107356051)
    ·
      refine ⟨160763952361781049161034077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107175968241187366107356051 160763952361781049161034077)
      ·
        refine ⟨60286482135667893435387779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160763952361781049161034077 60286482135667893435387779)
        ·
          refine ⟨90429723203501840153081669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60286482135667893435387779 90429723203501840153081669)
          ·
            refine ⟨16955573100656595028702813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90429723203501840153081669 16955573100656595028702813)
            ·
              refine ⟨6358339912746223135763555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16955573100656595028702813 6358339912746223135763555)
              ·
                refine ⟨9537509869119334703645333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358339912746223135763555 9537509869119334703645333)
                ·
                  refine ⟨447070775114968814233375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9537509869119334703645333 447070775114968814233375)
                  ·
                    rfl

theorem cell23_7836005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_7836005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836005 prefixEnd_7836005 := by exact prefixLift 7836005
  have htrace : WordTrace (prefixWord ++ tailWord_7836005) baseStart_7836005 baseEnd_7836005 := by
    simpa [prefixWord, tailWord_7836005, baseEnd_7836005] using wordTrace_append hprefix tailTrace_7836005
  have hstable : (prefixWord ++ tailWord_7836005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836005).length < 2 ^ (prefixWord ++ tailWord_7836005).sum := by decide
  have hdescent : baseEnd_7836005 < baseStart_7836005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836025 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 2, 3, 2]
def baseStart_7836025 : Nat := 118140960795 + 7836025 * 2 ^ 59
def prefixEnd_7836025 : Nat := 4983230072969 + 3 ^ 40 * 7836025 * 2
def baseEnd_7836025 : Nat := 4023647245647809249850283

theorem tailTrace_7836025 : CollatzResearch.WordTrace tailWord_7836025 prefixEnd_7836025 4023647245647809249850283 := by
  unfold tailWord_7836025
  simp only [CollatzResearch.WordTrace]
  refine ⟨285803311436427186368677529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190535540957618124245785019 285803311436427186368677529)
  ·
    refine ⟨214352483577320389776508147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285803311436427186368677529 214352483577320389776508147)
    ·
      refine ⟨321528725365980584664762221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214352483577320389776508147 321528725365980584664762221)
      ·
        refine ⟨120573272012242719249285833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321528725365980584664762221 120573272012242719249285833)
        ·
          refine ⟨90429954009182039436964375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120573272012242719249285833 90429954009182039436964375)
          ·
            refine ⟨135644931013773059155446563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90429954009182039436964375 135644931013773059155446563)
            ·
              refine ⟨203467396520659588733169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135644931013773059155446563 203467396520659588733169845)
              ·
                refine ⟨19075068423811836443734673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203467396520659588733169845 19075068423811836443734673)
                ·
                  refine ⟨14306301317858877332801005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19075068423811836443734673 14306301317858877332801005)
                  ·
                    refine ⟨5364862994197078999800377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14306301317858877332801005 5364862994197078999800377)
                    ·
                      refine ⟨4023647245647809249850283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5364862994197078999800377 4023647245647809249850283)
                      ·
                        rfl

theorem cell23_7836025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_7836025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836025 prefixEnd_7836025 := by exact prefixLift 7836025
  have htrace : WordTrace (prefixWord ++ tailWord_7836025) baseStart_7836025 baseEnd_7836025 := by
    simpa [prefixWord, tailWord_7836025, baseEnd_7836025] using wordTrace_append hprefix tailTrace_7836025
  have hstable : (prefixWord ++ tailWord_7836025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836025).length < 2 ^ (prefixWord ++ tailWord_7836025).sum := by decide
  have hdescent : baseEnd_7836025 < baseStart_7836025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836068 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7836068 : Nat := 118140960795 + 7836068 * 2 ^ 59
def prefixEnd_7836068 : Nat := 4983230072969 + 3 ^ 40 * 7836068 * 2
def baseEnd_7836068 : Nat := 4023669325315952581612585

theorem tailTrace_7836068 : CollatzResearch.WordTrace tailWord_7836068 prefixEnd_7836068 4023669325315952581612585 := by
  unfold tailWord_7836068
  simp only [CollatzResearch.WordTrace]
  refine ⟨142902439887635702356246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190536586516847603141661905 142902439887635702356246429)
  ·
    refine ⟨53588414957863388383592411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142902439887635702356246429 53588414957863388383592411)
    ·
      refine ⟨80382622436795082575388617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53588414957863388383592411 80382622436795082575388617)
      ·
        refine ⟨60286966827596311931541463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80382622436795082575388617 60286966827596311931541463)
        ·
          refine ⟨90430450241394467897312195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60286966827596311931541463 90430450241394467897312195)
          ·
            refine ⟨135645675362091701845968293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90430450241394467897312195 135645675362091701845968293)
            ·
              refine ⟨25433564130392194096119055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135645675362091701845968293 25433564130392194096119055)
              ·
                refine ⟨38150346195588291144178583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433564130392194096119055 38150346195588291144178583)
                ·
                  refine ⟨57225519293382436716267875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38150346195588291144178583 57225519293382436716267875)
                  ·
                    refine ⟨85838278940073655074401813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57225519293382436716267875 85838278940073655074401813)
                    ·
                      refine ⟨4023669325315952581612585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85838278940073655074401813 4023669325315952581612585)
                      ·
                        rfl

theorem cell23_7836068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7836068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836068 prefixEnd_7836068 := by exact prefixLift 7836068
  have htrace : WordTrace (prefixWord ++ tailWord_7836068) baseStart_7836068 baseEnd_7836068 := by
    simpa [prefixWord, tailWord_7836068, baseEnd_7836068] using wordTrace_append hprefix tailTrace_7836068
  have hstable : (prefixWord ++ tailWord_7836068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836068).length < 2 ^ (prefixWord ++ tailWord_7836068).sum := by decide
  have hdescent : baseEnd_7836068 < baseStart_7836068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836072 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7836072 : Nat := 118140960795 + 7836072 * 2 ^ 59
def prefixEnd_7836072 : Nat := 4983230072969 + 3 ^ 40 * 7836072 * 2
def baseEnd_7836072 : Nat := 4023671379238570565962567

theorem tailTrace_7836072 : CollatzResearch.WordTrace tailWord_7836072 prefixEnd_7836072 4023671379238570565962567 := by
  unfold tailWord_7836072
  simp only [CollatzResearch.WordTrace]
  refine ⟨142902512833628456697819235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190536683778171275597092313 142902512833628456697819235)
  ·
    refine ⟨214353769250442685046728853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142902512833628456697819235 214353769250442685046728853)
    ·
      refine ⟨10047832933614500861565415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 214353769250442685046728853 10047832933614500861565415)
      ·
        refine ⟨15071749400421751292348123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047832933614500861565415 15071749400421751292348123)
        ·
          refine ⟨22607624100632626938522185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071749400421751292348123 22607624100632626938522185)
          ·
            refine ⟨16955718075474470203891639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22607624100632626938522185 16955718075474470203891639)
            ·
              refine ⟨25433577113211705305837459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955718075474470203891639 25433577113211705305837459)
              ·
                refine ⟨38150365669817557958756189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433577113211705305837459 38150365669817557958756189)
                ·
                  refine ⟨14306387126181584234533571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38150365669817557958756189 14306387126181584234533571)
                  ·
                    refine ⟨21459580689272376351800357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14306387126181584234533571 21459580689272376351800357)
                    ·
                      refine ⟨4023671379238570565962567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21459580689272376351800357 4023671379238570565962567)
                      ·
                        rfl

theorem cell23_7836072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7836072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836072 prefixEnd_7836072 := by exact prefixLift 7836072
  have htrace : WordTrace (prefixWord ++ tailWord_7836072) baseStart_7836072 baseEnd_7836072 := by
    simpa [prefixWord, tailWord_7836072, baseEnd_7836072] using wordTrace_append hprefix tailTrace_7836072
  have hstable : (prefixWord ++ tailWord_7836072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836072).length < 2 ^ (prefixWord ++ tailWord_7836072).sum := by decide
  have hdescent : baseEnd_7836072 < baseStart_7836072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836092 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7836092 : Nat := 118140960795 + 7836092 * 2 ^ 59
def prefixEnd_7836092 : Nat := 4983230072969 + 3 ^ 40 * 7836092 * 2
def baseEnd_7836092 : Nat := 4023681648851660487712475

theorem tailTrace_7836092 : CollatzResearch.WordTrace tailWord_7836092 prefixEnd_7836092 4023681648851660487712475 := by
  unfold tailWord_7836092
  simp only [CollatzResearch.WordTrace]
  refine ⟨142902877563592228405683265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190537170084789637874244353 142902877563592228405683265)
  ·
    refine ⟨107177158172694171304262449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142902877563592228405683265 107177158172694171304262449)
    ·
      refine ⟨80382868629520628478196837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107177158172694171304262449 80382868629520628478196837)
      ·
        refine ⟨15071787868035117839661907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80382868629520628478196837 15071787868035117839661907)
        ·
          refine ⟨22607681802052676759492861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071787868035117839661907 22607681802052676759492861)
          ·
            refine ⟨8477880675769753784809823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22607681802052676759492861 8477880675769753784809823)
            ·
              refine ⟨12716821013654630677214735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477880675769753784809823 12716821013654630677214735)
              ·
                refine ⟨19075231520481946015822103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716821013654630677214735 19075231520481946015822103)
                ·
                  refine ⟨28612847280722919023733155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19075231520481946015822103 28612847280722919023733155)
                  ·
                    refine ⟨42919270921084378535599733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28612847280722919023733155 42919270921084378535599733)
                    ·
                      refine ⟨4023681648851660487712475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42919270921084378535599733 4023681648851660487712475)
                      ·
                        rfl

theorem cell23_7836092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7836092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836092 prefixEnd_7836092 := by exact prefixLift 7836092
  have htrace : WordTrace (prefixWord ++ tailWord_7836092) baseStart_7836092 baseEnd_7836092 := by
    simpa [prefixWord, tailWord_7836092, baseEnd_7836092] using wordTrace_append hprefix tailTrace_7836092
  have hstable : (prefixWord ++ tailWord_7836092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836092).length < 2 ^ (prefixWord ++ tailWord_7836092).sum := by decide
  have hdescent : baseEnd_7836092 < baseStart_7836092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836100 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7836100 : Nat := 118140960795 + 7836100 * 2 ^ 59
def prefixEnd_7836100 : Nat := 4983230072969 + 3 ^ 40 * 7836100 * 2
def baseEnd_7836100 : Nat := 4023685756696896456412439

theorem tailTrace_7836100 : CollatzResearch.WordTrace tailWord_7836100 prefixEnd_7836100 4023685756696896456412439 := by
  unfold tailWord_7836100
  simp only [CollatzResearch.WordTrace]
  refine ⟨142903023455577737088828877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190537364607436982785105169 142903023455577737088828877)
  ·
    refine ⟨53588633795841651408310829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142903023455577737088828877 53588633795841651408310829)
    ·
      refine ⟨20095737673440619278116561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53588633795841651408310829 20095737673440619278116561)
      ·
        refine ⟨15071803255080464458587421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20095737673440619278116561 15071803255080464458587421)
        ·
          refine ⟨5651926220655174171970283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15071803255080464458587421 5651926220655174171970283)
          ·
            refine ⟨8477889330982761257955425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651926220655174171970283 8477889330982761257955425)
            ·
              refine ⟨6358416998237070943466569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477889330982761257955425 6358416998237070943466569)
              ·
                refine ⟨4768812748677803207599927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358416998237070943466569 4768812748677803207599927)
                ·
                  refine ⟨7153219123016704811399891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768812748677803207599927 7153219123016704811399891)
                  ·
                    refine ⟨10729828684525057217099837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7153219123016704811399891 10729828684525057217099837)
                    ·
                      refine ⟨4023685756696896456412439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729828684525057217099837 4023685756696896456412439)
                      ·
                        rfl

theorem cell23_7836100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7836100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836100 prefixEnd_7836100 := by exact prefixLift 7836100
  have htrace : WordTrace (prefixWord ++ tailWord_7836100) baseStart_7836100 baseEnd_7836100 := by
    simpa [prefixWord, tailWord_7836100, baseEnd_7836100] using wordTrace_append hprefix tailTrace_7836100
  have hstable : (prefixWord ++ tailWord_7836100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836100).length < 2 ^ (prefixWord ++ tailWord_7836100).sum := by decide
  have hdescent : baseEnd_7836100 < baseStart_7836100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836105 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_7836105 : Nat := 118140960795 + 7836105 * 2 ^ 59
def prefixEnd_7836105 : Nat := 4983230072969 + 3 ^ 40 * 7836105 * 2
def baseEnd_7836105 : Nat := 4023688324100168936849915

theorem tailTrace_7836105 : CollatzResearch.WordTrace tailWord_7836105 prefixEnd_7836105 4023688324100168936849915 := by
  unfold tailWord_7836105
  simp only [CollatzResearch.WordTrace]
  refine ⟨285806229276137360031589769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190537486184091573354393179 285806229276137360031589769)
  ·
    refine ⟨214354671957103020023692327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285806229276137360031589769 214354671957103020023692327)
    ·
      refine ⟨321532007935654530035538491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214354671957103020023692327 321532007935654530035538491)
      ·
        refine ⟨482298011903481795053307737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321532007935654530035538491 482298011903481795053307737)
        ·
          refine ⟨361723508927611346289980803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482298011903481795053307737 361723508927611346289980803)
          ·
            refine ⟨542585263391417019434971205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361723508927611346289980803 542585263391417019434971205)
            ·
              refine ⟨101734736885890691144057101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542585263391417019434971205 101734736885890691144057101)
              ·
                refine ⟨38150526332209009179021413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101734736885890691144057101 38150526332209009179021413)
                ·
                  refine ⟨7153223687289189221066515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38150526332209009179021413 7153223687289189221066515)
                  ·
                    refine ⟨10729835530933783831599773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7153223687289189221066515 10729835530933783831599773)
                    ·
                      refine ⟨4023688324100168936849915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729835530933783831599773 4023688324100168936849915)
                      ·
                        rfl

theorem cell23_7836105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_7836105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836105 prefixEnd_7836105 := by exact prefixLift 7836105
  have htrace : WordTrace (prefixWord ++ tailWord_7836105) baseStart_7836105 baseEnd_7836105 := by
    simpa [prefixWord, tailWord_7836105, baseEnd_7836105] using wordTrace_append hprefix tailTrace_7836105
  have hstable : (prefixWord ++ tailWord_7836105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836105).length < 2 ^ (prefixWord ++ tailWord_7836105).sum := by decide
  have hdescent : baseEnd_7836105 < baseStart_7836105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836122 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_7836122 : Nat := 118140960795 + 7836122 * 2 ^ 59
def prefixEnd_7836122 : Nat := 4983230072969 + 3 ^ 40 * 7836122 * 2
def baseEnd_7836122 : Nat := 4023697053271295370337337

theorem tailTrace_7836122 : CollatzResearch.WordTrace tailWord_7836122 prefixEnd_7836122 4023697053271295370337337 := by
  unfold tailWord_7836122
  simp only [CollatzResearch.WordTrace]
  refine ⟨71451712329268942983739655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190537899544717181289972413 71451712329268942983739655)
  ·
    refine ⟨107177568493903414475609483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71451712329268942983739655 107177568493903414475609483)
    ·
      refine ⟨160766352740855121713414225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107177568493903414475609483 160766352740855121713414225)
      ·
        refine ⟨120574764555641341285060669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160766352740855121713414225 120574764555641341285060669)
        ·
          refine ⟨45215536708365502981897751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120574764555641341285060669 45215536708365502981897751)
          ·
            refine ⟨67823305062548254472846627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45215536708365502981897751 67823305062548254472846627)
            ·
              refine ⟨101734957593822381709269941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67823305062548254472846627 101734957593822381709269941)
              ·
                refine ⟨9537652274420848285244057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101734957593822381709269941 9537652274420848285244057)
                ·
                  refine ⟨7153239205815636213933043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537652274420848285244057 7153239205815636213933043)
                  ·
                    refine ⟨10729858808723454320899565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7153239205815636213933043 10729858808723454320899565)
                    ·
                      refine ⟨4023697053271295370337337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10729858808723454320899565 4023697053271295370337337)
                      ·
                        rfl

theorem cell23_7836122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_7836122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836122 prefixEnd_7836122 := by exact prefixLift 7836122
  have htrace : WordTrace (prefixWord ++ tailWord_7836122) baseStart_7836122 baseEnd_7836122 := by
    simpa [prefixWord, tailWord_7836122, baseEnd_7836122] using wordTrace_append hprefix tailTrace_7836122
  have hstable : (prefixWord ++ tailWord_7836122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836122).length < 2 ^ (prefixWord ++ tailWord_7836122).sum := by decide
  have hdescent : baseEnd_7836122 < baseStart_7836122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
