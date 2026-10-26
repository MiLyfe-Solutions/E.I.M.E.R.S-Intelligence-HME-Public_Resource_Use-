import V185TrunkScan22Chunk155

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1393571 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 3, 3]
def baseStart_1393571 : Nat := 118140960795 + 1393571 * 2 ^ 59
def prefixEnd_1393571 : Nat := 4983230072969 + 3 ^ 40 * 1393571 * 2
def baseEnd_1393571 : Nat := 477047832777914920502393

theorem tailTrace_1393571 : CollatzResearch.WordTrace tailWord_1393571 prefixEnd_1393571 477047832777914920502393 := by
  unfold tailWord_1393571
  simp only [CollatzResearch.WordTrace]
  refine ⟨50827710034337744823524567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33885140022891829882349711 50827710034337744823524567)
  ·
    refine ⟨76241565051506617235286851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50827710034337744823524567 76241565051506617235286851)
    ·
      refine ⟨114362347577259925852930277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76241565051506617235286851 114362347577259925852930277)
      ·
        refine ⟨21442940170736236097424427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114362347577259925852930277 21442940170736236097424427)
        ·
          refine ⟨32164410256104354146136641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21442940170736236097424427 32164410256104354146136641)
          ·
            refine ⟨24123307692078265609602481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32164410256104354146136641 24123307692078265609602481)
            ·
              refine ⟨18092480769058699207201861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24123307692078265609602481 18092480769058699207201861)
              ·
                refine ⟨3392340144198506101350349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18092480769058699207201861 3392340144198506101350349)
                ·
                  refine ⟨1272127554074439788006381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3392340144198506101350349 1272127554074439788006381)
                  ·
                    refine ⟨477047832777914920502393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272127554074439788006381 477047832777914920502393)
                    ·
                      rfl

theorem cell22_1393571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 3].length) (baseStart_1393571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393571 prefixEnd_1393571 := by exact prefixLift 1393571
  have htrace : WordTrace (prefixWord ++ tailWord_1393571) baseStart_1393571 baseEnd_1393571 := by
    simpa [prefixWord, tailWord_1393571, baseEnd_1393571] using wordTrace_append hprefix tailTrace_1393571
  have hstable : (prefixWord ++ tailWord_1393571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393571).length < 2 ^ (prefixWord ++ tailWord_1393571).sum := by decide
  have hdescent : baseEnd_1393571 < baseStart_1393571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393590 : List Nat := [5, 1, 4, 1, 1, 10]
def baseStart_1393590 : Nat := 118140960795 + 1393590 * 2 ^ 59
def prefixEnd_1393590 : Nat := 4983230072969 + 3 ^ 40 * 1393590 * 2
def baseEnd_1393590 : Nat := 5889559714397595114535

theorem tailTrace_1393590 : CollatzResearch.WordTrace tailWord_1393590 prefixEnd_1393590 5889559714397595114535 := by
  unfold tailWord_1393590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176775188829306941779139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33885602014179274045644149 3176775188829306941779139)
  ·
    refine ⟨4765162783243960412668709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3176775188829306941779139 4765162783243960412668709)
    ·
      refine ⟨893468021858242577375383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4765162783243960412668709 893468021858242577375383)
      ·
        refine ⟨1340202032787363866063075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893468021858242577375383 1340202032787363866063075)
        ·
          refine ⟨2010303049181045799094613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340202032787363866063075 2010303049181045799094613)
          ·
            refine ⟨5889559714397595114535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2010303049181045799094613 5889559714397595114535)
            ·
              rfl

theorem cell22_1393590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 10].length) (baseStart_1393590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393590 prefixEnd_1393590 := by exact prefixLift 1393590
  have htrace : WordTrace (prefixWord ++ tailWord_1393590) baseStart_1393590 baseEnd_1393590 := by
    simpa [prefixWord, tailWord_1393590, baseEnd_1393590] using wordTrace_append hprefix tailTrace_1393590
  have hstable : (prefixWord ++ tailWord_1393590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393590).length < 2 ^ (prefixWord ++ tailWord_1393590).sum := by decide
  have hdescent : baseEnd_1393590 < baseStart_1393590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393618 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1393618 : Nat := 118140960795 + 1393618 * 2 ^ 59
def prefixEnd_1393618 : Nat := 4983230072969 + 3 ^ 40 * 1393618 * 2
def baseEnd_1393618 : Nat := 159021307279474154859083

theorem tailTrace_1393618 : CollatzResearch.WordTrace tailWord_1393618 prefixEnd_1393618 159021307279474154859083 := by
  unfold tailWord_1393618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707356066291867962621377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33886282843444981233657005 12707356066291867962621377)
  ·
    refine ⟨9530517049718900971966033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12707356066291867962621377 9530517049718900971966033)
    ·
      refine ⟨7147887787289175728974525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9530517049718900971966033 7147887787289175728974525)
      ·
        refine ⟨2680457920233440898365447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7147887787289175728974525 2680457920233440898365447)
        ·
          refine ⟨4020686880350161347548171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680457920233440898365447 4020686880350161347548171)
          ·
            refine ⟨6031030320525242021322257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020686880350161347548171 6031030320525242021322257)
            ·
              refine ⟨4523272740393931515991693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6031030320525242021322257 4523272740393931515991693)
              ·
                refine ⟨1696227277647724318496885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4523272740393931515991693 1696227277647724318496885)
                ·
                  refine ⟨159021307279474154859083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1696227277647724318496885 159021307279474154859083)
                  ·
                    rfl

theorem cell22_1393618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1393618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393618 prefixEnd_1393618 := by exact prefixLift 1393618
  have htrace : WordTrace (prefixWord ++ tailWord_1393618) baseStart_1393618 baseEnd_1393618 := by
    simpa [prefixWord, tailWord_1393618, baseEnd_1393618] using wordTrace_append hprefix tailTrace_1393618
  have hstable : (prefixWord ++ tailWord_1393618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393618).length < 2 ^ (prefixWord ++ tailWord_1393618).sum := by decide
  have hdescent : baseEnd_1393618 < baseStart_1393618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393676 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1393676 : Nat := 118140960795 + 1393676 * 2 ^ 59
def prefixEnd_1393676 : Nat := 4983230072969 + 3 ^ 40 * 1393676 * 2
def baseEnd_1393676 : Nat := 477083776423729646627071

theorem tailTrace_1393676 : CollatzResearch.WordTrace tailWord_1393676 prefixEnd_1393676 477083776423729646627071 := by
  unfold tailWord_1393676
  simp only [CollatzResearch.WordTrace]
  refine ⟨25415769849478673878048441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33887693132638231837397921 25415769849478673878048441)
  ·
    refine ⟨19061827387109005408536331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25415769849478673878048441 19061827387109005408536331)
    ·
      refine ⟨28592741080663508112804497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19061827387109005408536331 28592741080663508112804497)
      ·
        refine ⟨21444555810497631084603373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28592741080663508112804497 21444555810497631084603373)
        ·
          refine ⟨8041708428936611656726265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21444555810497631084603373 8041708428936611656726265)
          ·
            refine ⟨6031281321702458742544699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8041708428936611656726265 6031281321702458742544699)
            ·
              refine ⟨9046921982553688113817049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031281321702458742544699 9046921982553688113817049)
              ·
                refine ⟨6785191486915266085362787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9046921982553688113817049 6785191486915266085362787)
                ·
                  refine ⟨10177787230372899128044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6785191486915266085362787 10177787230372899128044181)
                  ·
                    refine ⟨477083776423729646627071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10177787230372899128044181 477083776423729646627071)
                    ·
                      rfl

theorem cell22_1393676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1393676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393676 prefixEnd_1393676 := by exact prefixLift 1393676
  have htrace : WordTrace (prefixWord ++ tailWord_1393676) baseStart_1393676 baseEnd_1393676 := by
    simpa [prefixWord, tailWord_1393676, baseEnd_1393676] using wordTrace_append hprefix tailTrace_1393676
  have hstable : (prefixWord ++ tailWord_1393676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393676).length < 2 ^ (prefixWord ++ tailWord_1393676).sum := by decide
  have hdescent : baseEnd_1393676 < baseStart_1393676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393678 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1393678 : Nat := 118140960795 + 1393678 * 2 ^ 59
def prefixEnd_1393678 : Nat := 4983230072969 + 3 ^ 40 * 1393678 * 2
def baseEnd_1393678 : Nat := 477084461064602308077065

theorem tailTrace_1393678 : CollatzResearch.WordTrace tailWord_1393678 prefixEnd_1393678 477084461064602308077065 := by
  unfold tailWord_1393678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353951580618762762208711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33887741763300068065113125 6353951580618762762208711)
  ·
    refine ⟨9530927370928144143313067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6353951580618762762208711 9530927370928144143313067)
    ·
      refine ⟨14296391056392216214969601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9530927370928144143313067 14296391056392216214969601)
      ·
        refine ⟨10722293292294162161227201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14296391056392216214969601 10722293292294162161227201)
        ·
          refine ⟨8041719969220621620920401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10722293292294162161227201 8041719969220621620920401)
          ·
            refine ⟨6031289976915466215690301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8041719969220621620920401 6031289976915466215690301)
            ·
              refine ⟨2261733741343299830883863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031289976915466215690301 2261733741343299830883863)
              ·
                refine ⟨3392600612014949746325795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261733741343299830883863 3392600612014949746325795)
                ·
                  refine ⟨5088900918022424619488693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392600612014949746325795 5088900918022424619488693)
                  ·
                    refine ⟨477084461064602308077065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5088900918022424619488693 477084461064602308077065)
                    ·
                      rfl

theorem cell22_1393678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1393678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393678 prefixEnd_1393678 := by exact prefixLift 1393678
  have htrace : WordTrace (prefixWord ++ tailWord_1393678) baseStart_1393678 baseEnd_1393678 := by
    simpa [prefixWord, tailWord_1393678, baseEnd_1393678] using wordTrace_append hprefix tailTrace_1393678
  have hstable : (prefixWord ++ tailWord_1393678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393678).length < 2 ^ (prefixWord ++ tailWord_1393678).sum := by decide
  have hdescent : baseEnd_1393678 < baseStart_1393678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393729 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1393729 : Nat := 118140960795 + 1393729 * 2 ^ 59
def prefixEnd_1393729 : Nat := 4983230072969 + 3 ^ 40 * 1393729 * 2
def baseEnd_1393729 : Nat := 477101919406855175051909

theorem tailTrace_1393729 : CollatzResearch.WordTrace tailWord_1393729 prefixEnd_1393729 477101919406855175051909 := by
  unfold tailWord_1393729
  simp only [CollatzResearch.WordTrace]
  refine ⟨50833472767765337807776241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33888981845176891871850827 50833472767765337807776241)
  ·
    refine ⟨38125104575824003355832181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50833472767765337807776241 38125104575824003355832181)
    ·
      refine ⟨3574228553983500314609267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38125104575824003355832181 3574228553983500314609267)
      ·
        refine ⟨5361342830975250471913901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574228553983500314609267 5361342830975250471913901)
        ·
          refine ⟨2010503561615718926967713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5361342830975250471913901 2010503561615718926967713)
          ·
            refine ⟨1507877671211789195225785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010503561615718926967713 1507877671211789195225785)
            ·
              refine ⟨1130908253408841896419339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507877671211789195225785 1130908253408841896419339)
              ·
                refine ⟨1696362380113262844629009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130908253408841896419339 1696362380113262844629009)
                ·
                  refine ⟨1272271785084947133471757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696362380113262844629009 1272271785084947133471757)
                  ·
                    refine ⟨477101919406855175051909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272271785084947133471757 477101919406855175051909)
                    ·
                      rfl

theorem cell22_1393729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1393729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393729 prefixEnd_1393729 := by exact prefixLift 1393729
  have htrace : WordTrace (prefixWord ++ tailWord_1393729) baseStart_1393729 baseEnd_1393729 := by
    simpa [prefixWord, tailWord_1393729, baseEnd_1393729] using wordTrace_append hprefix tailTrace_1393729
  have hstable : (prefixWord ++ tailWord_1393729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393729).length < 2 ^ (prefixWord ++ tailWord_1393729).sum := by decide
  have hdescent : baseEnd_1393729 < baseStart_1393729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393751 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1393751 : Nat := 118140960795 + 1393751 * 2 ^ 59
def prefixEnd_1393751 : Nat := 4983230072969 + 3 ^ 40 * 1393751 * 2
def baseEnd_1393751 : Nat := 477109450456454451001841

theorem tailTrace_1393751 : CollatzResearch.WordTrace tailWord_1393751 prefixEnd_1393751 477109450456454451001841 := by
  unfold tailWord_1393751
  simp only [CollatzResearch.WordTrace]
  refine ⟨50834275173685635565077107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33889516782457090376718071 50834275173685635565077107)
  ·
    refine ⟨76251412760528453347615661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50834275173685635565077107 76251412760528453347615661)
    ·
      refine ⟨28594279785198170005355873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76251412760528453347615661 28594279785198170005355873)
      ·
        refine ⟨21445709838898627504016905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28594279785198170005355873 21445709838898627504016905)
        ·
          refine ⟨16084282379173970628012679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21445709838898627504016905 16084282379173970628012679)
          ·
            refine ⟨24126423568760955942019019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16084282379173970628012679 24126423568760955942019019)
            ·
              refine ⟨36189635353141433913028529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24126423568760955942019019 36189635353141433913028529)
              ·
                refine ⟨27142226514856075434771397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36189635353141433913028529 27142226514856075434771397)
                ·
                  refine ⟨5089167471535514144019637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27142226514856075434771397 5089167471535514144019637)
                  ·
                    refine ⟨477109450456454451001841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5089167471535514144019637 477109450456454451001841)
                    ·
                      rfl

theorem cell22_1393751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1393751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393751 prefixEnd_1393751 := by exact prefixLift 1393751
  have htrace : WordTrace (prefixWord ++ tailWord_1393751) baseStart_1393751 baseEnd_1393751 := by
    simpa [prefixWord, tailWord_1393751, baseEnd_1393751] using wordTrace_append hprefix tailTrace_1393751
  have hstable : (prefixWord ++ tailWord_1393751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393751).length < 2 ^ (prefixWord ++ tailWord_1393751).sum := by decide
  have hdescent : baseEnd_1393751 < baseStart_1393751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393770 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_1393770 : Nat := 118140960795 + 1393770 * 2 ^ 59
def prefixEnd_1393770 : Nat := 4983230072969 + 3 ^ 40 * 1393770 * 2
def baseEnd_1393770 : Nat := 159038651514914911592261

theorem tailTrace_1393770 : CollatzResearch.WordTrace tailWord_1393770 prefixEnd_1393770 159038651514914911592261 := by
  unfold tailWord_1393770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708742040154200452504691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33889978773744534540012509 12708742040154200452504691)
  ·
    refine ⟨19063113060231300678757037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12708742040154200452504691 19063113060231300678757037)
    ·
      refine ⟨7148667397586737754533889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19063113060231300678757037 7148667397586737754533889)
      ·
        refine ⟨5361500548190053315900417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148667397586737754533889 5361500548190053315900417)
        ·
          refine ⟨4021125411142539986925313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361500548190053315900417 4021125411142539986925313)
          ·
            refine ⟨3015844058356904990193985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021125411142539986925313 3015844058356904990193985)
            ·
              refine ⟨2261883043767678742645489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015844058356904990193985 2261883043767678742645489)
              ·
                refine ⟨1696412282825759056984117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261883043767678742645489 1696412282825759056984117)
                ·
                  refine ⟨159038651514914911592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1696412282825759056984117 159038651514914911592261)
                  ·
                    rfl

theorem cell22_1393770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_1393770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393770 prefixEnd_1393770 := by exact prefixLift 1393770
  have htrace : WordTrace (prefixWord ++ tailWord_1393770) baseStart_1393770 baseEnd_1393770 := by
    simpa [prefixWord, tailWord_1393770, baseEnd_1393770] using wordTrace_append hprefix tailTrace_1393770
  have hstable : (prefixWord ++ tailWord_1393770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393770).length < 2 ^ (prefixWord ++ tailWord_1393770).sum := by decide
  have hdescent : baseEnd_1393770 < baseStart_1393770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393774 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1393774 : Nat := 118140960795 + 1393774 * 2 ^ 59
def prefixEnd_1393774 : Nat := 4983230072969 + 3 ^ 40 * 1393774 * 2
def baseEnd_1393774 : Nat := 477117323826490057676771

theorem tailTrace_1393774 : CollatzResearch.WordTrace tailWord_1393774 prefixEnd_1393774 477117323826490057676771 := by
  unfold tailWord_1393774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354389256575288811645547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33890076035068206995442917 6354389256575288811645547)
  ·
    refine ⟨9531583884862933217468321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354389256575288811645547 9531583884862933217468321)
    ·
      refine ⟨7148687913647199913101241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9531583884862933217468321 7148687913647199913101241)
      ·
        refine ⟨5361515935235399934825931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148687913647199913101241 5361515935235399934825931)
        ·
          refine ⟨8042273902853099902238897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361515935235399934825931 8042273902853099902238897)
          ·
            refine ⟨6031705427139824926679173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8042273902853099902238897 6031705427139824926679173)
            ·
              refine ⟨1130944767588717173752345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6031705427139824926679173 1130944767588717173752345)
              ·
                refine ⟨848208575691537880314259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1130944767588717173752345 848208575691537880314259)
                ·
                  refine ⟨1272312863537306820471389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848208575691537880314259 1272312863537306820471389)
                  ·
                    refine ⟨477117323826490057676771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272312863537306820471389 477117323826490057676771)
                    ·
                      rfl

theorem cell22_1393774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1393774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393774 prefixEnd_1393774 := by exact prefixLift 1393774
  have htrace : WordTrace (prefixWord ++ tailWord_1393774) baseStart_1393774 baseEnd_1393774 := by
    simpa [prefixWord, tailWord_1393774, baseEnd_1393774] using wordTrace_append hprefix tailTrace_1393774
  have hstable : (prefixWord ++ tailWord_1393774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393774).length < 2 ^ (prefixWord ++ tailWord_1393774).sum := by decide
  have hdescent : baseEnd_1393774 < baseStart_1393774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393815 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 4]
def baseStart_1393815 : Nat := 118140960795 + 1393815 * 2 ^ 59
def prefixEnd_1393815 : Nat := 4983230072969 + 3 ^ 40 * 1393815 * 2
def baseEnd_1393815 : Nat := 159043786321459872467215

theorem tailTrace_1393815 : CollatzResearch.WordTrace tailWord_1393815 prefixEnd_1393815 159043786321459872467215 := by
  unfold tailWord_1393815
  simp only [CollatzResearch.WordTrace]
  refine ⟨50836609445453774495406899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33891072963635849663604599 50836609445453774495406899)
  ·
    refine ⟨76254914168180661743110349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50836609445453774495406899 76254914168180661743110349)
    ·
      refine ⟨28595592813067748153666381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76254914168180661743110349 28595592813067748153666381)
      ·
        refine ⟨10723347304900405557624893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28595592813067748153666381 10723347304900405557624893)
        ·
          refine ⟨4021255239337652084109335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10723347304900405557624893 4021255239337652084109335)
          ·
            refine ⟨6031882859006478126164003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021255239337652084109335 6031882859006478126164003)
            ·
              refine ⟨9047824288509717189246005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031882859006478126164003 9047824288509717189246005)
              ·
                refine ⟨848233527047785986491813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9047824288509717189246005 848233527047785986491813)
                ·
                  refine ⟨159043786321459872467215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848233527047785986491813 159043786321459872467215)
                  ·
                    rfl

theorem cell22_1393815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 4].length) (baseStart_1393815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393815 prefixEnd_1393815 := by exact prefixLift 1393815
  have htrace : WordTrace (prefixWord ++ tailWord_1393815) baseStart_1393815 baseEnd_1393815 := by
    simpa [prefixWord, tailWord_1393815, baseEnd_1393815] using wordTrace_append hprefix tailTrace_1393815
  have hstable : (prefixWord ++ tailWord_1393815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393815).length < 2 ^ (prefixWord ++ tailWord_1393815).sum := by decide
  have hdescent : baseEnd_1393815 < baseStart_1393815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393847 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 2, 3]
def baseStart_1393847 : Nat := 118140960795 + 1393847 * 2 ^ 59
def prefixEnd_1393847 : Nat := 4983230072969 + 3 ^ 40 * 1393847 * 2
def baseEnd_1393847 : Nat := 477142313218342200601547

theorem tailTrace_1393847 : CollatzResearch.WordTrace tailWord_1393847 prefixEnd_1393847 477142313218342200601547 := by
  unfold tailWord_1393847
  simp only [CollatzResearch.WordTrace]
  refine ⟨50837776581337843960571795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33891851054225229307047863 50837776581337843960571795)
  ·
    refine ⟨76256664872006765940857693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50837776581337843960571795 76256664872006765940857693)
    ·
      refine ⟨28596249327002537227821635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76256664872006765940857693 28596249327002537227821635)
      ·
        refine ⟨42894373990503805841732453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28596249327002537227821635 42894373990503805841732453)
        ·
          refine ⟨8042695123219463595324835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42894373990503805841732453 8042695123219463595324835)
          ·
            refine ⟨12064042684829195392987253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8042695123219463595324835 12064042684829195392987253)
            ·
              refine ⟨1131004001702737068092555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12064042684829195392987253 1131004001702737068092555)
              ·
                refine ⟨1696506002554105602138833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131004001702737068092555 1696506002554105602138833)
                ·
                  refine ⟨1272379501915579201604125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696506002554105602138833 1272379501915579201604125)
                  ·
                    refine ⟨477142313218342200601547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272379501915579201604125 477142313218342200601547)
                    ·
                      rfl

theorem cell22_1393847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_1393847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393847 prefixEnd_1393847 := by exact prefixLift 1393847
  have htrace : WordTrace (prefixWord ++ tailWord_1393847) baseStart_1393847 baseEnd_1393847 := by
    simpa [prefixWord, tailWord_1393847, baseEnd_1393847] using wordTrace_append hprefix tailTrace_1393847
  have hstable : (prefixWord ++ tailWord_1393847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393847).length < 2 ^ (prefixWord ++ tailWord_1393847).sum := by decide
  have hdescent : baseEnd_1393847 < baseStart_1393847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393860 : List Nat := [2, 3, 3, 1, 3, 1, 1, 8]
def baseStart_1393860 : Nat := 118140960795 + 1393860 * 2 ^ 59
def prefixEnd_1393860 : Nat := 4983230072969 + 3 ^ 40 * 1393860 * 2
def baseEnd_1393860 : Nat := 53016307042668277780723

theorem tailTrace_1393860 : CollatzResearch.WordTrace tailWord_1393860 prefixEnd_1393860 53016307042668277780723 := by
  unfold tailWord_1393860
  simp only [CollatzResearch.WordTrace]
  refine ⟨25419125365145373590397517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33892167153527164787196689 25419125365145373590397517)
  ·
    refine ⟨9532172011929515096399069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25419125365145373590397517 9532172011929515096399069)
    ·
      refine ⟨3574564504473568161149651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9532172011929515096399069 3574564504473568161149651)
      ·
        refine ⟨5361846756710352241724477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574564504473568161149651 5361846756710352241724477)
        ·
          refine ⟨2010692533766382090646679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5361846756710352241724477 2010692533766382090646679)
          ·
            refine ⟨3016038800649573135970019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010692533766382090646679 3016038800649573135970019)
            ·
              refine ⟨4524058200974359703955029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016038800649573135970019 4524058200974359703955029)
              ·
                refine ⟨53016307042668277780723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4524058200974359703955029 53016307042668277780723)
                ·
                  rfl

theorem cell22_1393860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_1393860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393860 prefixEnd_1393860 := by exact prefixLift 1393860
  have htrace : WordTrace (prefixWord ++ tailWord_1393860) baseStart_1393860 baseEnd_1393860 := by
    simpa [prefixWord, tailWord_1393860, baseEnd_1393860] using wordTrace_append hprefix tailTrace_1393860
  have hstable : (prefixWord ++ tailWord_1393860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393860).length < 2 ^ (prefixWord ++ tailWord_1393860).sum := by decide
  have hdescent : baseEnd_1393860 < baseStart_1393860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393888 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_1393888 : Nat := 118140960795 + 1393888 * 2 ^ 59
def prefixEnd_1393888 : Nat := 4983230072969 + 3 ^ 40 * 1393888 * 2
def baseEnd_1393888 : Nat := 159052116118743920108807

theorem tailTrace_1393888 : CollatzResearch.WordTrace tailWord_1393888 prefixEnd_1393888 159052116118743920108807 := by
  unfold tailWord_1393888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25419635987094653981407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33892847982792871975209545 25419635987094653981407159)
  ·
    refine ⟨38129453980641980972110739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25419635987094653981407159 38129453980641980972110739)
    ·
      refine ⟨57194180970962971458166109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38129453980641980972110739 57194180970962971458166109)
      ·
        refine ⟨21447817864111114296812291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57194180970962971458166109 21447817864111114296812291)
        ·
          refine ⟨32171726796166671445218437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21447817864111114296812291 32171726796166671445218437)
          ·
            refine ⟨6032198774281250895978457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32171726796166671445218437 6032198774281250895978457)
            ·
              refine ⟨4524149080710938171983843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032198774281250895978457 4524149080710938171983843)
              ·
                refine ⟨6786223621066407257975765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524149080710938171983843 6786223621066407257975765)
                ·
                  refine ⟨159052116118743920108807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6786223621066407257975765 159052116118743920108807)
                  ·
                    rfl

theorem cell22_1393888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_1393888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393888 prefixEnd_1393888 := by exact prefixLift 1393888
  have htrace : WordTrace (prefixWord ++ tailWord_1393888) baseStart_1393888 baseEnd_1393888 := by
    simpa [prefixWord, tailWord_1393888, baseEnd_1393888] using wordTrace_append hprefix tailTrace_1393888
  have hstable : (prefixWord ++ tailWord_1393888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393888).length < 2 ^ (prefixWord ++ tailWord_1393888).sum := by decide
  have hdescent : baseEnd_1393888 < baseStart_1393888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393892 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_1393892 : Nat := 118140960795 + 1393892 * 2 ^ 59
def prefixEnd_1393892 : Nat := 4983230072969 + 3 ^ 40 * 1393892 * 2
def baseEnd_1393892 : Nat := 477157717637977083226409

theorem tailTrace_1393892 : CollatzResearch.WordTrace tailWord_1393892 prefixEnd_1393892 477157717637977083226409 := by
  unfold tailWord_1393892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25419708933087408322979965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33892945244116544430639953 25419708933087408322979965)
  ·
    refine ⟨9532390849907778121117487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25419708933087408322979965 9532390849907778121117487)
    ·
      refine ⟨14298586274861667181676231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9532390849907778121117487 14298586274861667181676231)
      ·
        refine ⟨21447879412292500772514347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298586274861667181676231 21447879412292500772514347)
        ·
          refine ⟨32171819118438751158771521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21447879412292500772514347 32171819118438751158771521)
          ·
            refine ⟨24128864338829063369078641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32171819118438751158771521 24128864338829063369078641)
            ·
              refine ⟨18096648254121797526808981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24128864338829063369078641 18096648254121797526808981)
              ·
                refine ⟨848280386911959259069171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18096648254121797526808981 848280386911959259069171)
                ·
                  refine ⟨1272420580367938888603757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848280386911959259069171 1272420580367938888603757)
                  ·
                    refine ⟨477157717637977083226409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272420580367938888603757 477157717637977083226409)
                    ·
                      rfl

theorem cell22_1393892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_1393892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393892 prefixEnd_1393892 := by exact prefixLift 1393892
  have htrace : WordTrace (prefixWord ++ tailWord_1393892) baseStart_1393892 baseEnd_1393892 := by
    simpa [prefixWord, tailWord_1393892, baseEnd_1393892] using wordTrace_append hprefix tailTrace_1393892
  have hstable : (prefixWord ++ tailWord_1393892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393892).length < 2 ^ (prefixWord ++ tailWord_1393892).sum := by decide
  have hdescent : baseEnd_1393892 < baseStart_1393892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393980 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1393980 : Nat := 118140960795 + 1393980 * 2 ^ 59
def prefixEnd_1393980 : Nat := 4983230072969 + 3 ^ 40 * 1393980 * 2
def baseEnd_1393980 : Nat := 477187841836374187026139

theorem tailTrace_1393980 : CollatzResearch.WordTrace tailWord_1393980 prefixEnd_1393980 477187841836374187026139 := by
  unfold tailWord_1393980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25421313744928003837581697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33895084993237338450108929 25421313744928003837581697)
  ·
    refine ⟨19065985308696002878186273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25421313744928003837581697 19065985308696002878186273)
    ·
      refine ⟨14299488981522002158639705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19065985308696002878186273 14299488981522002158639705)
      ·
        refine ⟨10724616736141501618979779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14299488981522002158639705 10724616736141501618979779)
        ·
          refine ⟨16086925104212252428469669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724616736141501618979779 16086925104212252428469669)
          ·
            refine ⟨3016298457039797330338063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16086925104212252428469669 3016298457039797330338063)
            ·
              refine ⟨4524447685559695995507095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016298457039797330338063 4524447685559695995507095)
              ·
                refine ⟨6786671528339543993260643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524447685559695995507095 6786671528339543993260643)
                ·
                  refine ⟨10180007292509315989890965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786671528339543993260643 10180007292509315989890965)
                  ·
                    refine ⟨477187841836374187026139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10180007292509315989890965 477187841836374187026139)
                    ·
                      rfl

theorem cell22_1393980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1393980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393980 prefixEnd_1393980 := by exact prefixLift 1393980
  have htrace : WordTrace (prefixWord ++ tailWord_1393980) baseStart_1393980 baseEnd_1393980 := by
    simpa [prefixWord, tailWord_1393980, baseEnd_1393980] using wordTrace_append hprefix tailTrace_1393980
  have hstable : (prefixWord ++ tailWord_1393980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393980).length < 2 ^ (prefixWord ++ tailWord_1393980).sum := by decide
  have hdescent : baseEnd_1393980 < baseStart_1393980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393982 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1393982 : Nat := 118140960795 + 1393982 * 2 ^ 59
def prefixEnd_1393982 : Nat := 4983230072969 + 3 ^ 40 * 1393982 * 2
def baseEnd_1393982 : Nat := 477188526477246848476133

theorem tailTrace_1393982 : CollatzResearch.WordTrace tailWord_1393982 prefixEnd_1393982 477188526477246848476133 := by
  unfold tailWord_1393982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355337554481095252092025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33895133623899174677824133 6355337554481095252092025)
  ·
    refine ⟨4766503165860821439069019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6355337554481095252092025 4766503165860821439069019)
    ·
      refine ⟨7149754748791232158603529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766503165860821439069019 7149754748791232158603529)
      ·
        refine ⟨5362316061593424118952647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7149754748791232158603529 5362316061593424118952647)
        ·
          refine ⟨8043474092390136178428971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362316061593424118952647 8043474092390136178428971)
          ·
            refine ⟨12065211138585204267643457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043474092390136178428971 12065211138585204267643457)
            ·
              refine ⟨9048908353938903200732593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12065211138585204267643457 9048908353938903200732593)
              ·
                refine ⟨6786681265454177400549445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9048908353938903200732593 6786681265454177400549445)
                ·
                  refine ⟨1272502737272658262603021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6786681265454177400549445 1272502737272658262603021)
                  ·
                    refine ⟨477188526477246848476133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272502737272658262603021 477188526477246848476133)
                    ·
                      rfl

theorem cell22_1393982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1393982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1393982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1393982 prefixEnd_1393982 := by exact prefixLift 1393982
  have htrace : WordTrace (prefixWord ++ tailWord_1393982) baseStart_1393982 baseEnd_1393982 := by
    simpa [prefixWord, tailWord_1393982, baseEnd_1393982] using wordTrace_append hprefix tailTrace_1393982
  have hstable : (prefixWord ++ tailWord_1393982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393982).length < 2 ^ (prefixWord ++ tailWord_1393982).sum := by decide
  have hdescent : baseEnd_1393982 < baseStart_1393982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394046 : List Nat := [4, 2, 3, 2, 2, 1, 8]
def baseStart_1394046 : Nat := 118140960795 + 1394046 * 2 ^ 59
def prefixEnd_1394046 : Nat := 4983230072969 + 3 ^ 40 * 1394046 * 2
def baseEnd_1394046 : Nat := 17674460555006370921331

theorem tailTrace_1394046 : CollatzResearch.WordTrace tailWord_1394046 prefixEnd_1394046 17674460555006370921331 := by
  unfold tailWord_1394046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355629338452112618383249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33896689805077933964710661 6355629338452112618383249)
  ·
    refine ⟨4766722003839084463787437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6355629338452112618383249 4766722003839084463787437)
    ·
      refine ⟨1787520751439656673920289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4766722003839084463787437 1787520751439656673920289)
      ·
        refine ⟨1340640563579742505440217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787520751439656673920289 1340640563579742505440217)
        ·
          refine ⟨1005480422684806879080163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340640563579742505440217 1005480422684806879080163)
          ·
            refine ⟨1508220634027210318620245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005480422684806879080163 1508220634027210318620245)
            ·
              refine ⟨17674460555006370921331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1508220634027210318620245 17674460555006370921331)
              ·
                rfl

theorem cell22_1394046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 8].length) (baseStart_1394046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394046 prefixEnd_1394046 := by exact prefixLift 1394046
  have htrace : WordTrace (prefixWord ++ tailWord_1394046) baseStart_1394046 baseEnd_1394046 := by
    simpa [prefixWord, tailWord_1394046, baseEnd_1394046] using wordTrace_append hprefix tailTrace_1394046
  have hstable : (prefixWord ++ tailWord_1394046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394046).length < 2 ^ (prefixWord ++ tailWord_1394046).sum := by decide
  have hdescent : baseEnd_1394046 < baseStart_1394046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394087 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1394087 : Nat := 118140960795 + 1394087 * 2 ^ 59
def prefixEnd_1394087 : Nat := 4983230072969 + 3 ^ 40 * 1394087 * 2
def baseEnd_1394087 : Nat := 477224470123061574600811

theorem tailTrace_1394087 : CollatzResearch.WordTrace tailWord_1394087 prefixEnd_1394087 477224470123061574600811 := by
  unfold tailWord_1394087
  simp only [CollatzResearch.WordTrace]
  refine ⟨50846530100468364949308515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33897686733645576632872343 50846530100468364949308515)
  ·
    refine ⟨76269795150702547423962773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50846530100468364949308515 76269795150702547423962773)
    ·
      refine ⟨3575146647689181910498255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76269795150702547423962773 3575146647689181910498255)
      ·
        refine ⟨5362719971533772865747383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575146647689181910498255 5362719971533772865747383)
        ·
          refine ⟨8044079957300659298621075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362719971533772865747383 8044079957300659298621075)
          ·
            refine ⟨12066119935950988947931613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044079957300659298621075 12066119935950988947931613)
            ·
              refine ⟨4524794975981620855474355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12066119935950988947931613 4524794975981620855474355)
              ·
                refine ⟨6787192463972431283211533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524794975981620855474355 6787192463972431283211533)
                ·
                  refine ⟨2545197173989661731204325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6787192463972431283211533 2545197173989661731204325)
                  ·
                    refine ⟨477224470123061574600811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545197173989661731204325 477224470123061574600811)
                    ·
                      rfl

theorem cell22_1394087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1394087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394087 prefixEnd_1394087 := by exact prefixLift 1394087
  have htrace : WordTrace (prefixWord ++ tailWord_1394087) baseStart_1394087 baseEnd_1394087 := by
    simpa [prefixWord, tailWord_1394087, baseEnd_1394087] using wordTrace_append hprefix tailTrace_1394087
  have hstable : (prefixWord ++ tailWord_1394087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394087).length < 2 ^ (prefixWord ++ tailWord_1394087).sum := by decide
  have hdescent : baseEnd_1394087 < baseStart_1394087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394134 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1394134 : Nat := 118140960795 + 1394134 * 2 ^ 59
def prefixEnd_1394134 : Nat := 4983230072969 + 3 ^ 40 * 1394134 * 2
def baseEnd_1394134 : Nat := 477240559183569118675667

theorem tailTrace_1394134 : CollatzResearch.WordTrace tailWord_1394134 prefixEnd_1394134 477240559183569118675667 := by
  unfold tailWord_1394134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178015270706130748516841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33898829554198727984179637 3178015270706130748516841)
  ·
    refine ⟨2383511453029598061387631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3178015270706130748516841 2383511453029598061387631)
    ·
      refine ⟨3575267179544397092081447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383511453029598061387631 3575267179544397092081447)
      ·
        refine ⟨5362900769316595638122171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575267179544397092081447 5362900769316595638122171)
        ·
          refine ⟨8044351153974893457183257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362900769316595638122171 8044351153974893457183257)
          ·
            refine ⟨6033263365481170092887443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044351153974893457183257 6033263365481170092887443)
            ·
              refine ⟨9049895048221755139331165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6033263365481170092887443 9049895048221755139331165)
              ·
                refine ⟨3393710643083158177249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9049895048221755139331165 3393710643083158177249187)
                ·
                  refine ⟨5090565964624737265873781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393710643083158177249187 5090565964624737265873781)
                  ·
                    refine ⟨477240559183569118675667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5090565964624737265873781 477240559183569118675667)
                    ·
                      rfl

theorem cell22_1394134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1394134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394134 prefixEnd_1394134 := by exact prefixLift 1394134
  have htrace : WordTrace (prefixWord ++ tailWord_1394134) baseStart_1394134 baseEnd_1394134 := by
    simpa [prefixWord, tailWord_1394134, baseEnd_1394134] using wordTrace_append hprefix tailTrace_1394134
  have hstable : (prefixWord ++ tailWord_1394134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394134).length < 2 ^ (prefixWord ++ tailWord_1394134).sum := by decide
  have hdescent : baseEnd_1394134 < baseStart_1394134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394149 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1394149 : Nat := 118140960795 + 1394149 * 2 ^ 59
def prefixEnd_1394149 : Nat := 4983230072969 + 3 ^ 40 * 1394149 * 2
def baseEnd_1394149 : Nat := 477245693990114079550621

theorem tailTrace_1394149 : CollatzResearch.WordTrace tailWord_1394149 prefixEnd_1394149 477245693990114079550621 := by
  unfold tailWord_1394149
  simp only [CollatzResearch.WordTrace]
  refine ⟨50848791426243749538065501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33899194284162499692043667 50848791426243749538065501)
  ·
    refine ⟨19068296784841406076774563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50848791426243749538065501 19068296784841406076774563)
    ·
      refine ⟨28602445177262109115161845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19068296784841406076774563 28602445177262109115161845)
      ·
        refine ⟨2681479235368322729546423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28602445177262109115161845 2681479235368322729546423)
        ·
          refine ⟨4022218853052484094319635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681479235368322729546423 4022218853052484094319635)
          ·
            refine ⟨6033328279578726141479453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022218853052484094319635 6033328279578726141479453)
            ·
              refine ⟨2262498104842022303054795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033328279578726141479453 2262498104842022303054795)
              ·
                refine ⟨3393747157263033454582193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262498104842022303054795 3393747157263033454582193)
                ·
                  refine ⟨2545310367947275090936645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3393747157263033454582193 2545310367947275090936645)
                  ·
                    refine ⟨477245693990114079550621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545310367947275090936645 477245693990114079550621)
                    ·
                      rfl

theorem cell22_1394149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1394149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394149 prefixEnd_1394149 := by exact prefixLift 1394149
  have htrace : WordTrace (prefixWord ++ tailWord_1394149) baseStart_1394149 baseEnd_1394149 := by
    simpa [prefixWord, tailWord_1394149, baseEnd_1394149] using wordTrace_append hprefix tailTrace_1394149
  have hstable : (prefixWord ++ tailWord_1394149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394149).length < 2 ^ (prefixWord ++ tailWord_1394149).sum := by decide
  have hdescent : baseEnd_1394149 < baseStart_1394149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394230 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1394230 : Nat := 118140960795 + 1394230 * 2 ^ 59
def prefixEnd_1394230 : Nat := 4983230072969 + 3 ^ 40 * 1394230 * 2
def baseEnd_1394230 : Nat := 477273421945456868275373

theorem tailTrace_1394230 : CollatzResearch.WordTrace tailWord_1394230 prefixEnd_1394230 477273421945456868275373 := by
  unfold tailWord_1394230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178234108684393773235259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33901163825966866914509429 3178234108684393773235259)
  ·
    refine ⟨4767351163026590659852889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3178234108684393773235259 4767351163026590659852889)
    ·
      refine ⟨3575513372269942994889667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4767351163026590659852889 3575513372269942994889667)
      ·
        refine ⟨5363270058404914492334501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575513372269942994889667 5363270058404914492334501)
        ·
          refine ⟨1005613135950921467312719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5363270058404914492334501 1005613135950921467312719)
          ·
            refine ⟨1508419703926382200969079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005613135950921467312719 1508419703926382200969079)
            ·
              refine ⟨2262629555889573301453619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508419703926382200969079 2262629555889573301453619)
              ·
                refine ⟨3393944333834359952180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262629555889573301453619 3393944333834359952180429)
                ·
                  refine ⟨1272729125187884982067661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3393944333834359952180429 1272729125187884982067661)
                  ·
                    refine ⟨477273421945456868275373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272729125187884982067661 477273421945456868275373)
                    ·
                      rfl

theorem cell22_1394230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1394230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394230 prefixEnd_1394230 := by exact prefixLift 1394230
  have htrace : WordTrace (prefixWord ++ tailWord_1394230) baseStart_1394230 baseEnd_1394230 := by
    simpa [prefixWord, tailWord_1394230, baseEnd_1394230] using wordTrace_append hprefix tailTrace_1394230
  have hstable : (prefixWord ++ tailWord_1394230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394230).length < 2 ^ (prefixWord ++ tailWord_1394230).sum := by decide
  have hdescent : baseEnd_1394230 < baseStart_1394230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394282 : List Nat := [3, 1, 3, 2, 1, 12]
def baseStart_1394282 : Nat := 118140960795 + 1394282 * 2 ^ 59
def prefixEnd_1394282 : Nat := 4983230072969 + 3 ^ 40 * 1394282 * 2
def baseEnd_1394282 : Nat := 5892484229730198345373

theorem tailTrace_1394282 : CollatzResearch.WordTrace tailWord_1394282 prefixEnd_1394282 5892484229730198345373 := by
  unfold tailWord_1394282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713410583690478313164275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33902428223174608835104733 12713410583690478313164275)
  ·
    refine ⟨19070115875535717469746413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12713410583690478313164275 19070115875535717469746413)
    ·
      refine ⟨7151293453325894051154905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19070115875535717469746413 7151293453325894051154905)
      ·
        refine ⟨5363470089994420538366179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151293453325894051154905 5363470089994420538366179)
        ·
          refine ⟨8045205134991630807549269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363470089994420538366179 8045205134991630807549269)
          ·
            refine ⟨5892484229730198345373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8045205134991630807549269 5892484229730198345373)
            ·
              rfl

theorem cell22_1394282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 12].length) (baseStart_1394282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394282 prefixEnd_1394282 := by exact prefixLift 1394282
  have htrace : WordTrace (prefixWord ++ tailWord_1394282) baseStart_1394282 baseEnd_1394282 := by
    simpa [prefixWord, tailWord_1394282, baseEnd_1394282] using wordTrace_append hprefix tailTrace_1394282
  have hstable : (prefixWord ++ tailWord_1394282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394282).length < 2 ^ (prefixWord ++ tailWord_1394282).sum := by decide
  have hdescent : baseEnd_1394282 < baseStart_1394282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394288 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_1394288 : Nat := 118140960795 + 1394288 * 2 ^ 59
def prefixEnd_1394288 : Nat := 4983230072969 + 3 ^ 40 * 1394288 * 2
def baseEnd_1394288 : Nat := 159097758843588016775065

theorem tailTrace_1394288 : CollatzResearch.WordTrace tailWord_1394288 prefixEnd_1394288 159097758843588016775065 := by
  unfold tailWord_1394288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25426930586370088138687759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33902574115160117518250345 25426930586370088138687759)
  ·
    refine ⟨38140395879555132208031639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25426930586370088138687759 38140395879555132208031639)
    ·
      refine ⟨57210593819332698312047459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38140395879555132208031639 57210593819332698312047459)
      ·
        refine ⟨85815890728999047468071189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57210593819332698312047459 85815890728999047468071189)
        ·
          refine ⟨4022619877921830350065837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85815890728999047468071189 4022619877921830350065837)
          ·
            refine ⟨1508482454220686381274689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4022619877921830350065837 1508482454220686381274689)
            ·
              refine ⟨1131361840665514785956017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508482454220686381274689 1131361840665514785956017)
              ·
                refine ⟨848521380499136089467013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131361840665514785956017 848521380499136089467013)
                ·
                  refine ⟨159097758843588016775065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848521380499136089467013 159097758843588016775065)
                  ·
                    rfl

theorem cell22_1394288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_1394288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394288 prefixEnd_1394288 := by exact prefixLift 1394288
  have htrace : WordTrace (prefixWord ++ tailWord_1394288) baseStart_1394288 baseEnd_1394288 := by
    simpa [prefixWord, tailWord_1394288, baseEnd_1394288] using wordTrace_append hprefix tailTrace_1394288
  have hstable : (prefixWord ++ tailWord_1394288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394288).length < 2 ^ (prefixWord ++ tailWord_1394288).sum := by decide
  have hdescent : baseEnd_1394288 < baseStart_1394288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394359 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1394359 : Nat := 118140960795 + 1394359 * 2 ^ 59
def prefixEnd_1394359 : Nat := 4983230072969 + 3 ^ 40 * 1394359 * 2
def baseEnd_1394359 : Nat := 477317581281743531799977

theorem tailTrace_1394359 : CollatzResearch.WordTrace tailWord_1394359 prefixEnd_1394359 477317581281743531799977 := by
  unfold tailWord_1394359
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856450755482955403210131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33904300503655303602140087 50856450755482955403210131)
  ·
    refine ⟨76284676133224433104815197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50856450755482955403210131 76284676133224433104815197)
    ·
      refine ⟨28606753549959162414305699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76284676133224433104815197 28606753549959162414305699)
      ·
        refine ⟨42910130324938743621458549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28606753549959162414305699 42910130324938743621458549)
        ·
          refine ⟨4022824717963007214511739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42910130324938743621458549 4022824717963007214511739)
          ·
            refine ⟨6034237076944510821767609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022824717963007214511739 6034237076944510821767609)
            ·
              refine ⟨4525677807708383116325707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6034237076944510821767609 4525677807708383116325707)
              ·
                refine ⟨6788516711562574674488561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525677807708383116325707 6788516711562574674488561)
                ·
                  refine ⟨5091387533671931005866421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788516711562574674488561 5091387533671931005866421)
                  ·
                    refine ⟨477317581281743531799977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5091387533671931005866421 477317581281743531799977)
                    ·
                      rfl

theorem cell22_1394359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1394359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394359 prefixEnd_1394359 := by exact prefixLift 1394359
  have htrace : WordTrace (prefixWord ++ tailWord_1394359) baseStart_1394359 baseEnd_1394359 := by
    simpa [prefixWord, tailWord_1394359, baseEnd_1394359] using wordTrace_append hprefix tailTrace_1394359
  have hstable : (prefixWord ++ tailWord_1394359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394359).length < 2 ^ (prefixWord ++ tailWord_1394359).sum := by decide
  have hdescent : baseEnd_1394359 < baseStart_1394359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394436 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_1394436 : Nat := 118140960795 + 1394436 * 2 ^ 59
def prefixEnd_1394436 : Nat := 4983230072969 + 3 ^ 40 * 1394436 * 2
def baseEnd_1394436 : Nat := 477343939955340997624741

theorem tailTrace_1394436 : CollatzResearch.WordTrace tailWord_1394436 prefixEnd_1394436 477343939955340997624741 := by
  unfold tailWord_1394436
  simp only [CollatzResearch.WordTrace]
  refine ⟨25429629588101998776881581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33906172784135998369175441 25429629588101998776881581)
  ·
    refine ⟨9536111095538249541330593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25429629588101998776881581 9536111095538249541330593)
    ·
      refine ⟨7152083321653687155997945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9536111095538249541330593 7152083321653687155997945)
      ·
        refine ⟨5364062491240265366998459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7152083321653687155997945 5364062491240265366998459)
        ·
          refine ⟨8046093736860398050497689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364062491240265366998459 8046093736860398050497689)
          ·
            refine ⟨6034570302645298537873267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8046093736860398050497689 6034570302645298537873267)
            ·
              refine ⟨9051855453967947806809901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034570302645298537873267 9051855453967947806809901)
              ·
                refine ⟨3394445795237980427553713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9051855453967947806809901 3394445795237980427553713)
                ·
                  refine ⟨2545834346428485320665285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394445795237980427553713 2545834346428485320665285)
                  ·
                    refine ⟨477343939955340997624741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2545834346428485320665285 477343939955340997624741)
                    ·
                      rfl

theorem cell22_1394436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_1394436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394436 prefixEnd_1394436 := by exact prefixLift 1394436
  have htrace : WordTrace (prefixWord ++ tailWord_1394436) baseStart_1394436 baseEnd_1394436 := by
    simpa [prefixWord, tailWord_1394436, baseEnd_1394436] using wordTrace_append hprefix tailTrace_1394436
  have hstable : (prefixWord ++ tailWord_1394436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394436).length < 2 ^ (prefixWord ++ tailWord_1394436).sum := by decide
  have hdescent : baseEnd_1394436 < baseStart_1394436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394464 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_1394464 : Nat := 118140960795 + 1394464 * 2 ^ 59
def prefixEnd_1394464 : Nat := 4983230072969 + 3 ^ 40 * 1394464 * 2
def baseEnd_1394464 : Nat := 477353524927558257924655

theorem tailTrace_1394464 : CollatzResearch.WordTrace tailWord_1394464 prefixEnd_1394464 477353524927558257924655 := by
  unfold tailWord_1394464
  simp only [CollatzResearch.WordTrace]
  refine ⟨25430140210051279167891223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33906853613401705557188297 25430140210051279167891223)
  ·
    refine ⟨38145210315076918751836835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25430140210051279167891223 38145210315076918751836835)
    ·
      refine ⟨57217815472615378127755253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38145210315076918751836835 57217815472615378127755253)
      ·
        refine ⟨5364170200557691699477055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57217815472615378127755253 5364170200557691699477055)
        ·
          refine ⟨8046255300836537549215583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364170200557691699477055 8046255300836537549215583)
          ·
            refine ⟨12069382951254806323823375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046255300836537549215583 12069382951254806323823375)
            ·
              refine ⟨18104074426882209485735063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069382951254806323823375 18104074426882209485735063)
              ·
                refine ⟨27156111640323314228602595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18104074426882209485735063 27156111640323314228602595)
                ·
                  refine ⟨40734167460484971342903893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27156111640323314228602595 40734167460484971342903893)
                  ·
                    refine ⟨477353524927558257924655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40734167460484971342903893 477353524927558257924655)
                    ·
                      rfl

theorem cell22_1394464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_1394464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394464 prefixEnd_1394464 := by exact prefixLift 1394464
  have htrace : WordTrace (prefixWord ++ tailWord_1394464) baseStart_1394464 baseEnd_1394464 := by
    simpa [prefixWord, tailWord_1394464, baseEnd_1394464] using wordTrace_append hprefix tailTrace_1394464
  have hstable : (prefixWord ++ tailWord_1394464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394464).length < 2 ^ (prefixWord ++ tailWord_1394464).sum := by decide
  have hdescent : baseEnd_1394464 < baseStart_1394464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394483 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 3, 3]
def baseStart_1394483 : Nat := 118140960795 + 1394483 * 2 ^ 59
def prefixEnd_1394483 : Nat := 4983230072969 + 3 ^ 40 * 1394483 * 2
def baseEnd_1394483 : Nat := 477360029015848541699597

theorem tailTrace_1394483 : CollatzResearch.WordTrace tailWord_1394483 prefixEnd_1394483 477360029015848541699597 := by
  unfold tailWord_1394483
  simp only [CollatzResearch.WordTrace]
  refine ⟨50860973407033724580724103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33907315604689149720482735 50860973407033724580724103)
  ·
    refine ⟨76291460110550586871086155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50860973407033724580724103 76291460110550586871086155)
    ·
      refine ⟨114437190165825880306629233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76291460110550586871086155 114437190165825880306629233)
      ·
        refine ⟨85827892624369410229971925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114437190165825880306629233 85827892624369410229971925)
        ·
          refine ⟨2011591233383658052264967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85827892624369410229971925 2011591233383658052264967)
          ·
            refine ⟨3017386850075487078397451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011591233383658052264967 3017386850075487078397451)
            ·
              refine ⟨4526080275113230617596177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017386850075487078397451 4526080275113230617596177)
              ·
                refine ⟨3394560206334922963197133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526080275113230617596177 3394560206334922963197133)
                ·
                  refine ⟨1272960077375596111198925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3394560206334922963197133 1272960077375596111198925)
                  ·
                    refine ⟨477360029015848541699597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1272960077375596111198925 477360029015848541699597)
                    ·
                      rfl

theorem cell22_1394483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 3].length) (baseStart_1394483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394483 prefixEnd_1394483 := by exact prefixLift 1394483
  have htrace : WordTrace (prefixWord ++ tailWord_1394483) baseStart_1394483 baseEnd_1394483 := by
    simpa [prefixWord, tailWord_1394483, baseEnd_1394483] using wordTrace_append hprefix tailTrace_1394483
  have hstable : (prefixWord ++ tailWord_1394483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394483).length < 2 ^ (prefixWord ++ tailWord_1394483).sum := by decide
  have hdescent : baseEnd_1394483 < baseStart_1394483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394513 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 5]
def baseStart_1394513 : Nat := 118140960795 + 1394513 * 2 ^ 59
def prefixEnd_1394513 : Nat := 4983230072969 + 3 ^ 40 * 1394513 * 2
def baseEnd_1394513 : Nat := 159123432876312821149835

theorem tailTrace_1394513 : CollatzResearch.WordTrace tailWord_1394513 prefixEnd_1394513 159123432876312821149835 := by
  unfold tailWord_1394513
  simp only [CollatzResearch.WordTrace]
  refine ⟨50862067596925039704316193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33908045064616693136210795 50862067596925039704316193)
  ·
    refine ⟨38146550697693779778237145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50862067596925039704316193 38146550697693779778237145)
    ·
      refine ⟨28609913023270334833677859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38146550697693779778237145 28609913023270334833677859)
      ·
        refine ⟨42914869534905502250516789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28609913023270334833677859 42914869534905502250516789)
        ·
          refine ⟨4023269018897390835985949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42914869534905502250516789 4023269018897390835985949)
          ·
            refine ⟨1508725882086521563494731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4023269018897390835985949 1508725882086521563494731)
            ·
              refine ⟨2263088823129782345242097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508725882086521563494731 2263088823129782345242097)
              ·
                refine ⟨1697316617347336758931573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263088823129782345242097 1697316617347336758931573)
                ·
                  refine ⟨159123432876312821149835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697316617347336758931573 159123432876312821149835)
                  ·
                    rfl

theorem cell22_1394513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_1394513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394513 prefixEnd_1394513 := by exact prefixLift 1394513
  have htrace : WordTrace (prefixWord ++ tailWord_1394513) baseStart_1394513 baseEnd_1394513 := by
    simpa [prefixWord, tailWord_1394513, baseEnd_1394513] using wordTrace_append hprefix tailTrace_1394513
  have hstable : (prefixWord ++ tailWord_1394513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394513).length < 2 ^ (prefixWord ++ tailWord_1394513).sum := by decide
  have hdescent : baseEnd_1394513 < baseStart_1394513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394530 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1394530 : Nat := 118140960795 + 1394530 * 2 ^ 59
def prefixEnd_1394530 : Nat := 4983230072969 + 3 ^ 40 * 1394530 * 2
def baseEnd_1394530 : Nat := 159125372692118695258151

theorem tailTrace_1394530 : CollatzResearch.WordTrace tailWord_1394530 prefixEnd_1394530 159125372692118695258151 := by
  unfold tailWord_1394530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715671909465862901921261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33908458425242301071790029 12715671909465862901921261)
  ·
    refine ⟨4768376966049698588220473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12715671909465862901921261 4768376966049698588220473)
    ·
      refine ⟨3576282724537273941165355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4768376966049698588220473 3576282724537273941165355)
      ·
        refine ⟨5364424086805910911748033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576282724537273941165355 5364424086805910911748033)
        ·
          refine ⟨4023318065104433183811025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364424086805910911748033 4023318065104433183811025)
          ·
            refine ⟨3017488548828324887858269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023318065104433183811025 3017488548828324887858269)
            ·
              refine ⟨1131558205810621832946851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3017488548828324887858269 1131558205810621832946851)
              ·
                refine ⟨1697337308715932749420277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131558205810621832946851 1697337308715932749420277)
                ·
                  refine ⟨159125372692118695258151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697337308715932749420277 159125372692118695258151)
                  ·
                    rfl

theorem cell22_1394530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1394530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394530 prefixEnd_1394530 := by exact prefixLift 1394530
  have htrace : WordTrace (prefixWord ++ tailWord_1394530) baseStart_1394530 baseEnd_1394530 := by
    simpa [prefixWord, tailWord_1394530, baseEnd_1394530] using wordTrace_append hprefix tailTrace_1394530
  have hstable : (prefixWord ++ tailWord_1394530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394530).length < 2 ^ (prefixWord ++ tailWord_1394530).sum := by decide
  have hdescent : baseEnd_1394530 < baseStart_1394530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394541 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1394541 : Nat := 118140960795 + 1394541 * 2 ^ 59
def prefixEnd_1394541 : Nat := 4983230072969 + 3 ^ 40 * 1394541 * 2
def baseEnd_1394541 : Nat := 159126627867051907916473

theorem tailTrace_1394541 : CollatzResearch.WordTrace tailWord_1394541 prefixEnd_1394541 159126627867051907916473 := by
  unfold tailWord_1394541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50863088840823600486335477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33908725893882400324223651 50863088840823600486335477)
  ·
    refine ⟨4768414578827212545593951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50863088840823600486335477 4768414578827212545593951)
    ·
      refine ⟨7152621868240818818390927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4768414578827212545593951 7152621868240818818390927)
      ·
        refine ⟨10728932802361228227586391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7152621868240818818390927 10728932802361228227586391)
        ·
          refine ⟨16093399203541842341379587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10728932802361228227586391 16093399203541842341379587)
          ·
            refine ⟨24140098805312763512069381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16093399203541842341379587 24140098805312763512069381)
            ·
              refine ⟨4526268525996143158513009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24140098805312763512069381 4526268525996143158513009)
              ·
                refine ⟨3394701394497107368884757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526268525996143158513009 3394701394497107368884757)
                ·
                  refine ⟨159126627867051907916473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3394701394497107368884757 159126627867051907916473)
                  ·
                    rfl

theorem cell22_1394541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1394541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394541 prefixEnd_1394541 := by exact prefixLift 1394541
  have htrace : WordTrace (prefixWord ++ tailWord_1394541) baseStart_1394541 baseEnd_1394541 := by
    simpa [prefixWord, tailWord_1394541, baseEnd_1394541] using wordTrace_append hprefix tailTrace_1394541
  have hstable : (prefixWord ++ tailWord_1394541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394541).length < 2 ^ (prefixWord ++ tailWord_1394541).sum := by decide
  have hdescent : baseEnd_1394541 < baseStart_1394541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394586 : List Nat := [3, 1, 1, 4, 2, 1, 1, 9]
def baseStart_1394586 : Nat := 118140960795 + 1394586 * 2 ^ 59
def prefixEnd_1394586 : Nat := 4983230072969 + 3 ^ 40 * 1394586 * 2
def baseEnd_1394586 : Nat := 53043920891198956263809

theorem tailTrace_1394586 : CollatzResearch.WordTrace tailWord_1394586 prefixEnd_1394586 53043920891198956263809 := by
  unfold tailWord_1394586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12716182531415143292930903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33909820083773715447815741 12716182531415143292930903)
  ·
    refine ⟨19074273797122714939396355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12716182531415143292930903 19074273797122714939396355)
    ·
      refine ⟨28611410695684072409094533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19074273797122714939396355 28611410695684072409094533)
      ·
        refine ⟨5364639505440763576705225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28611410695684072409094533 5364639505440763576705225)
        ·
          refine ⟨4023479629080572682528919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364639505440763576705225 4023479629080572682528919)
          ·
            refine ⟨6035219443620859023793379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023479629080572682528919 6035219443620859023793379)
            ·
              refine ⟨9052829165431288535690069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035219443620859023793379 9052829165431288535690069)
              ·
                refine ⟨53043920891198956263809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9052829165431288535690069 53043920891198956263809)
                ·
                  rfl

theorem cell22_1394586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_1394586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394586 prefixEnd_1394586 := by exact prefixLift 1394586
  have htrace : WordTrace (prefixWord ++ tailWord_1394586) baseStart_1394586 baseEnd_1394586 := by
    simpa [prefixWord, tailWord_1394586, baseEnd_1394586] using wordTrace_append hprefix tailTrace_1394586
  have hstable : (prefixWord ++ tailWord_1394586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394586).length < 2 ^ (prefixWord ++ tailWord_1394586).sum := by decide
  have hdescent : baseEnd_1394586 < baseStart_1394586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394635 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 1, 3]
def baseStart_1394635 : Nat := 118140960795 + 1394635 * 2 ^ 59
def prefixEnd_1394635 : Nat := 4983230072969 + 3 ^ 40 * 1394635 * 2
def baseEnd_1394635 : Nat := 477412061722170811899131

theorem tailTrace_1394635 : CollatzResearch.WordTrace tailWord_1394635 prefixEnd_1394635 477412061722170811899131 := by
  unfold tailWord_1394635
  simp only [CollatzResearch.WordTrace]
  refine ⟨50866517302483054540257359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33911011534988703026838239 50866517302483054540257359)
  ·
    refine ⟨76299775953724581810386039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50866517302483054540257359 76299775953724581810386039)
    ·
      refine ⟨114449663930586872715579059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76299775953724581810386039 114449663930586872715579059)
      ·
        refine ⟨171674495895880309073368589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114449663930586872715579059 171674495895880309073368589)
        ·
          refine ⟨64377935960955115902513221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171674495895880309073368589 64377935960955115902513221)
          ·
            refine ⟨12070862992679084231721229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64377935960955115902513221 12070862992679084231721229)
            ·
              refine ⟨4526573622254656586895461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12070862992679084231721229 4526573622254656586895461)
              ·
                refine ⟨848732554172748110042899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4526573622254656586895461 848732554172748110042899)
                ·
                  refine ⟨1273098831259122165064349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848732554172748110042899 1273098831259122165064349)
                  ·
                    refine ⟨477412061722170811899131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273098831259122165064349 477412061722170811899131)
                    ·
                      rfl

theorem cell22_1394635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 3].length) (baseStart_1394635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394635 prefixEnd_1394635 := by exact prefixLift 1394635
  have htrace : WordTrace (prefixWord ++ tailWord_1394635) baseStart_1394635 baseEnd_1394635 := by
    simpa [prefixWord, tailWord_1394635, baseEnd_1394635] using wordTrace_append hprefix tailTrace_1394635
  have hstable : (prefixWord ++ tailWord_1394635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394635).length < 2 ^ (prefixWord ++ tailWord_1394635).sum := by decide
  have hdescent : baseEnd_1394635 < baseStart_1394635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394691 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_1394691 : Nat := 118140960795 + 1394691 * 2 ^ 59
def prefixEnd_1394691 : Nat := 4983230072969 + 3 ^ 40 * 1394691 * 2
def baseEnd_1394691 : Nat := 477431231666605332498959

theorem tailTrace_1394691 : CollatzResearch.WordTrace tailWord_1394691 prefixEnd_1394691 477431231666605332498959 := by
  unfold tailWord_1394691
  simp only [CollatzResearch.WordTrace]
  refine ⟨50868559790280176104295927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33912373193520117402863951 50868559790280176104295927)
  ·
    refine ⟨76302839685420264156443891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50868559790280176104295927 76302839685420264156443891)
    ·
      refine ⟨114454259528130396234665837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76302839685420264156443891 114454259528130396234665837)
      ·
        refine ⟨42920347323048898587999689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114454259528130396234665837 42920347323048898587999689)
        ·
          refine ⟨32190260492286673940999767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42920347323048898587999689 32190260492286673940999767)
          ·
            refine ⟨48285390738430010911499651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32190260492286673940999767 48285390738430010911499651)
            ·
              refine ⟨72428086107645016367249477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48285390738430010911499651 72428086107645016367249477)
              ·
                refine ⟨13580266145183440568859277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72428086107645016367249477 13580266145183440568859277)
                ·
                  refine ⟨5092599804443790213322229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13580266145183440568859277 5092599804443790213322229)
                  ·
                    refine ⟨477431231666605332498959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5092599804443790213322229 477431231666605332498959)
                    ·
                      rfl

theorem cell22_1394691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_1394691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394691 prefixEnd_1394691 := by exact prefixLift 1394691
  have htrace : WordTrace (prefixWord ++ tailWord_1394691) baseStart_1394691 baseEnd_1394691 := by
    simpa [prefixWord, tailWord_1394691, baseEnd_1394691] using wordTrace_append hprefix tailTrace_1394691
  have hstable : (prefixWord ++ tailWord_1394691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394691).length < 2 ^ (prefixWord ++ tailWord_1394691).sum := by decide
  have hdescent : baseEnd_1394691 < baseStart_1394691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394693 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 6]
def baseStart_1394693 : Nat := 118140960795 + 1394693 * 2 ^ 59
def prefixEnd_1394693 : Nat := 4983230072969 + 3 ^ 40 * 1394693 * 2
def baseEnd_1394693 : Nat := 159143972102492664649651

theorem tailTrace_1394693 : CollatzResearch.WordTrace tailWord_1394693 prefixEnd_1394693 159143972102492664649651 := by
  unfold tailWord_1394693
  simp only [CollatzResearch.WordTrace]
  refine ⟨50868632736272930445868733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33912421824181953630579155 50868632736272930445868733)
  ·
    refine ⟨19075737276102348917200775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50868632736272930445868733 19075737276102348917200775)
    ·
      refine ⟨28613605914153523375801163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19075737276102348917200775 28613605914153523375801163)
      ·
        refine ⟨42920408871230285063701745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28613605914153523375801163 42920408871230285063701745)
        ·
          refine ⟨32190306653422713797776309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42920408871230285063701745 32190306653422713797776309)
          ·
            refine ⟨3017841248758379418541529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32190306653422713797776309 3017841248758379418541529)
            ·
              refine ⟨2263380936568784563906147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017841248758379418541529 2263380936568784563906147)
              ·
                refine ⟨3395071404853176845859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263380936568784563906147 3395071404853176845859221)
                ·
                  refine ⟨159143972102492664649651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3395071404853176845859221 159143972102492664649651)
                  ·
                    rfl

theorem cell22_1394693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_1394693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394693 prefixEnd_1394693 := by exact prefixLift 1394693
  have htrace : WordTrace (prefixWord ++ tailWord_1394693) baseStart_1394693 baseEnd_1394693 := by
    simpa [prefixWord, tailWord_1394693, baseEnd_1394693] using wordTrace_append hprefix tailTrace_1394693
  have hstable : (prefixWord ++ tailWord_1394693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394693).length < 2 ^ (prefixWord ++ tailWord_1394693).sum := by decide
  have hdescent : baseEnd_1394693 < baseStart_1394693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394723 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_1394723 : Nat := 118140960795 + 1394723 * 2 ^ 59
def prefixEnd_1394723 : Nat := 4983230072969 + 3 ^ 40 * 1394723 * 2
def baseEnd_1394723 : Nat := 477442185920567915698861

theorem tailTrace_1394723 : CollatzResearch.WordTrace tailWord_1394723 prefixEnd_1394723 477442185920567915698861 := by
  unfold tailWord_1394723
  simp only [CollatzResearch.WordTrace]
  refine ⟨50869726926164245569460823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913151284109497046307215 50869726926164245569460823)
  ·
    refine ⟨76304590389246368354191235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50869726926164245569460823 76304590389246368354191235)
    ·
      refine ⟨114456885583869552531286853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76304590389246368354191235 114456885583869552531286853)
      ·
        refine ⟨21460666046975541099616285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114456885583869552531286853 21460666046975541099616285)
        ·
          refine ⟨8047749767615827912356107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21460666046975541099616285 8047749767615827912356107)
          ·
            refine ⟨12071624651423741868534161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047749767615827912356107 12071624651423741868534161)
            ·
              refine ⟨9053718488567806401400621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12071624651423741868534161 9053718488567806401400621)
              ·
                refine ⟨3395144433212927400525233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9053718488567806401400621 3395144433212927400525233)
                ·
                  refine ⟨2546358324909695550393925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395144433212927400525233 2546358324909695550393925)
                  ·
                    refine ⟨477442185920567915698861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546358324909695550393925 477442185920567915698861)
                    ·
                      rfl

theorem cell22_1394723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_1394723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394723 prefixEnd_1394723 := by exact prefixLift 1394723
  have htrace : WordTrace (prefixWord ++ tailWord_1394723) baseStart_1394723 baseEnd_1394723 := by
    simpa [prefixWord, tailWord_1394723, baseEnd_1394723] using wordTrace_append hprefix tailTrace_1394723
  have hstable : (prefixWord ++ tailWord_1394723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394723).length < 2 ^ (prefixWord ++ tailWord_1394723).sum := by decide
  have hdescent : baseEnd_1394723 < baseStart_1394723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394738 : List Nat := [3, 2, 1, 1, 2, 5, 8]
def baseStart_1394738 : Nat := 118140960795 + 1394738 * 2 ^ 59
def prefixEnd_1394738 : Nat := 4983230072969 + 3 ^ 40 * 1394738 * 2
def baseEnd_1394738 : Nat := 17683234101004180613845

theorem tailTrace_1394738 : CollatzResearch.WordTrace tailWord_1394738 prefixEnd_1394738 17683234101004180613845 := by
  unfold tailWord_1394738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12717568505277475782814217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33913516014073268754171245 12717568505277475782814217)
  ·
    refine ⟨9538176378958106837110663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12717568505277475782814217 9538176378958106837110663)
    ·
      refine ⟨14307264568437160255665995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9538176378958106837110663 14307264568437160255665995)
      ·
        refine ⟨21460896852655740383498993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14307264568437160255665995 21460896852655740383498993)
        ·
          refine ⟨16095672639491805287624245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21460896852655740383498993 16095672639491805287624245)
          ·
            refine ⟨1508969309952356745714773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16095672639491805287624245 1508969309952356745714773)
            ·
              refine ⟨17683234101004180613845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1508969309952356745714773 17683234101004180613845)
              ·
                rfl

theorem cell22_1394738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 8].length) (baseStart_1394738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394738 prefixEnd_1394738 := by exact prefixLift 1394738
  have htrace : WordTrace (prefixWord ++ tailWord_1394738) baseStart_1394738 baseEnd_1394738 := by
    simpa [prefixWord, tailWord_1394738, baseEnd_1394738] using wordTrace_append hprefix tailTrace_1394738
  have hstable : (prefixWord ++ tailWord_1394738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394738).length < 2 ^ (prefixWord ++ tailWord_1394738).sum := by decide
  have hdescent : baseEnd_1394738 < baseStart_1394738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394742 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1394742 : Nat := 118140960795 + 1394742 * 2 ^ 59
def prefixEnd_1394742 : Nat := 4983230072969 + 3 ^ 40 * 1394742 * 2
def baseEnd_1394742 : Nat := 477448690008858199473803

theorem tailTrace_1394742 : CollatzResearch.WordTrace tailWord_1394742 prefixEnd_1394742 477448690008858199473803 := by
  unfold tailWord_1394742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179401244568463238400155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33913613275396941209601653 3179401244568463238400155)
  ·
    refine ⟨4769101866852694857600233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179401244568463238400155 4769101866852694857600233)
    ·
      refine ⟨3576826400139521143200175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4769101866852694857600233 3576826400139521143200175)
      ·
        refine ⟨5365239600209281714800263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576826400139521143200175 5365239600209281714800263)
        ·
          refine ⟨8047859400313922572200395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365239600209281714800263 8047859400313922572200395)
          ·
            refine ⟨12071789100470883858300593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047859400313922572200395 12071789100470883858300593)
            ·
              refine ⟨9053841825353162893725445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12071789100470883858300593 9053841825353162893725445)
              ·
                refine ⟨1697595342253718042573521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9053841825353162893725445 1697595342253718042573521)
                ·
                  refine ⟨1273196506690288531930141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697595342253718042573521 1273196506690288531930141)
                  ·
                    refine ⟨477448690008858199473803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273196506690288531930141 477448690008858199473803)
                    ·
                      rfl

theorem cell22_1394742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1394742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394742 prefixEnd_1394742 := by exact prefixLift 1394742
  have htrace : WordTrace (prefixWord ++ tailWord_1394742) baseStart_1394742 baseEnd_1394742 := by
    simpa [prefixWord, tailWord_1394742, baseEnd_1394742] using wordTrace_append hprefix tailTrace_1394742
  have hstable : (prefixWord ++ tailWord_1394742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394742).length < 2 ^ (prefixWord ++ tailWord_1394742).sum := by decide
  have hdescent : baseEnd_1394742 < baseStart_1394742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394774 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1394774 : Nat := 118140960795 + 1394774 * 2 ^ 59
def prefixEnd_1394774 : Nat := 4983230072969 + 3 ^ 40 * 1394774 * 2
def baseEnd_1394774 : Nat := 477459644262820782673705

theorem tailTrace_1394774 : CollatzResearch.WordTrace tailWord_1394774 prefixEnd_1394774 477459644262820782673705 := by
  unfold tailWord_1394774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179474190561217579972961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33914391365986320853044917 3179474190561217579972961)
  ·
    refine ⟨2384605642920913184979721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3179474190561217579972961 2384605642920913184979721)
    ·
      refine ⟨1788454232190684888734791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384605642920913184979721 1788454232190684888734791)
      ·
        refine ⟨2682681348286027333102187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788454232190684888734791 2682681348286027333102187)
        ·
          refine ⟨4024022022429040999653281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682681348286027333102187 4024022022429040999653281)
          ·
            refine ⟨3018016516821780749739961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024022022429040999653281 3018016516821780749739961)
            ·
              refine ⟨2263512387616335562304971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018016516821780749739961 2263512387616335562304971)
              ·
                refine ⟨3395268581424503343457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263512387616335562304971 3395268581424503343457457)
                ·
                  refine ⟨2546451436068377507593093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395268581424503343457457 2546451436068377507593093)
                  ·
                    refine ⟨477459644262820782673705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546451436068377507593093 477459644262820782673705)
                    ·
                      rfl

theorem cell22_1394774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1394774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394774 prefixEnd_1394774 := by exact prefixLift 1394774
  have htrace : WordTrace (prefixWord ++ tailWord_1394774) baseStart_1394774 baseEnd_1394774 := by
    simpa [prefixWord, tailWord_1394774, baseEnd_1394774] using wordTrace_append hprefix tailTrace_1394774
  have hstable : (prefixWord ++ tailWord_1394774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394774).length < 2 ^ (prefixWord ++ tailWord_1394774).sum := by decide
  have hdescent : baseEnd_1394774 < baseStart_1394774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394800 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_1394800 : Nat := 118140960795 + 1394800 * 2 ^ 59
def prefixEnd_1394800 : Nat := 4983230072969 + 3 ^ 40 * 1394800 * 2
def baseEnd_1394800 : Nat := 159156181531388460507875

theorem tailTrace_1394800 : CollatzResearch.WordTrace tailWord_1394800 prefixEnd_1394800 159156181531388460507875 := by
  unfold tailWord_1394800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25436267673442643860006927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33915023564590191813342569 25436267673442643860006927)
  ·
    refine ⟨38154401510163965790010391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25436267673442643860006927 38154401510163965790010391)
    ·
      refine ⟨57231602265245948685015587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38154401510163965790010391 57231602265245948685015587)
      ·
        refine ⟨85847403397868923027523381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57231602265245948685015587 85847403397868923027523381)
        ·
          refine ⟨8048194068550211533830317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85847403397868923027523381 8048194068550211533830317)
          ·
            refine ⟨3018072775706329325186369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8048194068550211533830317 3018072775706329325186369)
            ·
              refine ⟨2263554581779746993889777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018072775706329325186369 2263554581779746993889777)
              ·
                refine ⟨1697665936334810245417333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263554581779746993889777 1697665936334810245417333)
                ·
                  refine ⟨159156181531388460507875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697665936334810245417333 159156181531388460507875)
                  ·
                    rfl

theorem cell22_1394800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_1394800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394800 prefixEnd_1394800 := by exact prefixLift 1394800
  have htrace : WordTrace (prefixWord ++ tailWord_1394800) baseStart_1394800 baseEnd_1394800 := by
    simpa [prefixWord, tailWord_1394800, baseEnd_1394800] using wordTrace_append hprefix tailTrace_1394800
  have hstable : (prefixWord ++ tailWord_1394800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394800).length < 2 ^ (prefixWord ++ tailWord_1394800).sum := by decide
  have hdescent : baseEnd_1394800 < baseStart_1394800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394843 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_1394843 : Nat := 118140960795 + 1394843 * 2 ^ 59
def prefixEnd_1394843 : Nat := 4983230072969 + 3 ^ 40 * 1394843 * 2
def baseEnd_1394843 : Nat := 477483264372927602698493

theorem tailTrace_1394843 : CollatzResearch.WordTrace tailWord_1394843 prefixEnd_1394843 477483264372927602698493 := by
  unfold tailWord_1394843
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874103685729506063829183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33916069123819670709219455 50874103685729506063829183)
  ·
    refine ⟨76311155528594259095743775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50874103685729506063829183 76311155528594259095743775)
    ·
      refine ⟨114466733292891388643615663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76311155528594259095743775 114466733292891388643615663)
      ·
        refine ⟨171700099939337082965423495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114466733292891388643615663 171700099939337082965423495)
        ·
          refine ⟨257550149909005624448135243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171700099939337082965423495 257550149909005624448135243)
          ·
            refine ⟨386325224863508436672202865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257550149909005624448135243 386325224863508436672202865)
            ·
              refine ⟨289743918647631327504152149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386325224863508436672202865 289743918647631327504152149)
              ·
                refine ⟨3395436546651929619189283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 289743918647631327504152149 3395436546651929619189283)
                ·
                  refine ⟨5093154819977894428783925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395436546651929619189283 5093154819977894428783925)
                  ·
                    refine ⟨477483264372927602698493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5093154819977894428783925 477483264372927602698493)
                    ·
                      rfl

theorem cell22_1394843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_1394843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394843 prefixEnd_1394843 := by exact prefixLift 1394843
  have htrace : WordTrace (prefixWord ++ tailWord_1394843) baseStart_1394843 baseEnd_1394843 := by
    simpa [prefixWord, tailWord_1394843, baseEnd_1394843] using wordTrace_append hprefix tailTrace_1394843
  have hstable : (prefixWord ++ tailWord_1394843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394843).length < 2 ^ (prefixWord ++ tailWord_1394843).sum := by decide
  have hdescent : baseEnd_1394843 < baseStart_1394843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394847 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 1, 4]
def baseStart_1394847 : Nat := 118140960795 + 1394847 * 2 ^ 59
def prefixEnd_1394847 : Nat := 4983230072969 + 3 ^ 40 * 1394847 * 2
def baseEnd_1394847 : Nat := 477484633654672925598481

theorem tailTrace_1394847 : CollatzResearch.WordTrace tailWord_1394847 prefixEnd_1394847 477484633654672925598481 := by
  unfold tailWord_1394847
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874249577715014746974795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33916166385143343164649863 50874249577715014746974795)
  ·
    refine ⟨76311374366572522120462193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50874249577715014746974795 76311374366572522120462193)
    ·
      refine ⟨57233530774929391590346645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76311374366572522120462193 57233530774929391590346645)
      ·
        refine ⟨2682821755074815230797499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57233530774929391590346645 2682821755074815230797499)
        ·
          refine ⟨4024232632612222846196249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682821755074815230797499 4024232632612222846196249)
          ·
            refine ⟨3018174474459167134647187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024232632612222846196249 3018174474459167134647187)
            ·
              refine ⟨4527261711688750701970781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018174474459167134647187 4527261711688750701970781)
              ·
                refine ⟨1697723141883281513239043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4527261711688750701970781 1697723141883281513239043)
                ·
                  refine ⟨2546584712824922269858565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697723141883281513239043 2546584712824922269858565)
                  ·
                    refine ⟨477484633654672925598481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546584712824922269858565 477484633654672925598481)
                    ·
                      rfl

theorem cell22_1394847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_1394847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394847 prefixEnd_1394847 := by exact prefixLift 1394847
  have htrace : WordTrace (prefixWord ++ tailWord_1394847) baseStart_1394847 baseEnd_1394847 := by
    simpa [prefixWord, tailWord_1394847, baseEnd_1394847] using wordTrace_append hprefix tailTrace_1394847
  have hstable : (prefixWord ++ tailWord_1394847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394847).length < 2 ^ (prefixWord ++ tailWord_1394847).sum := by decide
  have hdescent : baseEnd_1394847 < baseStart_1394847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394868 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1394868 : Nat := 118140960795 + 1394868 * 2 ^ 59
def prefixEnd_1394868 : Nat := 4983230072969 + 3 ^ 40 * 1394868 * 2
def baseEnd_1394868 : Nat := 159163940794611956941139

theorem tailTrace_1394868 : CollatzResearch.WordTrace tailWord_1394868 prefixEnd_1394868 159163940794611956941139 := by
  unfold tailWord_1394868
  simp only [CollatzResearch.WordTrace]
  refine ⟨25437507755319467666744629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33916677007092623555659505 25437507755319467666744629)
  ·
    refine ⟨2384766352061200093757309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25437507755319467666744629 2384766352061200093757309)
    ·
      refine ⟨894287382022950035158991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2384766352061200093757309 894287382022950035158991)
      ·
        refine ⟨1341431073034425052738487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894287382022950035158991 1341431073034425052738487)
        ·
          refine ⟨2012146609551637579107731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341431073034425052738487 2012146609551637579107731)
          ·
            refine ⟨3018219914327456368661597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012146609551637579107731 3018219914327456368661597)
            ·
              refine ⟨1131832467872796138248099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018219914327456368661597 1131832467872796138248099)
              ·
                refine ⟨1697748701809194207372149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131832467872796138248099 1697748701809194207372149)
                ·
                  refine ⟨159163940794611956941139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697748701809194207372149 159163940794611956941139)
                  ·
                    rfl

theorem cell22_1394868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1394868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394868 prefixEnd_1394868 := by exact prefixLift 1394868
  have htrace : WordTrace (prefixWord ++ tailWord_1394868) baseStart_1394868 baseEnd_1394868 := by
    simpa [prefixWord, tailWord_1394868, baseEnd_1394868] using wordTrace_append hprefix tailTrace_1394868
  have hstable : (prefixWord ++ tailWord_1394868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394868).length < 2 ^ (prefixWord ++ tailWord_1394868).sum := by decide
  have hdescent : baseEnd_1394868 < baseStart_1394868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394873 : List Nat := [1, 2, 1, 4, 1, 2, 2, 9]
def baseStart_1394873 : Nat := 118140960795 + 1394873 * 2 ^ 59
def prefixEnd_1394873 : Nat := 4983230072969 + 3 ^ 40 * 1394873 * 2
def baseEnd_1394873 : Nat := 53054837109557502716489

theorem tailTrace_1394873 : CollatzResearch.WordTrace tailWord_1394873 prefixEnd_1394873 53054837109557502716489 := by
  unfold tailWord_1394873
  simp only [CollatzResearch.WordTrace]
  refine ⟨50875197875620821187421273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33916798583747214124947515 50875197875620821187421273)
  ·
    refine ⟨38156398406715615890565955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50875197875620821187421273 38156398406715615890565955)
    ·
      refine ⟨57234597610073423835848933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38156398406715615890565955 57234597610073423835848933)
      ·
        refine ⟨10731487051888766969221675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57234597610073423835848933 10731487051888766969221675)
        ·
          refine ⟨16097230577833150453832513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10731487051888766969221675 16097230577833150453832513)
          ·
            refine ⟨12072922933374862840374385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16097230577833150453832513 12072922933374862840374385)
            ·
              refine ⟨9054692200031147130280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12072922933374862840374385 9054692200031147130280789)
              ·
                refine ⟨53054837109557502716489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9054692200031147130280789 53054837109557502716489)
                ·
                  rfl

theorem cell22_1394873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 9].length) (baseStart_1394873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394873 prefixEnd_1394873 := by exact prefixLift 1394873
  have htrace : WordTrace (prefixWord ++ tailWord_1394873) baseStart_1394873 baseEnd_1394873 := by
    simpa [prefixWord, tailWord_1394873, baseEnd_1394873] using wordTrace_append hprefix tailTrace_1394873
  have hstable : (prefixWord ++ tailWord_1394873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394873).length < 2 ^ (prefixWord ++ tailWord_1394873).sum := by decide
  have hdescent : baseEnd_1394873 < baseStart_1394873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394888 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1394888 : Nat := 118140960795 + 1394888 * 2 ^ 59
def prefixEnd_1394888 : Nat := 4983230072969 + 3 ^ 40 * 1394888 * 2
def baseEnd_1394888 : Nat := 477498668792562485323355

theorem tailTrace_1394888 : CollatzResearch.WordTrace tailWord_1394888 prefixEnd_1394888 477498668792562485323355 := by
  unfold tailWord_1394888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25437872485283239374608659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33917163313710985832811545 25437872485283239374608659)
  ·
    refine ⟨38156808727924859061912989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25437872485283239374608659 38156808727924859061912989)
    ·
      refine ⟨14308803272971822148217371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38156808727924859061912989 14308803272971822148217371)
      ·
        refine ⟨21463204909457733222326057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14308803272971822148217371 21463204909457733222326057)
        ·
          refine ⟨16097403682093299916744543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21463204909457733222326057 16097403682093299916744543)
          ·
            refine ⟨24146105523139949875116815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097403682093299916744543 24146105523139949875116815)
            ·
              refine ⟨36219158284709924812675223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24146105523139949875116815 36219158284709924812675223)
              ·
                refine ⟨54328737427064887219012835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36219158284709924812675223 54328737427064887219012835)
                ·
                  refine ⟨81493106140597330828519253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54328737427064887219012835 81493106140597330828519253)
                  ·
                    refine ⟨477498668792562485323355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81493106140597330828519253 477498668792562485323355)
                    ·
                      rfl

theorem cell22_1394888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1394888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394888 prefixEnd_1394888 := by exact prefixLift 1394888
  have htrace : WordTrace (prefixWord ++ tailWord_1394888) baseStart_1394888 baseEnd_1394888 := by
    simpa [prefixWord, tailWord_1394888, baseEnd_1394888] using wordTrace_append hprefix tailTrace_1394888
  have hstable : (prefixWord ++ tailWord_1394888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394888).length < 2 ^ (prefixWord ++ tailWord_1394888).sum := by decide
  have hdescent : baseEnd_1394888 < baseStart_1394888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394903 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1394903 : Nat := 118140960795 + 1394903 * 2 ^ 59
def prefixEnd_1394903 : Nat := 4983230072969 + 3 ^ 40 * 1394903 * 2
def baseEnd_1394903 : Nat := 477503803599107446198309

theorem tailTrace_1394903 : CollatzResearch.WordTrace tailWord_1394903 prefixEnd_1394903 477503803599107446198309 := by
  unfold tailWord_1394903
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876292065512136311013363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33917528043674757540675575 50876292065512136311013363)
  ·
    refine ⟨76314438098268204466520045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50876292065512136311013363 76314438098268204466520045)
    ·
      refine ⟨28617914286850576674945017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76314438098268204466520045 28617914286850576674945017)
      ·
        refine ⟨21463435715137932506208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28617914286850576674945017 21463435715137932506208763)
        ·
          refine ⟨32195153572706898759313145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21463435715137932506208763 32195153572706898759313145)
          ·
            refine ⟨24146365179530174069484859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32195153572706898759313145 24146365179530174069484859)
            ·
              refine ⟨36219547769295261104227289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24146365179530174069484859 36219547769295261104227289)
              ·
                refine ⟨27164660826971445828170467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36219547769295261104227289 27164660826971445828170467)
                ·
                  refine ⟨40746991240457168742255701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27164660826971445828170467 40746991240457168742255701)
                  ·
                    refine ⟨477503803599107446198309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40746991240457168742255701 477503803599107446198309)
                    ·
                      rfl

theorem cell22_1394903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1394903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394903 prefixEnd_1394903 := by exact prefixLift 1394903
  have htrace : WordTrace (prefixWord ++ tailWord_1394903) baseStart_1394903 baseEnd_1394903 := by
    simpa [prefixWord, tailWord_1394903, baseEnd_1394903] using wordTrace_append hprefix tailTrace_1394903
  have hstable : (prefixWord ++ tailWord_1394903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394903).length < 2 ^ (prefixWord ++ tailWord_1394903).sum := by decide
  have hdescent : baseEnd_1394903 < baseStart_1394903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394905 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_1394905 : Nat := 118140960795 + 1394905 * 2 ^ 59
def prefixEnd_1394905 : Nat := 4983230072969 + 3 ^ 40 * 1394905 * 2
def baseEnd_1394905 : Nat := 477504488239980107648303

theorem tailTrace_1394905 : CollatzResearch.WordTrace tailWord_1394905 prefixEnd_1394905 477504488239980107648303 := by
  unfold tailWord_1394905
  simp only [CollatzResearch.WordTrace]
  refine ⟨50876365011504890652586169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33917576674336593768390779 50876365011504890652586169)
  ·
    refine ⟨38157273758628667989439627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50876365011504890652586169 38157273758628667989439627)
    ·
      refine ⟨57235910637943001984159441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38157273758628667989439627 57235910637943001984159441)
      ·
        refine ⟨42926932978457251488119581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57235910637943001984159441 42926932978457251488119581)
        ·
          refine ⟨16097599866921469308044843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42926932978457251488119581 16097599866921469308044843)
          ·
            refine ⟨24146399800382203962067265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097599866921469308044843 24146399800382203962067265)
            ·
              refine ⟨18109799850286652971550449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24146399800382203962067265 18109799850286652971550449)
              ·
                refine ⟨13582349887714989728662837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18109799850286652971550449 13582349887714989728662837)
                ·
                  refine ⟨1273345301973280287062141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13582349887714989728662837 1273345301973280287062141)
                  ·
                    refine ⟨477504488239980107648303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273345301973280287062141 477504488239980107648303)
                    ·
                      rfl

theorem cell22_1394905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_1394905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1394905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1394905 prefixEnd_1394905 := by exact prefixLift 1394905
  have htrace : WordTrace (prefixWord ++ tailWord_1394905) baseStart_1394905 baseEnd_1394905 := by
    simpa [prefixWord, tailWord_1394905, baseEnd_1394905] using wordTrace_append hprefix tailTrace_1394905
  have hstable : (prefixWord ++ tailWord_1394905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394905).length < 2 ^ (prefixWord ++ tailWord_1394905).sum := by decide
  have hdescent : baseEnd_1394905 < baseStart_1394905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395025 : List Nat := [1, 2, 2, 1, 4, 3, 9]
def baseStart_1395025 : Nat := 118140960795 + 1395025 * 2 ^ 59
def prefixEnd_1395025 : Nat := 4983230072969 + 3 ^ 40 * 1395025 * 2
def baseEnd_1395025 : Nat := 17686872840457029431405

theorem tailTrace_1395025 : CollatzResearch.WordTrace tailWord_1395025 prefixEnd_1395025 17686872840457029431405 := by
  unfold tailWord_1395025
  simp only [CollatzResearch.WordTrace]
  refine ⟨50880741771070151146954529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33920494514046767431303019 50880741771070151146954529)
  ·
    refine ⟨38160556328302613360215897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50880741771070151146954529 38160556328302613360215897)
    ·
      refine ⟨28620417246226960020161923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38160556328302613360215897 28620417246226960020161923)
      ·
        refine ⟨42930625869340440030242885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28620417246226960020161923 42930625869340440030242885)
        ·
          refine ⟨8049492350501332505670541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42930625869340440030242885 8049492350501332505670541)
          ·
            refine ⟨3018559631437999689626453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8049492350501332505670541 3018559631437999689626453)
            ·
              refine ⟨17686872840457029431405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3018559631437999689626453 17686872840457029431405)
              ·
                rfl

theorem cell22_1395025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 9].length) (baseStart_1395025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395025 prefixEnd_1395025 := by exact prefixLift 1395025
  have htrace : WordTrace (prefixWord ++ tailWord_1395025) baseStart_1395025 baseEnd_1395025 := by
    simpa [prefixWord, tailWord_1395025, baseEnd_1395025] using wordTrace_append hprefix tailTrace_1395025
  have hstable : (prefixWord ++ tailWord_1395025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395025).length < 2 ^ (prefixWord ++ tailWord_1395025).sum := by decide
  have hdescent : baseEnd_1395025 < baseStart_1395025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395029 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1395029 : Nat := 118140960795 + 1395029 * 2 ^ 59
def prefixEnd_1395029 : Nat := 4983230072969 + 3 ^ 40 * 1395029 * 2
def baseEnd_1395029 : Nat := 477546935974085117547923

theorem tailTrace_1395029 : CollatzResearch.WordTrace tailWord_1395029 prefixEnd_1395029 477546935974085117547923 := by
  unfold tailWord_1395029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50880887663055659830100141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33920591775370439886733427 50880887663055659830100141)
  ·
    refine ⟨19080332873645872436287553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50880887663055659830100141 19080332873645872436287553)
    ·
      refine ⟨14310249655234404327215665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19080332873645872436287553 14310249655234404327215665)
      ·
        refine ⟨10732687241425803245411749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14310249655234404327215665 10732687241425803245411749)
        ·
          refine ⟨2012378857767338108514703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10732687241425803245411749 2012378857767338108514703)
          ·
            refine ⟨3018568286651007162772055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012378857767338108514703 3018568286651007162772055)
            ·
              refine ⟨4527852429976510744158083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018568286651007162772055 4527852429976510744158083)
              ·
                refine ⟨6791778644964766116237125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527852429976510744158083 6791778644964766116237125)
                ·
                  refine ⟨1273458495930893646794461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6791778644964766116237125 1273458495930893646794461)
                  ·
                    refine ⟨477546935974085117547923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273458495930893646794461 477546935974085117547923)
                    ·
                      rfl

theorem cell22_1395029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1395029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395029 prefixEnd_1395029 := by exact prefixLift 1395029
  have htrace : WordTrace (prefixWord ++ tailWord_1395029) baseStart_1395029 baseEnd_1395029 := by
    simpa [prefixWord, tailWord_1395029, baseEnd_1395029] using wordTrace_append hprefix tailTrace_1395029
  have hstable : (prefixWord ++ tailWord_1395029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395029).length < 2 ^ (prefixWord ++ tailWord_1395029).sum := by decide
  have hdescent : baseEnd_1395029 < baseStart_1395029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395104 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_1395104 : Nat := 118140960795 + 1395104 * 2 ^ 59
def prefixEnd_1395104 : Nat := 4983230072969 + 3 ^ 40 * 1395104 * 2
def baseEnd_1395104 : Nat := 159190870002269973974231

theorem tailTrace_1395104 : CollatzResearch.WordTrace tailWord_1395104 prefixEnd_1395104 159190870002269973974231 := by
  unfold tailWord_1395104
  simp only [CollatzResearch.WordTrace]
  refine ⟨25441811568891973819540183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33922415425189298426053577 25441811568891973819540183)
  ·
    refine ⟨38162717353337960729310275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25441811568891973819540183 38162717353337960729310275)
    ·
      refine ⟨57244076030006941093965413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38162717353337960729310275 57244076030006941093965413)
      ·
        refine ⟨10733264255626301455118515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57244076030006941093965413 10733264255626301455118515)
        ·
          refine ⟨16099896383439452182677773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10733264255626301455118515 16099896383439452182677773)
          ·
            refine ⟨6037461143789794568504165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16099896383439452182677773 6037461143789794568504165)
            ·
              refine ⟨1132023964460586481594531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6037461143789794568504165 1132023964460586481594531)
              ·
                refine ⟨1698035946690879722391797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132023964460586481594531 1698035946690879722391797)
                ·
                  refine ⟨159190870002269973974231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698035946690879722391797 159190870002269973974231)
                  ·
                    rfl

theorem cell22_1395104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_1395104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395104 prefixEnd_1395104 := by exact prefixLift 1395104
  have htrace : WordTrace (prefixWord ++ tailWord_1395104) baseStart_1395104 baseEnd_1395104 := by
    simpa [prefixWord, tailWord_1395104, baseEnd_1395104] using wordTrace_append hprefix tailTrace_1395104
  have hstable : (prefixWord ++ tailWord_1395104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395104).length < 2 ^ (prefixWord ++ tailWord_1395104).sum := by decide
  have hdescent : baseEnd_1395104 < baseStart_1395104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395134 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1395134 : Nat := 118140960795 + 1395134 * 2 ^ 59
def prefixEnd_1395134 : Nat := 4983230072969 + 3 ^ 40 * 1395134 * 2
def baseEnd_1395134 : Nat := 477582879619899843672601

theorem tailTrace_1395134 : CollatzResearch.WordTrace tailWord_1395134 prefixEnd_1395134 477582879619899843672601 := by
  unfold tailWord_1395134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360589665959407845334057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33923144885116841841781637 6360589665959407845334057)
  ·
    refine ⟨4770442249469555884000543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6360589665959407845334057 4770442249469555884000543)
    ·
      refine ⟨7155663374204333826000815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770442249469555884000543 7155663374204333826000815)
      ·
        refine ⟨10733495061306500739001223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155663374204333826000815 10733495061306500739001223)
        ·
          refine ⟨16100242591959751108501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10733495061306500739001223 16100242591959751108501835)
          ·
            refine ⟨24150363887939626662752753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16100242591959751108501835 24150363887939626662752753)
            ·
              refine ⟨18112772915954719997064565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24150363887939626662752753 18112772915954719997064565)
              ·
                refine ⟨1698072460870754999724803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18112772915954719997064565 1698072460870754999724803)
                ·
                  refine ⟨2547108691306132499587205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698072460870754999724803 2547108691306132499587205)
                  ·
                    refine ⟨477582879619899843672601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547108691306132499587205 477582879619899843672601)
                    ·
                      rfl

theorem cell22_1395134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1395134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395134 prefixEnd_1395134 := by exact prefixLift 1395134
  have htrace : WordTrace (prefixWord ++ tailWord_1395134) baseStart_1395134 baseEnd_1395134 := by
    simpa [prefixWord, tailWord_1395134, baseEnd_1395134] using wordTrace_append hprefix tailTrace_1395134
  have hstable : (prefixWord ++ tailWord_1395134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395134).length < 2 ^ (prefixWord ++ tailWord_1395134).sum := by decide
  have hdescent : baseEnd_1395134 < baseStart_1395134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395162 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1395162 : Nat := 118140960795 + 1395162 * 2 ^ 59
def prefixEnd_1395162 : Nat := 4983230072969 + 3 ^ 40 * 1395162 * 2
def baseEnd_1395162 : Nat := 477592464592117103972515

theorem tailTrace_1395162 : CollatzResearch.WordTrace tailWord_1395162 prefixEnd_1395162 477592464592117103972515 := by
  unfold tailWord_1395162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721434642893455886172935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33923825714382549029794493 12721434642893455886172935)
  ·
    refine ⟨19082151964340183829259403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12721434642893455886172935 19082151964340183829259403)
    ·
      refine ⟨28623227946510275743889105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19082151964340183829259403 28623227946510275743889105)
      ·
        refine ⟨21467420959882706807916829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28623227946510275743889105 21467420959882706807916829)
        ·
          refine ⟨8050282859956015052968811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21467420959882706807916829 8050282859956015052968811)
          ·
            refine ⟨12075424289934022579453217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050282859956015052968811 12075424289934022579453217)
            ·
              refine ⟨9056568217450516934589913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12075424289934022579453217 9056568217450516934589913)
              ·
                refine ⟨6792426163087887700942435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056568217450516934589913 6792426163087887700942435)
                ·
                  refine ⟨10188639244631831551413653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792426163087887700942435 10188639244631831551413653)
                  ·
                    refine ⟨477592464592117103972515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10188639244631831551413653 477592464592117103972515)
                    ·
                      rfl

theorem cell22_1395162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1395162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395162 prefixEnd_1395162 := by exact prefixLift 1395162
  have htrace : WordTrace (prefixWord ++ tailWord_1395162) baseStart_1395162 baseEnd_1395162 := by
    simpa [prefixWord, tailWord_1395162, baseEnd_1395162] using wordTrace_append hprefix tailTrace_1395162
  have hstable : (prefixWord ++ tailWord_1395162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395162).length < 2 ^ (prefixWord ++ tailWord_1395162).sum := by decide
  have hdescent : baseEnd_1395162 < baseStart_1395162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395237 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1395237 : Nat := 118140960795 + 1395237 * 2 ^ 59
def prefixEnd_1395237 : Nat := 4983230072969 + 3 ^ 40 * 1395237 * 2
def baseEnd_1395237 : Nat := 477618138624841908347285

theorem tailTrace_1395237 : CollatzResearch.WordTrace tailWord_1395237 prefixEnd_1395237 477618138624841908347285 := by
  unfold tailWord_1395237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50888474046302111353671965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33925649364201407569114643 50888474046302111353671965)
  ·
    refine ⟨19083177767363291757626987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50888474046302111353671965 19083177767363291757626987)
    ·
      refine ⟨28624766651044937636440481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083177767363291757626987 28624766651044937636440481)
      ·
        refine ⟨21468574988283703227330361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28624766651044937636440481 21468574988283703227330361)
        ·
          refine ⟨16101431241212777420497771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21468574988283703227330361 16101431241212777420497771)
          ·
            refine ⟨24152146861819166130746657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101431241212777420497771 24152146861819166130746657)
            ·
              refine ⟨18114110146364374598059993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24152146861819166130746657 18114110146364374598059993)
              ·
                refine ⟨13585582609773280948544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18114110146364374598059993 13585582609773280948544995)
                ·
                  refine ⟨20378373914659921422817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13585582609773280948544995 20378373914659921422817493)
                  ·
                    refine ⟨477618138624841908347285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20378373914659921422817493 477618138624841908347285)
                    ·
                      rfl

theorem cell22_1395237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1395237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395237 prefixEnd_1395237 := by exact prefixLift 1395237
  have htrace : WordTrace (prefixWord ++ tailWord_1395237) baseStart_1395237 baseEnd_1395237 := by
    simpa [prefixWord, tailWord_1395237, baseEnd_1395237] using wordTrace_append hprefix tailTrace_1395237
  have hstable : (prefixWord ++ tailWord_1395237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395237).length < 2 ^ (prefixWord ++ tailWord_1395237).sum := by decide
  have hdescent : baseEnd_1395237 < baseStart_1395237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395245 : List Nat := [1, 5, 4, 1, 2, 1, 8]
def baseStart_1395245 : Nat := 118140960795 + 1395245 * 2 ^ 59
def prefixEnd_1395245 : Nat := 4983230072969 + 3 ^ 40 * 1395245 * 2
def baseEnd_1395245 : Nat := 17689662118086390894343

theorem tailTrace_1395245 : CollatzResearch.WordTrace tailWord_1395245 prefixEnd_1395245 17689662118086390894343 := by
  unfold tailWord_1395245
  simp only [CollatzResearch.WordTrace]
  refine ⟨50888765830273128719963189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33925843886848752479975459 50888765830273128719963189)
  ·
    refine ⟨4770821796588105817496549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50888765830273128719963189 4770821796588105817496549)
    ·
      refine ⟨894529086860269840780603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4770821796588105817496549 894529086860269840780603)
      ·
        refine ⟨1341793630290404761170905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894529086860269840780603 1341793630290404761170905)
        ·
          refine ⟨1006345222717803570878179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1341793630290404761170905 1006345222717803570878179)
          ·
            refine ⟨1509517834076705356317269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006345222717803570878179 1509517834076705356317269)
            ·
              refine ⟨17689662118086390894343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1509517834076705356317269 17689662118086390894343)
              ·
                rfl

theorem cell22_1395245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 8].length) (baseStart_1395245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395245 prefixEnd_1395245 := by exact prefixLift 1395245
  have htrace : WordTrace (prefixWord ++ tailWord_1395245) baseStart_1395245 baseEnd_1395245 := by
    simpa [prefixWord, tailWord_1395245, baseEnd_1395245] using wordTrace_append hprefix tailTrace_1395245
  have hstable : (prefixWord ++ tailWord_1395245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395245).length < 2 ^ (prefixWord ++ tailWord_1395245).sum := by decide
  have hdescent : baseEnd_1395245 < baseStart_1395245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395260 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_1395260 : Nat := 118140960795 + 1395260 * 2 ^ 59
def prefixEnd_1395260 : Nat := 4983230072969 + 3 ^ 40 * 1395260 * 2
def baseEnd_1395260 : Nat := 477626011994877515022215

theorem tailTrace_1395260 : CollatzResearch.WordTrace tailWord_1395260 prefixEnd_1395260 477626011994877515022215 := by
  unfold tailWord_1395260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444656462609393140879617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33926208616812524187839489 25444656462609393140879617)
  ·
    refine ⟨19083492346957044855659713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25444656462609393140879617 19083492346957044855659713)
    ·
      refine ⟨14312619260217783641744785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19083492346957044855659713 14312619260217783641744785)
      ·
        refine ⟨10734464445163337731308589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312619260217783641744785 10734464445163337731308589)
        ·
          refine ⟨4025424166936251649240721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10734464445163337731308589 4025424166936251649240721)
          ·
            refine ⟨3019068125202188736930541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025424166936251649240721 3019068125202188736930541)
            ·
              refine ⟨1132150546950820776348953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3019068125202188736930541 1132150546950820776348953)
              ·
                refine ⟨849112910213115582261715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132150546950820776348953 849112910213115582261715)
                ·
                  refine ⟨1273669365319673373392573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849112910213115582261715 1273669365319673373392573)
                  ·
                    refine ⟨477626011994877515022215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273669365319673373392573 477626011994877515022215)
                    ·
                      rfl

theorem cell22_1395260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_1395260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395260 prefixEnd_1395260 := by exact prefixLift 1395260
  have htrace : WordTrace (prefixWord ++ tailWord_1395260) baseStart_1395260 baseEnd_1395260 := by
    simpa [prefixWord, tailWord_1395260, baseEnd_1395260] using wordTrace_append hprefix tailTrace_1395260
  have hstable : (prefixWord ++ tailWord_1395260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395260).length < 2 ^ (prefixWord ++ tailWord_1395260).sum := by decide
  have hdescent : baseEnd_1395260 < baseStart_1395260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395299 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_1395299 : Nat := 118140960795 + 1395299 * 2 ^ 59
def prefixEnd_1395299 : Nat := 4983230072969 + 3 ^ 40 * 1395299 * 2
def baseEnd_1395299 : Nat := 477639362491894413297095

theorem tailTrace_1395299 : CollatzResearch.WordTrace tailWord_1395299 prefixEnd_1395299 477639362491894413297095 := by
  unfold tailWord_1395299
  simp only [CollatzResearch.WordTrace]
  refine ⟨50890735372077495942428951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33927156914718330628285967 50890735372077495942428951)
  ·
    refine ⟨76336103058116243913643427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50890735372077495942428951 76336103058116243913643427)
    ·
      refine ⟨114504154587174365870465141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76336103058116243913643427 114504154587174365870465141)
      ·
        refine ⟨10734764492547596800356107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114504154587174365870465141 10734764492547596800356107)
        ·
          refine ⟨16102146738821395200534161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734764492547596800356107 16102146738821395200534161)
          ·
            refine ⟨12076610054116046400400621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16102146738821395200534161 12076610054116046400400621)
            ·
              refine ⟨4528728770293517400150233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12076610054116046400400621 4528728770293517400150233)
              ·
                refine ⟨3396546577720138050112675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528728770293517400150233 3396546577720138050112675)
                ·
                  refine ⟨5094819866580207075169013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396546577720138050112675 5094819866580207075169013)
                  ·
                    refine ⟨477639362491894413297095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5094819866580207075169013 477639362491894413297095)
                    ·
                      rfl

theorem cell22_1395299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_1395299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395299 prefixEnd_1395299 := by exact prefixLift 1395299
  have htrace : WordTrace (prefixWord ++ tailWord_1395299) baseStart_1395299 baseEnd_1395299 := by
    simpa [prefixWord, tailWord_1395299, baseEnd_1395299] using wordTrace_append hprefix tailTrace_1395299
  have hstable : (prefixWord ++ tailWord_1395299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395299).length < 2 ^ (prefixWord ++ tailWord_1395299).sum := by decide
  have hdescent : baseEnd_1395299 < baseStart_1395299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395312 : List Nat := [2, 1, 1, 1, 17]
def baseStart_1395312 : Nat := 118140960795 + 1395312 * 2 ^ 59
def prefixEnd_1395312 : Nat := 4983230072969 + 3 ^ 40 * 1395312 * 2
def baseEnd_1395312 : Nat := 1965612397767764249885

theorem tailTrace_1395312 : CollatzResearch.WordTrace tailWord_1395312 prefixEnd_1395312 1965612397767764249885 := by
  unfold tailWord_1395312
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445604760515199581326095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33927473014020266108434793 25445604760515199581326095)
  ·
    refine ⟨38168407140772799371989143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25445604760515199581326095 38168407140772799371989143)
    ·
      refine ⟨57252610711159199057983715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38168407140772799371989143 57252610711159199057983715)
      ·
        refine ⟨85878916066738798586975573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57252610711159199057983715 85878916066738798586975573)
        ·
          refine ⟨1965612397767764249885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 85878916066738798586975573 1965612397767764249885)
          ·
            rfl

theorem cell22_1395312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 17].length) (baseStart_1395312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395312 prefixEnd_1395312 := by exact prefixLift 1395312
  have htrace : WordTrace (prefixWord ++ tailWord_1395312) baseStart_1395312 baseEnd_1395312 := by
    simpa [prefixWord, tailWord_1395312, baseEnd_1395312] using wordTrace_append hprefix tailTrace_1395312
  have hstable : (prefixWord ++ tailWord_1395312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395312).length < 2 ^ (prefixWord ++ tailWord_1395312).sum := by decide
  have hdescent : baseEnd_1395312 < baseStart_1395312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395348 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1395348 : Nat := 118140960795 + 1395348 * 2 ^ 59
def prefixEnd_1395348 : Nat := 4983230072969 + 3 ^ 40 * 1395348 * 2
def baseEnd_1395348 : Nat := 477656136193274618821945

theorem tailTrace_1395348 : CollatzResearch.WordTrace tailWord_1395348 prefixEnd_1395348 477656136193274618821945 := by
  unfold tailWord_1395348
  simp only [CollatzResearch.WordTrace]
  refine ⟨25446261274449988655481349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33928348365933318207308465 25446261274449988655481349)
  ·
    refine ⟨4771173988959372872902753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25446261274449988655481349 4771173988959372872902753)
    ·
      refine ⟨3578380491719529654677065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4771173988959372872902753 3578380491719529654677065)
      ·
        refine ⟨2683785368789647241007799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578380491719529654677065 2683785368789647241007799)
        ·
          refine ⟨4025678053184470861511699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683785368789647241007799 4025678053184470861511699)
          ·
            refine ⟨6038517079776706292267549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025678053184470861511699 6038517079776706292267549)
            ·
              refine ⟨2264443904916264859600331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6038517079776706292267549 2264443904916264859600331)
              ·
                refine ⟨3396665857374397289400497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264443904916264859600331 3396665857374397289400497)
                ·
                  refine ⟨2547499393030797967050373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3396665857374397289400497 2547499393030797967050373)
                  ·
                    refine ⟨477656136193274618821945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547499393030797967050373 477656136193274618821945)
                    ·
                      rfl

theorem cell22_1395348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1395348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395348 prefixEnd_1395348 := by exact prefixLift 1395348
  have htrace : WordTrace (prefixWord ++ tailWord_1395348) baseStart_1395348 baseEnd_1395348 := by
    simpa [prefixWord, tailWord_1395348, baseEnd_1395348] using wordTrace_append hprefix tailTrace_1395348
  have hstable : (prefixWord ++ tailWord_1395348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395348).length < 2 ^ (prefixWord ++ tailWord_1395348).sum := by decide
  have hdescent : baseEnd_1395348 < baseStart_1395348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395367 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1395367 : Nat := 118140960795 + 1395367 * 2 ^ 59
def prefixEnd_1395367 : Nat := 4983230072969 + 3 ^ 40 * 1395367 * 2
def baseEnd_1395367 : Nat := 477662640281564902596887

theorem tailTrace_1395367 : CollatzResearch.WordTrace tailWord_1395367 prefixEnd_1395367 477662640281564902596887 := by
  unfold tailWord_1395367
  simp only [CollatzResearch.WordTrace]
  refine ⟨50893215535831143555904355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33928810357220762370602903 50893215535831143555904355)
  ·
    refine ⟨76339823303746715333856533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50893215535831143555904355 76339823303746715333856533)
    ·
      refine ⟨3578429217363127281274525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76339823303746715333856533 3578429217363127281274525)
      ·
        refine ⟨1341910956511172730477947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3578429217363127281274525 1341910956511172730477947)
        ·
          refine ⟨2012866434766759095716921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341910956511172730477947 2012866434766759095716921)
          ·
            refine ⟨1509649826075069321787691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2012866434766759095716921 1509649826075069321787691)
            ·
              refine ⟨2264474739112603982681537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509649826075069321787691 2264474739112603982681537)
              ·
                refine ⟨1698356054334452987011153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264474739112603982681537 1698356054334452987011153)
                ·
                  refine ⟨1273767040750839740258365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698356054334452987011153 1273767040750839740258365)
                  ·
                    refine ⟨477662640281564902596887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273767040750839740258365 477662640281564902596887)
                    ·
                      rfl

theorem cell22_1395367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1395367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395367 prefixEnd_1395367 := by exact prefixLift 1395367
  have htrace : WordTrace (prefixWord ++ tailWord_1395367) baseStart_1395367 baseEnd_1395367 := by
    simpa [prefixWord, tailWord_1395367, baseEnd_1395367] using wordTrace_append hprefix tailTrace_1395367
  have hstable : (prefixWord ++ tailWord_1395367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395367).length < 2 ^ (prefixWord ++ tailWord_1395367).sum := by decide
  have hdescent : baseEnd_1395367 < baseStart_1395367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395449 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_1395449 : Nat := 118140960795 + 1395449 * 2 ^ 59
def prefixEnd_1395449 : Nat := 4983230072969 + 3 ^ 40 * 1395449 * 2
def baseEnd_1395449 : Nat := 477690710557344022046635

theorem tailTrace_1395449 : CollatzResearch.WordTrace tailWord_1395449 prefixEnd_1395449 477690710557344022046635 := by
  unfold tailWord_1395449
  simp only [CollatzResearch.WordTrace]
  refine ⟨50896206321534071560389401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33930804214356047706926267 50896206321534071560389401)
  ·
    refine ⟨38172154741150553670292051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50896206321534071560389401 38172154741150553670292051)
    ·
      refine ⟨57258232111725830505438077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38172154741150553670292051 57258232111725830505438077)
      ·
        refine ⟨21471837041897186439539279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57258232111725830505438077 21471837041897186439539279)
        ·
          refine ⟨32207755562845779659308919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21471837041897186439539279 32207755562845779659308919)
          ·
            refine ⟨48311633344268669488963379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32207755562845779659308919 48311633344268669488963379)
            ·
              refine ⟨72467450016403004233445069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48311633344268669488963379 72467450016403004233445069)
              ·
                refine ⟨27175293756151126587541901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72467450016403004233445069 27175293756151126587541901)
                ·
                  refine ⟨10190735158556672470328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27175293756151126587541901 10190735158556672470328213)
                  ·
                    refine ⟨477690710557344022046635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10190735158556672470328213 477690710557344022046635)
                    ·
                      rfl

theorem cell22_1395449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_1395449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395449 prefixEnd_1395449 := by exact prefixLift 1395449
  have htrace : WordTrace (prefixWord ++ tailWord_1395449) baseStart_1395449 baseEnd_1395449 := by
    simpa [prefixWord, tailWord_1395449, baseEnd_1395449] using wordTrace_append hprefix tailTrace_1395449
  have hstable : (prefixWord ++ tailWord_1395449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395449).length < 2 ^ (prefixWord ++ tailWord_1395449).sum := by decide
  have hdescent : baseEnd_1395449 < baseStart_1395449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395517 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_1395517 : Nat := 118140960795 + 1395517 * 2 ^ 59
def prefixEnd_1395517 : Nat := 4983230072969 + 3 ^ 40 * 1395517 * 2
def baseEnd_1395517 : Nat := 477713988347014511346427

theorem tailTrace_1395517 : CollatzResearch.WordTrace tailWord_1395517 prefixEnd_1395517 477713988347014511346427 := by
  unfold tailWord_1395517
  simp only [CollatzResearch.WordTrace]
  refine ⟨50898686485287719173864805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33932457656858479449243203 50898686485287719173864805)
  ·
    refine ⟨9543503715991447345099651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50898686485287719173864805 9543503715991447345099651)
    ·
      refine ⟨14315255573987171017649477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543503715991447345099651 14315255573987171017649477)
      ·
        refine ⟨2684110420122594565809277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14315255573987171017649477 2684110420122594565809277)
        ·
          refine ⟨1006541407545972962178479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2684110420122594565809277 1006541407545972962178479)
          ·
            refine ⟨1509812111318959443267719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006541407545972962178479 1509812111318959443267719)
            ·
              refine ⟨2264718166978439164901579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509812111318959443267719 2264718166978439164901579)
              ·
                refine ⟨3397077250467658747352369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264718166978439164901579 3397077250467658747352369)
                ·
                  refine ⟨2547807937850744060514277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397077250467658747352369 2547807937850744060514277)
                  ·
                    refine ⟨477713988347014511346427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2547807937850744060514277 477713988347014511346427)
                    ·
                      rfl

theorem cell22_1395517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_1395517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395517 prefixEnd_1395517 := by exact prefixLift 1395517
  have htrace : WordTrace (prefixWord ++ tailWord_1395517) baseStart_1395517 baseEnd_1395517 := by
    simpa [prefixWord, tailWord_1395517, baseEnd_1395517] using wordTrace_append hprefix tailTrace_1395517
  have hstable : (prefixWord ++ tailWord_1395517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395517).length < 2 ^ (prefixWord ++ tailWord_1395517).sum := by decide
  have hdescent : baseEnd_1395517 < baseStart_1395517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395541 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1395541 : Nat := 118140960795 + 1395541 * 2 ^ 59
def prefixEnd_1395541 : Nat := 4983230072969 + 3 ^ 40 * 1395541 * 2
def baseEnd_1395541 : Nat := 477722204037486448746353

theorem tailTrace_1395541 : CollatzResearch.WordTrace tailWord_1395541 prefixEnd_1395541 477722204037486448746353 := by
  unfold tailWord_1395541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899561837200771272738477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33933041224800514181825651 50899561837200771272738477)
  ·
    refine ⟨19087335688950289227276929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50899561837200771272738477 19087335688950289227276929)
    ·
      refine ⟨14315501766712716920457697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19087335688950289227276929 14315501766712716920457697)
      ·
        refine ⟨10736626325034537690343273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14315501766712716920457697 10736626325034537690343273)
        ·
          refine ⟨8052469743775903267757455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10736626325034537690343273 8052469743775903267757455)
          ·
            refine ⟨12078704615663854901636183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052469743775903267757455 12078704615663854901636183)
            ·
              refine ⟨18118056923495782352454275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078704615663854901636183 18118056923495782352454275)
              ·
                refine ⟨27177085385243673528681413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18118056923495782352454275 27177085385243673528681413)
                ·
                  refine ⟨5095703509733188786627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27177085385243673528681413 5095703509733188786627765)
                  ·
                    refine ⟨477722204037486448746353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5095703509733188786627765 477722204037486448746353)
                    ·
                      rfl

theorem cell22_1395541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1395541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395541 prefixEnd_1395541 := by exact prefixLift 1395541
  have htrace : WordTrace (prefixWord ++ tailWord_1395541) baseStart_1395541 baseEnd_1395541 := by
    simpa [prefixWord, tailWord_1395541, baseEnd_1395541] using wordTrace_append hprefix tailTrace_1395541
  have hstable : (prefixWord ++ tailWord_1395541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395541).length < 2 ^ (prefixWord ++ tailWord_1395541).sum := by decide
  have hdescent : baseEnd_1395541 < baseStart_1395541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395543 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 5]
def baseStart_1395543 : Nat := 118140960795 + 1395543 * 2 ^ 59
def prefixEnd_1395543 : Nat := 4983230072969 + 3 ^ 40 * 1395543 * 2
def baseEnd_1395543 : Nat := 159240962892786370065449

theorem tailTrace_1395543 : CollatzResearch.WordTrace tailWord_1395543 prefixEnd_1395543 159240962892786370065449 := by
  unfold tailWord_1395543
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899634783193525614311283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33933089855462350409540855 50899634783193525614311283)
  ·
    refine ⟨76349452174790288421466925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50899634783193525614311283 76349452174790288421466925)
    ·
      refine ⟨28631044565546358158050097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76349452174790288421466925 28631044565546358158050097)
      ·
        refine ⟨21473283424159768618537573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28631044565546358158050097 21473283424159768618537573)
        ·
          refine ⟨4026240642029956615975795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21473283424159768618537573 4026240642029956615975795)
          ·
            refine ⟨6039360963044934923963693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026240642029956615975795 6039360963044934923963693)
            ·
              refine ⟨2264760361141850596486385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6039360963044934923963693 2264760361141850596486385)
              ·
                refine ⟨1698570270856387947364789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264760361141850596486385 1698570270856387947364789)
                ·
                  refine ⟨159240962892786370065449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698570270856387947364789 159240962892786370065449)
                  ·
                    rfl

theorem cell22_1395543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].length) (baseStart_1395543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395543 prefixEnd_1395543 := by exact prefixLift 1395543
  have htrace : WordTrace (prefixWord ++ tailWord_1395543) baseStart_1395543 baseEnd_1395543 := by
    simpa [prefixWord, tailWord_1395543, baseEnd_1395543] using wordTrace_append hprefix tailTrace_1395543
  have hstable : (prefixWord ++ tailWord_1395543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395543).length < 2 ^ (prefixWord ++ tailWord_1395543).sum := by decide
  have hdescent : baseEnd_1395543 < baseStart_1395543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395560 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_1395560 : Nat := 118140960795 + 1395560 * 2 ^ 59
def prefixEnd_1395560 : Nat := 4983230072969 + 3 ^ 40 * 1395560 * 2
def baseEnd_1395560 : Nat := 159242902708592244173765

theorem tailTrace_1395560 : CollatzResearch.WordTrace tailWord_1395560 prefixEnd_1395560 159242902708592244173765 := by
  unfold tailWord_1395560
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450127412065968758840067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33933503216087958345120089 25450127412065968758840067)
  ·
    refine ⟨38175191118098953138260101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25450127412065968758840067 38175191118098953138260101)
    ·
      refine ⟨7157848334643553713423769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38175191118098953138260101 7157848334643553713423769)
      ·
        refine ⟨5368386250982665285067827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7157848334643553713423769 5368386250982665285067827)
        ·
          refine ⟨8052579376473997927601741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368386250982665285067827 8052579376473997927601741)
          ·
            refine ⟨3019717266177749222850653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8052579376473997927601741 3019717266177749222850653)
            ·
              refine ⟨1132393974816655958568995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3019717266177749222850653 1132393974816655958568995)
              ·
                refine ⟨1698590962224983937853493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132393974816655958568995 1698590962224983937853493)
                ·
                  refine ⟨159242902708592244173765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698590962224983937853493 159242902708592244173765)
                  ·
                    rfl

theorem cell22_1395560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_1395560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395560 prefixEnd_1395560 := by exact prefixLift 1395560
  have htrace : WordTrace (prefixWord ++ tailWord_1395560) baseStart_1395560 baseEnd_1395560 := by
    simpa [prefixWord, tailWord_1395560, baseEnd_1395560] using wordTrace_append hprefix tailTrace_1395560
  have hstable : (prefixWord ++ tailWord_1395560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395560).length < 2 ^ (prefixWord ++ tailWord_1395560).sum := by decide
  have hdescent : baseEnd_1395560 < baseStart_1395560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395571 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 6]
def baseStart_1395571 : Nat := 118140960795 + 1395571 * 2 ^ 59
def prefixEnd_1395571 : Nat := 4983230072969 + 3 ^ 40 * 1395571 * 2
def baseEnd_1395571 : Nat := 159244157883525456832087

theorem tailTrace_1395571 : CollatzResearch.WordTrace tailWord_1395571 prefixEnd_1395571 159244157883525456832087 := by
  unfold tailWord_1395571
  simp only [CollatzResearch.WordTrace]
  refine ⟨50900656027092086396330567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33933770684728057597553711 50900656027092086396330567)
  ·
    refine ⟨76350984040638129594495851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50900656027092086396330567 76350984040638129594495851)
    ·
      refine ⟨114526476060957194391743777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76350984040638129594495851 114526476060957194391743777)
      ·
        refine ⟨85894857045717895793807833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114526476060957194391743777 85894857045717895793807833)
        ·
          refine ⟨64421142784288421845355875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85894857045717895793807833 64421142784288421845355875)
          ·
            refine ⟨96631714176432632768033813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64421142784288421845355875 96631714176432632768033813)
            ·
              refine ⟨4529611602020279661001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96631714176432632768033813 4529611602020279661001585)
              ·
                refine ⟨3397208701515209745751189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529611602020279661001585 3397208701515209745751189)
                ·
                  refine ⟨159244157883525456832087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3397208701515209745751189 159244157883525456832087)
                  ·
                    rfl

theorem cell22_1395571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_1395571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395571 prefixEnd_1395571 := by exact prefixLift 1395571
  have htrace : WordTrace (prefixWord ++ tailWord_1395571) baseStart_1395571 baseEnd_1395571 := by
    simpa [prefixWord, tailWord_1395571, baseEnd_1395571] using wordTrace_append hprefix tailTrace_1395571
  have hstable : (prefixWord ++ tailWord_1395571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395571).length < 2 ^ (prefixWord ++ tailWord_1395571).sum := by decide
  have hdescent : baseEnd_1395571 < baseStart_1395571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395616 : List Nat := [2, 1, 1, 4, 1, 1, 3, 9]
def baseStart_1395616 : Nat := 118140960795 + 1395616 * 2 ^ 59
def prefixEnd_1395616 : Nat := 4983230072969 + 3 ^ 40 * 1395616 * 2
def baseEnd_1395616 : Nat := 53083097563356805902347

theorem tailTrace_1395616 : CollatzResearch.WordTrace tailWord_1395616 prefixEnd_1395616 53083097563356805902347 := by
  unfold tailWord_1395616
  simp only [CollatzResearch.WordTrace]
  refine ⟨25451148655964529540859351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33934864874619372721145801 25451148655964529540859351)
  ·
    refine ⟨38176722983946794311289027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25451148655964529540859351 38176722983946794311289027)
    ·
      refine ⟨57265084475920191466933541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38176722983946794311289027 57265084475920191466933541)
      ·
        refine ⟨10737203339235035900050039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57265084475920191466933541 10737203339235035900050039)
        ·
          refine ⟨16105805008852553850075059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10737203339235035900050039 16105805008852553850075059)
          ·
            refine ⟨24158707513278830775112589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16105805008852553850075059 24158707513278830775112589)
            ·
              refine ⟨9059515317479561540667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24158707513278830775112589 9059515317479561540667221)
              ·
                refine ⟨53083097563356805902347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9059515317479561540667221 53083097563356805902347)
                ·
                  rfl

theorem cell22_1395616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_1395616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395616 prefixEnd_1395616 := by exact prefixLift 1395616
  have htrace : WordTrace (prefixWord ++ tailWord_1395616) baseStart_1395616 baseEnd_1395616 := by
    simpa [prefixWord, tailWord_1395616, baseEnd_1395616] using wordTrace_append hprefix tailTrace_1395616
  have hstable : (prefixWord ++ tailWord_1395616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395616).length < 2 ^ (prefixWord ++ tailWord_1395616).sum := by decide
  have hdescent : baseEnd_1395616 < baseStart_1395616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395620 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1395620 : Nat := 118140960795 + 1395620 * 2 ^ 59
def prefixEnd_1395620 : Nat := 4983230072969 + 3 ^ 40 * 1395620 * 2
def baseEnd_1395620 : Nat := 477749247351956576021111

theorem tailTrace_1395620 : CollatzResearch.WordTrace tailWord_1395620 prefixEnd_1395620 477749247351956576021111 := by
  unfold tailWord_1395620
  simp only [CollatzResearch.WordTrace]
  refine ⟨25451221601957283882432157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33934962135943045176576209 25451221601957283882432157)
  ·
    refine ⟨9544208100733981455912059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25451221601957283882432157 9544208100733981455912059)
    ·
      refine ⟨14316312151100972183868089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9544208100733981455912059 14316312151100972183868089)
      ·
        refine ⟨10737234113325729137901067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14316312151100972183868089 10737234113325729137901067)
        ·
          refine ⟨16105851169988593706851601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10737234113325729137901067 16105851169988593706851601)
          ·
            refine ⟨12079388377491445280138701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16105851169988593706851601 12079388377491445280138701)
            ·
              refine ⟨4529770641559291980052013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12079388377491445280138701 4529770641559291980052013)
              ·
                refine ⟨1698663990584734492519505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4529770641559291980052013 1698663990584734492519505)
                ·
                  refine ⟨1273997992938550869389629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698663990584734492519505 1273997992938550869389629)
                  ·
                    refine ⟨477749247351956576021111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273997992938550869389629 477749247351956576021111)
                    ·
                      rfl

theorem cell22_1395620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1395620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395620 prefixEnd_1395620 := by exact prefixLift 1395620
  have htrace : WordTrace (prefixWord ++ tailWord_1395620) baseStart_1395620 baseEnd_1395620 := by
    simpa [prefixWord, tailWord_1395620, baseEnd_1395620] using wordTrace_append hprefix tailTrace_1395620
  have hstable : (prefixWord ++ tailWord_1395620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395620).length < 2 ^ (prefixWord ++ tailWord_1395620).sum := by decide
  have hdescent : baseEnd_1395620 < baseStart_1395620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395682 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1395682 : Nat := 118140960795 + 1395682 * 2 ^ 59
def prefixEnd_1395682 : Nat := 4983230072969 + 3 ^ 40 * 1395682 * 2
def baseEnd_1395682 : Nat := 477770471219009080970921

theorem tailTrace_1395682 : CollatzResearch.WordTrace tailWord_1395682 prefixEnd_1395682 477770471219009080970921 := by
  unfold tailWord_1395682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726176132422488088405325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33936469686459968235747533 12726176132422488088405325)
  ·
    refine ⟨4772316049658433033151997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12726176132422488088405325 4772316049658433033151997)
    ·
      refine ⟨1789618518621912387431999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4772316049658433033151997 1789618518621912387431999)
      ·
        refine ⟨2684427777932868581147999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789618518621912387431999 2684427777932868581147999)
        ·
          refine ⟨4026641666899302871721999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684427777932868581147999 4026641666899302871721999)
          ·
            refine ⟨6039962500348954307582999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026641666899302871721999 6039962500348954307582999)
            ·
              refine ⟨9059943750523431461374499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039962500348954307582999 9059943750523431461374499)
              ·
                refine ⟨13589915625785147192061749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9059943750523431461374499 13589915625785147192061749)
                ·
                  refine ⟨1274054589917357549255789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13589915625785147192061749 1274054589917357549255789)
                  ·
                    refine ⟨477770471219009080970921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274054589917357549255789 477770471219009080970921)
                    ·
                      rfl

theorem cell22_1395682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1395682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395682 prefixEnd_1395682 := by exact prefixLift 1395682
  have htrace : WordTrace (prefixWord ++ tailWord_1395682) baseStart_1395682 baseEnd_1395682 := by
    simpa [prefixWord, tailWord_1395682, baseEnd_1395682] using wordTrace_append hprefix tailTrace_1395682
  have hstable : (prefixWord ++ tailWord_1395682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395682).length < 2 ^ (prefixWord ++ tailWord_1395682).sum := by decide
  have hdescent : baseEnd_1395682 < baseStart_1395682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395723 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 6]
def baseStart_1395723 : Nat := 118140960795 + 1395723 * 2 ^ 59
def prefixEnd_1395723 : Nat := 4983230072969 + 3 ^ 40 * 1395723 * 2
def baseEnd_1395723 : Nat := 159261502118966213565265

theorem tailTrace_1395723 : CollatzResearch.WordTrace tailWord_1395723 prefixEnd_1395723 159261502118966213565265 := by
  unfold tailWord_1395723
  simp only [CollatzResearch.WordTrace]
  refine ⟨50906199922541416355863823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33937466615027610903909215 50906199922541416355863823)
  ·
    refine ⟨76359299883812124533795735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50906199922541416355863823 76359299883812124533795735)
    ·
      refine ⟨114538949825718186800693603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76359299883812124533795735 114538949825718186800693603)
      ·
        refine ⟨171808424738577280201040405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114538949825718186800693603 171808424738577280201040405)
        ·
          refine ⟨8053519909620810009423769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171808424738577280201040405 8053519909620810009423769)
          ·
            refine ⟨6040139932215607507067827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8053519909620810009423769 6040139932215607507067827)
            ·
              refine ⟨9060209898323411260601741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040139932215607507067827 9060209898323411260601741)
              ·
                refine ⟨3397578711871279222725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9060209898323411260601741 3397578711871279222725653)
                ·
                  refine ⟨159261502118966213565265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3397578711871279222725653 159261502118966213565265)
                  ·
                    rfl

theorem cell22_1395723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_1395723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395723 prefixEnd_1395723 := by exact prefixLift 1395723
  have htrace : WordTrace (prefixWord ++ tailWord_1395723) baseStart_1395723 baseEnd_1395723 := by
    simpa [prefixWord, tailWord_1395723, baseEnd_1395723] using wordTrace_append hprefix tailTrace_1395723
  have hstable : (prefixWord ++ tailWord_1395723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395723).length < 2 ^ (prefixWord ++ tailWord_1395723).sum := by decide
  have hdescent : baseEnd_1395723 < baseStart_1395723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395768 : List Nat := [2, 1, 2, 1, 5, 1, 10]
def baseStart_1395768 : Nat := 118140960795 + 1395768 * 2 ^ 59
def prefixEnd_1395768 : Nat := 4983230072969 + 3 ^ 40 * 1395768 * 2
def baseEnd_1395768 : Nat := 17696292991723463826691

theorem tailTrace_1395768 : CollatzResearch.WordTrace tailWord_1395768 prefixEnd_1395768 17696292991723463826691 := by
  unfold tailWord_1395768
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453920603689194520625979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33938560804918926027501305 25453920603689194520625979)
  ·
    refine ⟨38180880905533791780938969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25453920603689194520625979 38180880905533791780938969)
    ·
      refine ⟨28635660679150343835704227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38180880905533791780938969 28635660679150343835704227)
      ·
        refine ⟨42953491018725515753556341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28635660679150343835704227 42953491018725515753556341)
        ·
          refine ⟨4026889783005517101895907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42953491018725515753556341 4026889783005517101895907)
          ·
            refine ⟨6040334674508275652843861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026889783005517101895907 6040334674508275652843861)
            ·
              refine ⟨17696292991723463826691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6040334674508275652843861 17696292991723463826691)
              ·
                rfl

theorem cell22_1395768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 10].length) (baseStart_1395768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395768 prefixEnd_1395768 := by exact prefixLift 1395768
  have htrace : WordTrace (prefixWord ++ tailWord_1395768) baseStart_1395768 baseEnd_1395768 := by
    simpa [prefixWord, tailWord_1395768, baseEnd_1395768] using wordTrace_append hprefix tailTrace_1395768
  have hstable : (prefixWord ++ tailWord_1395768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395768).length < 2 ^ (prefixWord ++ tailWord_1395768).sum := by decide
  have hdescent : baseEnd_1395768 < baseStart_1395768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395789 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1395789 : Nat := 118140960795 + 1395789 * 2 ^ 59
def prefixEnd_1395789 : Nat := 4983230072969 + 3 ^ 40 * 1395789 * 2
def baseEnd_1395789 : Nat := 477807099505696468545593

theorem tailTrace_1395789 : CollatzResearch.WordTrace tailWord_1395789 prefixEnd_1395789 477807099505696468545593 := by
  unfold tailWord_1395789
  simp only [CollatzResearch.WordTrace]
  refine ⟨50908607140302309627766421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33939071426868206418510947 50908607140302309627766421)
  ·
    refine ⟨2386340959701670763801551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50908607140302309627766421 2386340959701670763801551)
    ·
      refine ⟨3579511439552506145702327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386340959701670763801551 3579511439552506145702327)
      ·
        refine ⟨5369267159328759218553491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579511439552506145702327 5369267159328759218553491)
        ·
          refine ⟨8053900738993138827830237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369267159328759218553491 8053900738993138827830237)
          ·
            refine ⟨3020212777122427060436339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8053900738993138827830237 3020212777122427060436339)
            ·
              refine ⟨4530319165683640590654509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020212777122427060436339 4530319165683640590654509)
              ·
                refine ⟨1698869687131365221495441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4530319165683640590654509 1698869687131365221495441)
                ·
                  refine ⟨1274152265348523916121581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698869687131365221495441 1274152265348523916121581)
                  ·
                    refine ⟨477807099505696468545593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274152265348523916121581 477807099505696468545593)
                    ·
                      rfl

theorem cell22_1395789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1395789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395789 prefixEnd_1395789 := by exact prefixLift 1395789
  have htrace : WordTrace (prefixWord ++ tailWord_1395789) baseStart_1395789 baseEnd_1395789 := by
    simpa [prefixWord, tailWord_1395789, baseEnd_1395789] using wordTrace_append hprefix tailTrace_1395789
  have hstable : (prefixWord ++ tailWord_1395789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395789).length < 2 ^ (prefixWord ++ tailWord_1395789).sum := by decide
  have hdescent : baseEnd_1395789 < baseStart_1395789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395800 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1395800 : Nat := 118140960795 + 1395800 * 2 ^ 59
def prefixEnd_1395800 : Nat := 4983230072969 + 3 ^ 40 * 1395800 * 2
def baseEnd_1395800 : Nat := 477810865030496106520559

theorem tailTrace_1395800 : CollatzResearch.WordTrace tailWord_1395800 prefixEnd_1395800 477810865030496106520559 := by
  unfold tailWord_1395800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25454504171631229253208427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33939338895508305670944569 25454504171631229253208427)
  ·
    refine ⟨38181756257446843879812641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25454504171631229253208427 38181756257446843879812641)
    ·
      refine ⟨28636317193085132909859481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38181756257446843879812641 28636317193085132909859481)
      ·
        refine ⟨21477237894813849682394611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28636317193085132909859481 21477237894813849682394611)
        ·
          refine ⟨32215856842220774523591917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21477237894813849682394611 32215856842220774523591917)
          ·
            refine ⟨12080946315832790446346969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32215856842220774523591917 12080946315832790446346969)
            ·
              refine ⟨9060709736874592834760227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12080946315832790446346969 9060709736874592834760227)
              ·
                refine ⟨13591064605311889252140341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060709736874592834760227 13591064605311889252140341)
                ·
                  refine ⟨1274162306747989617388157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13591064605311889252140341 1274162306747989617388157)
                  ·
                    refine ⟨477810865030496106520559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274162306747989617388157 477810865030496106520559)
                    ·
                      rfl

theorem cell22_1395800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1395800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395800 prefixEnd_1395800 := by exact prefixLift 1395800
  have htrace : WordTrace (prefixWord ++ tailWord_1395800) baseStart_1395800 baseEnd_1395800 := by
    simpa [prefixWord, tailWord_1395800, baseEnd_1395800] using wordTrace_append hprefix tailTrace_1395800
  have hstable : (prefixWord ++ tailWord_1395800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395800).length < 2 ^ (prefixWord ++ tailWord_1395800).sum := by decide
  have hdescent : baseEnd_1395800 < baseStart_1395800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395877 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1395877 : Nat := 118140960795 + 1395877 * 2 ^ 59
def prefixEnd_1395877 : Nat := 4983230072969 + 3 ^ 40 * 1395877 * 2
def baseEnd_1395877 : Nat := 477837223704093572345323

theorem tailTrace_1395877 : CollatzResearch.WordTrace tailWord_1395877 prefixEnd_1395877 477837223704093572345323 := by
  unfold tailWord_1395877
  simp only [CollatzResearch.WordTrace]
  refine ⟨50911816763983500656969885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33941211175989000437979923 50911816763983500656969885)
  ·
    refine ⟨19091931286493812746363707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50911816763983500656969885 19091931286493812746363707)
    ·
      refine ⟨28637896929740719119545561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19091931286493812746363707 28637896929740719119545561)
      ·
        refine ⟨21478422697305539339659171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28637896929740719119545561 21478422697305539339659171)
        ·
          refine ⟨32217634045958309009488757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21478422697305539339659171 32217634045958309009488757)
          ·
            refine ⟨3020403191808591469639571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32217634045958309009488757 3020403191808591469639571)
            ·
              refine ⟨4530604787712887204459357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020403191808591469639571 4530604787712887204459357)
              ·
                refine ⟨1698976795392332701672259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4530604787712887204459357 1698976795392332701672259)
                ·
                  refine ⟨2548465193088499052508389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698976795392332701672259 2548465193088499052508389)
                  ·
                    refine ⟨477837223704093572345323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548465193088499052508389 477837223704093572345323)
                    ·
                      rfl

theorem cell22_1395877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1395877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395877 prefixEnd_1395877 := by exact prefixLift 1395877
  have htrace : WordTrace (prefixWord ++ tailWord_1395877) baseStart_1395877 baseEnd_1395877 := by
    simpa [prefixWord, tailWord_1395877, baseEnd_1395877] using wordTrace_append hprefix tailTrace_1395877
  have hstable : (prefixWord ++ tailWord_1395877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395877).length < 2 ^ (prefixWord ++ tailWord_1395877).sum := by decide
  have hdescent : baseEnd_1395877 < baseStart_1395877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395922 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1395922 : Nat := 118140960795 + 1395922 * 2 ^ 59
def prefixEnd_1395922 : Nat := 4983230072969 + 3 ^ 40 * 1395922 * 2
def baseEnd_1395922 : Nat := 477852628123728454970185

theorem tailTrace_1395922 : CollatzResearch.WordTrace tailWord_1395922 prefixEnd_1395922 477852628123728454970185 := by
  unfold tailWord_1395922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728364512205118335589505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33942305365880315561572013 12728364512205118335589505)
  ·
    refine ⟨9546273384153838751692129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12728364512205118335589505 9546273384153838751692129)
    ·
      refine ⟨7159705038115379063769097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9546273384153838751692129 7159705038115379063769097)
      ·
        refine ⟨5369778778586534297826823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7159705038115379063769097 5369778778586534297826823)
        ·
          refine ⟨8054668167879801446740235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369778778586534297826823 8054668167879801446740235)
          ·
            refine ⟨12082002251819702170110353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054668167879801446740235 12082002251819702170110353)
            ·
              refine ⟨9061501688864776627582765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12082002251819702170110353 9061501688864776627582765)
              ·
                refine ⟨3398063133324291235343537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9061501688864776627582765 3398063133324291235343537)
                ·
                  refine ⟨2548547349993218426507653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398063133324291235343537 2548547349993218426507653)
                  ·
                    refine ⟨477852628123728454970185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548547349993218426507653 477852628123728454970185)
                    ·
                      rfl

theorem cell22_1395922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1395922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395922 prefixEnd_1395922 := by exact prefixLift 1395922
  have htrace : WordTrace (prefixWord ++ tailWord_1395922) baseStart_1395922 baseEnd_1395922 := by
    simpa [prefixWord, tailWord_1395922, baseEnd_1395922] using wordTrace_append hprefix tailTrace_1395922
  have hstable : (prefixWord ++ tailWord_1395922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395922).length < 2 ^ (prefixWord ++ tailWord_1395922).sum := by decide
  have hdescent : baseEnd_1395922 < baseStart_1395922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395999 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 5]
def baseStart_1395999 : Nat := 118140960795 + 1395999 * 2 ^ 59
def prefixEnd_1395999 : Nat := 4983230072969 + 3 ^ 40 * 1395999 * 2
def baseEnd_1395999 : Nat := 159292995599108640264983

theorem tailTrace_1395999 : CollatzResearch.WordTrace tailWord_1395999 prefixEnd_1395999 159292995599108640264983 := by
  unfold tailWord_1395999
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916266469541515492911051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33944177646361010328607367 50916266469541515492911051)
  ·
    refine ⟨76374399704312273239366577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50916266469541515492911051 76374399704312273239366577)
    ·
      refine ⟨57280799778234204929524933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76374399704312273239366577 57280799778234204929524933)
      ·
        refine ⟨10740149958418913424285925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57280799778234204929524933 10740149958418913424285925)
        ·
          refine ⟨2013778117203546267053611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10740149958418913424285925 2013778117203546267053611)
          ·
            refine ⟨3020667175805319400580417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013778117203546267053611 3020667175805319400580417)
            ·
              refine ⟨2265500381853989550435313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020667175805319400580417 2265500381853989550435313)
              ·
                refine ⟨1699125286390492162826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265500381853989550435313 1699125286390492162826485)
                ·
                  refine ⟨159292995599108640264983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1699125286390492162826485 159292995599108640264983)
                  ·
                    rfl

theorem cell22_1395999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].length) (baseStart_1395999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1395999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1395999 prefixEnd_1395999 := by exact prefixLift 1395999
  have htrace : WordTrace (prefixWord ++ tailWord_1395999) baseStart_1395999 baseEnd_1395999 := by
    simpa [prefixWord, tailWord_1395999, baseEnd_1395999] using wordTrace_append hprefix tailTrace_1395999
  have hstable : (prefixWord ++ tailWord_1395999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395999).length < 2 ^ (prefixWord ++ tailWord_1395999).sum := by decide
  have hdescent : baseEnd_1395999 < baseStart_1395999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396003 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 1, 3]
def baseStart_1396003 : Nat := 118140960795 + 1396003 * 2 ^ 59
def prefixEnd_1396003 : Nat := 4983230072969 + 3 ^ 40 * 1396003 * 2
def baseEnd_1396003 : Nat := 477880356079071243694937

theorem tailTrace_1396003 : CollatzResearch.WordTrace tailWord_1396003 prefixEnd_1396003 477880356079071243694937 := by
  unfold tailWord_1396003
  simp only [CollatzResearch.WordTrace]
  refine ⟨50916412361527024176056663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33944274907684682784037775 50916412361527024176056663)
  ·
    refine ⟨76374618542290536264084995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50916412361527024176056663 76374618542290536264084995)
    ·
      refine ⟨114561927813435804396127493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76374618542290536264084995 114561927813435804396127493)
      ·
        refine ⟨21480361465019213324273905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114561927813435804396127493 21480361465019213324273905)
        ·
          refine ⟨16110271098764409993205429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21480361465019213324273905 16110271098764409993205429)
          ·
            refine ⟨1510337915509163436863009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16110271098764409993205429 1510337915509163436863009)
            ·
              refine ⟨1132753436631872577647257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510337915509163436863009 1132753436631872577647257)
              ·
                refine ⟨849565077473904433235443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132753436631872577647257 849565077473904433235443)
                ·
                  refine ⟨1274347616210856649853165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849565077473904433235443 1274347616210856649853165)
                  ·
                    refine ⟨477880356079071243694937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274347616210856649853165 477880356079071243694937)
                    ·
                      rfl

theorem cell22_1396003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 3].length) (baseStart_1396003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396003 prefixEnd_1396003 := by exact prefixLift 1396003
  have htrace : WordTrace (prefixWord ++ tailWord_1396003) baseStart_1396003 baseEnd_1396003 := by
    simpa [prefixWord, tailWord_1396003, baseEnd_1396003] using wordTrace_append hprefix tailTrace_1396003
  have hstable : (prefixWord ++ tailWord_1396003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396003).length < 2 ^ (prefixWord ++ tailWord_1396003).sum := by decide
  have hdescent : baseEnd_1396003 < baseStart_1396003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396044 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_1396044 : Nat := 118140960795 + 1396044 * 2 ^ 59
def prefixEnd_1396044 : Nat := 4983230072969 + 3 ^ 40 * 1396044 * 2
def baseEnd_1396044 : Nat := 159298130405653601139937

theorem tailTrace_1396044 : CollatzResearch.WordTrace tailWord_1396044 prefixEnd_1396044 159298130405653601139937 := by
  unfold tailWord_1396044
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458953877189244089149593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33945271836252325452199457 25458953877189244089149593)
  ·
    refine ⟨19094215407891933066862195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25458953877189244089149593 19094215407891933066862195)
    ·
      refine ⟨28641323111837899600293293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19094215407891933066862195 28641323111837899600293293)
      ·
        refine ⟨10740496166939212350109985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28641323111837899600293293 10740496166939212350109985)
        ·
          refine ⟨8055372125204409262582489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10740496166939212350109985 8055372125204409262582489)
          ·
            refine ⟨6041529093903306946936867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8055372125204409262582489 6041529093903306946936867)
            ·
              refine ⟨9062293640854960420405301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041529093903306946936867 9062293640854960420405301)
              ·
                refine ⟨849590028830152539412997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9062293640854960420405301 849590028830152539412997)
                ·
                  refine ⟨159298130405653601139937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849590028830152539412997 159298130405653601139937)
                  ·
                    rfl

theorem cell22_1396044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_1396044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396044 prefixEnd_1396044 := by exact prefixLift 1396044
  have htrace : WordTrace (prefixWord ++ tailWord_1396044) baseStart_1396044 baseEnd_1396044 := by
    simpa [prefixWord, tailWord_1396044, baseEnd_1396044] using wordTrace_append hprefix tailTrace_1396044
  have hstable : (prefixWord ++ tailWord_1396044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396044).length < 2 ^ (prefixWord ++ tailWord_1396044).sum := by decide
  have hdescent : baseEnd_1396044 < baseStart_1396044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396057 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_1396057 : Nat := 118140960795 + 1396057 * 2 ^ 59
def prefixEnd_1396057 : Nat := 4983230072969 + 3 ^ 40 * 1396057 * 2
def baseEnd_1396057 : Nat := 477898841382633102844771

theorem tailTrace_1396057 : CollatzResearch.WordTrace tailWord_1396057 prefixEnd_1396057 477898841382633102844771 := by
  unfold tailWord_1396057
  simp only [CollatzResearch.WordTrace]
  refine ⟨50918381903331391398522425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33945587935554260932348283 50918381903331391398522425)
  ·
    refine ⟨38188786427498543548891819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50918381903331391398522425 38188786427498543548891819)
    ·
      refine ⟨57283179641247815323337729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38188786427498543548891819 57283179641247815323337729)
      ·
        refine ⟨42962384730935861492503297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57283179641247815323337729 42962384730935861492503297)
        ·
          refine ⟨32221788548201896119377473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42962384730935861492503297 32221788548201896119377473)
          ·
            refine ⟨24166341411151422089533105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32221788548201896119377473 24166341411151422089533105)
            ·
              refine ⟨18124756058363566567149829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24166341411151422089533105 18124756058363566567149829)
              ·
                refine ⟨3398391760943168731340593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18124756058363566567149829 3398391760943168731340593)
                ·
                  refine ⟨2548793820707376548505445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398391760943168731340593 2548793820707376548505445)
                  ·
                    refine ⟨477898841382633102844771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2548793820707376548505445 477898841382633102844771)
                    ·
                      rfl

theorem cell22_1396057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_1396057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396057 prefixEnd_1396057 := by exact prefixLift 1396057
  have htrace : WordTrace (prefixWord ++ tailWord_1396057) baseStart_1396057 baseEnd_1396057 := by
    simpa [prefixWord, tailWord_1396057, baseEnd_1396057] using wordTrace_append hprefix tailTrace_1396057
  have hstable : (prefixWord ++ tailWord_1396057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396057).length < 2 ^ (prefixWord ++ tailWord_1396057).sum := by decide
  have hdescent : baseEnd_1396057 < baseStart_1396057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396117 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 7]
def baseStart_1396117 : Nat := 118140960795 + 1396117 * 2 ^ 59
def prefixEnd_1396117 : Nat := 4983230072969 + 3 ^ 40 * 1396117 * 2
def baseEnd_1396117 : Nat := 159306460202937648781529

theorem tailTrace_1396117 : CollatzResearch.WordTrace tailWord_1396117 prefixEnd_1396117 159306460202937648781529 := by
  unfold tailWord_1396117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50920570283114021645706605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33947046855409347763804403 50920570283114021645706605)
  ·
    refine ⟨19095213856167758117139977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50920570283114021645706605 19095213856167758117139977)
    ·
      refine ⟨14321410392125818587854983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19095213856167758117139977 14321410392125818587854983)
      ·
        refine ⟨21482115588188727881782475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321410392125818587854983 21482115588188727881782475)
        ·
          refine ⟨32223173382283091822673713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21482115588188727881782475 32223173382283091822673713)
          ·
            refine ⟨24167380036712318867005285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32223173382283091822673713 24167380036712318867005285)
            ·
              refine ⟨4531383756883559787563491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24167380036712318867005285 4531383756883559787563491)
              ·
                refine ⟨6797075635325339681345237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531383756883559787563491 6797075635325339681345237)
                ·
                  refine ⟨159306460202937648781529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6797075635325339681345237 159306460202937648781529)
                  ·
                    rfl

theorem cell22_1396117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_1396117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396117 prefixEnd_1396117 := by exact prefixLift 1396117
  have htrace : WordTrace (prefixWord ++ tailWord_1396117) baseStart_1396117 baseEnd_1396117 := by
    simpa [prefixWord, tailWord_1396117, baseEnd_1396117] using wordTrace_append hprefix tailTrace_1396117
  have hstable : (prefixWord ++ tailWord_1396117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396117).length < 2 ^ (prefixWord ++ tailWord_1396117).sum := by decide
  have hdescent : baseEnd_1396117 < baseStart_1396117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396121 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_1396121 : Nat := 118140960795 + 1396121 * 2 ^ 59
def prefixEnd_1396121 : Nat := 4983230072969 + 3 ^ 40 * 1396121 * 2
def baseEnd_1396121 : Nat := 477920749890558269244575

theorem tailTrace_1396121 : CollatzResearch.WordTrace tailWord_1396121 prefixEnd_1396121 477920749890558269244575 := by
  unfold tailWord_1396121
  simp only [CollatzResearch.WordTrace]
  refine ⟨50920716175099530328852217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33947144116733020219234811 50920716175099530328852217)
  ·
    refine ⟨38190537131324647746639163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50920716175099530328852217 38190537131324647746639163)
    ·
      refine ⟨57285805696986971619958745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38190537131324647746639163 57285805696986971619958745)
      ·
        refine ⟨42964354272740228714969059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57285805696986971619958745 42964354272740228714969059)
        ·
          refine ⟨64446531409110343072453589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42964354272740228714969059 64446531409110343072453589)
          ·
            refine ⟨1510465579901023665760631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64446531409110343072453589 1510465579901023665760631)
            ·
              refine ⟨2265698369851535498640947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510465579901023665760631 2265698369851535498640947)
              ·
                refine ⟨3398547554777303247961421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265698369851535498640947 3398547554777303247961421)
                ·
                  refine ⟨1274455333041488717985533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3398547554777303247961421 1274455333041488717985533)
                  ·
                    refine ⟨477920749890558269244575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274455333041488717985533 477920749890558269244575)
                    ·
                      rfl

theorem cell22_1396121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_1396121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396121 prefixEnd_1396121 := by exact prefixLift 1396121
  have htrace : WordTrace (prefixWord ++ tailWord_1396121) baseStart_1396121 baseEnd_1396121 := by
    simpa [prefixWord, tailWord_1396121, baseEnd_1396121] using wordTrace_append hprefix tailTrace_1396121
  have hstable : (prefixWord ++ tailWord_1396121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396121).length < 2 ^ (prefixWord ++ tailWord_1396121).sum := by decide
  have hdescent : baseEnd_1396121 < baseStart_1396121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396132 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1396132 : Nat := 118140960795 + 1396132 * 2 ^ 59
def prefixEnd_1396132 : Nat := 4983230072969 + 3 ^ 40 * 1396132 * 2
def baseEnd_1396132 : Nat := 477924515415357907219541

theorem tailTrace_1396132 : CollatzResearch.WordTrace tailWord_1396132 prefixEnd_1396132 477924515415357907219541 := by
  unfold tailWord_1396132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25460558689029839603751325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33947411585373119471668433 25460558689029839603751325)
  ·
    refine ⟨9547709508386189851406747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25460558689029839603751325 9547709508386189851406747)
    ·
      refine ⟨14321564262579284777110121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9547709508386189851406747 14321564262579284777110121)
      ·
        refine ⟨10741173196934463582832591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14321564262579284777110121 10741173196934463582832591)
        ·
          refine ⟨16111759795401695374248887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10741173196934463582832591 16111759795401695374248887)
          ·
            refine ⟨24167639693102543061373331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16111759795401695374248887 24167639693102543061373331)
            ·
              refine ⟨36251459539653814592059997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24167639693102543061373331 36251459539653814592059997)
              ·
                refine ⟨13594297327370180472022499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36251459539653814592059997 13594297327370180472022499)
                ·
                  refine ⟨20391445991055270708033749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13594297327370180472022499 20391445991055270708033749)
                  ·
                    refine ⟨477924515415357907219541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20391445991055270708033749 477924515415357907219541)
                    ·
                      rfl

theorem cell22_1396132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1396132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396132 prefixEnd_1396132 := by exact prefixLift 1396132
  have htrace : WordTrace (prefixWord ++ tailWord_1396132) baseStart_1396132 baseEnd_1396132 := by
    simpa [prefixWord, tailWord_1396132, baseEnd_1396132] using wordTrace_append hprefix tailTrace_1396132
  have hstable : (prefixWord ++ tailWord_1396132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396132).length < 2 ^ (prefixWord ++ tailWord_1396132).sum := by decide
  have hdescent : baseEnd_1396132 < baseStart_1396132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396207 : List Nat := [1, 1, 2, 1, 4, 1, 2, 10]
def baseStart_1396207 : Nat := 118140960795 + 1396207 * 2 ^ 59
def prefixEnd_1396207 : Nat := 4983230072969 + 3 ^ 40 * 1396207 * 2
def baseEnd_1396207 : Nat := 53105576605342523510479

theorem tailTrace_1396207 : CollatzResearch.WordTrace tailWord_1396207 prefixEnd_1396207 53105576605342523510479 := by
  unfold tailWord_1396207
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923852852787967016482875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33949235235191978010988583 50923852852787967016482875)
  ·
    refine ⟨76385779279181950524724313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50923852852787967016482875 76385779279181950524724313)
    ·
      refine ⟨57289334459386462893543235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76385779279181950524724313 57289334459386462893543235)
      ·
        refine ⟨85934001689079694340314853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57289334459386462893543235 85934001689079694340314853)
        ·
          refine ⟨16112625316702442688809035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85934001689079694340314853 16112625316702442688809035)
          ·
            refine ⟨24168937975053664033213553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16112625316702442688809035 24168937975053664033213553)
            ·
              refine ⟨18126703481290248024910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24168937975053664033213553 18126703481290248024910165)
              ·
                refine ⟨53105576605342523510479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18126703481290248024910165 53105576605342523510479)
                ·
                  rfl

theorem cell22_1396207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 10].length) (baseStart_1396207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396207 prefixEnd_1396207 := by exact prefixLift 1396207
  have htrace : WordTrace (prefixWord ++ tailWord_1396207) baseStart_1396207 baseEnd_1396207 := by
    simpa [prefixWord, tailWord_1396207, baseEnd_1396207] using wordTrace_append hprefix tailTrace_1396207
  have hstable : (prefixWord ++ tailWord_1396207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396207).length < 2 ^ (prefixWord ++ tailWord_1396207).sum := by decide
  have hdescent : baseEnd_1396207 < baseStart_1396207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396209 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1396209 : Nat := 118140960795 + 1396209 * 2 ^ 59
def prefixEnd_1396209 : Nat := 4983230072969 + 3 ^ 40 * 1396209 * 2
def baseEnd_1396209 : Nat := 477950874088955373044305

theorem tailTrace_1396209 : CollatzResearch.WordTrace tailWord_1396209 prefixEnd_1396209 477950874088955373044305 := by
  unfold tailWord_1396209
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923925798780721358055681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33949283865853814238703787 50923925798780721358055681)
  ·
    refine ⟨38192944349085541018541761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50923925798780721358055681 38192944349085541018541761)
    ·
      refine ⟨28644708261814155763906321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38192944349085541018541761 28644708261814155763906321)
      ·
        refine ⟨21483531196360616822929741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28644708261814155763906321 21483531196360616822929741)
        ·
          refine ⟨8056324198635231308598653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21483531196360616822929741 8056324198635231308598653)
          ·
            refine ⟨3021121574488211740724495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8056324198635231308598653 3021121574488211740724495)
            ·
              refine ⟨4531682361732317611086743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021121574488211740724495 4531682361732317611086743)
              ·
                refine ⟨6797523542598476416630115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531682361732317611086743 6797523542598476416630115)
                ·
                  refine ⟨10196285313897714624945173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6797523542598476416630115 10196285313897714624945173)
                  ·
                    refine ⟨477950874088955373044305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10196285313897714624945173 477950874088955373044305)
                    ·
                      rfl

theorem cell22_1396209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1396209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396209 prefixEnd_1396209 := by exact prefixLift 1396209
  have htrace : WordTrace (prefixWord ++ tailWord_1396209) baseStart_1396209 baseEnd_1396209 := by
    simpa [prefixWord, tailWord_1396209, baseEnd_1396209] using wordTrace_append hprefix tailTrace_1396209
  have hstable : (prefixWord ++ tailWord_1396209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396209).length < 2 ^ (prefixWord ++ tailWord_1396209).sum := by decide
  have hdescent : baseEnd_1396209 < baseStart_1396209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396213 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 4]
def baseStart_1396213 : Nat := 118140960795 + 1396213 * 2 ^ 59
def prefixEnd_1396213 : Nat := 4983230072969 + 3 ^ 40 * 1396213 * 2
def baseEnd_1396213 : Nat := 159317414456900231981431

theorem tailTrace_1396213 : CollatzResearch.WordTrace tailWord_1396213 prefixEnd_1396213 159317414456900231981431 := by
  unfold tailWord_1396213
  simp only [CollatzResearch.WordTrace]
  refine ⟨50924071690766230041201293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33949381127177486694134195 50924071690766230041201293)
  ·
    refine ⟨19096526884037336265450485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50924071690766230041201293 19096526884037336265450485)
    ·
      refine ⟨1790299395378500274885983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19096526884037336265450485 1790299395378500274885983)
      ·
        refine ⟨2685449093067750412328975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790299395378500274885983 2685449093067750412328975)
        ·
          refine ⟨4028173639601625618493463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685449093067750412328975 4028173639601625618493463)
          ·
            refine ⟨6042260459402438427740195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028173639601625618493463 6042260459402438427740195)
            ·
              refine ⟨9063390689103657641610293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042260459402438427740195 9063390689103657641610293)
              ·
                refine ⟨849692877103467903900965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9063390689103657641610293 849692877103467903900965)
                ·
                  refine ⟨159317414456900231981431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849692877103467903900965 159317414456900231981431)
                  ·
                    rfl

theorem cell22_1396213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_1396213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396213 prefixEnd_1396213 := by exact prefixLift 1396213
  have htrace : WordTrace (prefixWord ++ tailWord_1396213) baseStart_1396213 baseEnd_1396213 := by
    simpa [prefixWord, tailWord_1396213, baseEnd_1396213] using wordTrace_append hprefix tailTrace_1396213
  have hstable : (prefixWord ++ tailWord_1396213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396213).length < 2 ^ (prefixWord ++ tailWord_1396213).sum := by decide
  have hdescent : baseEnd_1396213 < baseStart_1396213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396228 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1396228 : Nat := 118140960795 + 1396228 * 2 ^ 59
def prefixEnd_1396228 : Nat := 4983230072969 + 3 ^ 40 * 1396228 * 2
def baseEnd_1396228 : Nat := 477957378177245656819247

theorem tailTrace_1396228 : CollatzResearch.WordTrace tailWord_1396228 prefixEnd_1396228 477957378177245656819247 := by
  unfold tailWord_1396228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25462309392855943801498669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33949745857141258401998225 25462309392855943801498669)
  ·
    refine ⟨9548366022320978925562001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25462309392855943801498669 9548366022320978925562001)
    ·
      refine ⟨7161274516740734194171501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9548366022320978925562001 7161274516740734194171501)
      ·
        refine ⟨2685477943777775322814313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7161274516740734194171501 2685477943777775322814313)
        ·
          refine ⟨2014108457833331492110735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685477943777775322814313 2014108457833331492110735)
          ·
            refine ⟨3021162686749997238166103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014108457833331492110735 3021162686749997238166103)
            ·
              refine ⟨4531744030124995857249155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021162686749997238166103 4531744030124995857249155)
              ·
                refine ⟨6797616045187493785873733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4531744030124995857249155 6797616045187493785873733)
                ·
                  refine ⟨1274553008472655084851325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6797616045187493785873733 1274553008472655084851325)
                  ·
                    refine ⟨477957378177245656819247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274553008472655084851325 477957378177245656819247)
                    ·
                      rfl

theorem cell22_1396228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1396228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396228 prefixEnd_1396228 := by exact prefixLift 1396228
  have htrace : WordTrace (prefixWord ++ tailWord_1396228) baseStart_1396228 baseEnd_1396228 := by
    simpa [prefixWord, tailWord_1396228, baseEnd_1396228] using wordTrace_append hprefix tailTrace_1396228
  have hstable : (prefixWord ++ tailWord_1396228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396228).length < 2 ^ (prefixWord ++ tailWord_1396228).sum := by decide
  have hdescent : baseEnd_1396228 < baseStart_1396228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396299 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_1396299 : Nat := 118140960795 + 1396299 * 2 ^ 59
def prefixEnd_1396299 : Nat := 4983230072969 + 3 ^ 40 * 1396299 * 2
def baseEnd_1396299 : Nat := 477981682928225138294029

theorem tailTrace_1396299 : CollatzResearch.WordTrace tailWord_1396299 prefixEnd_1396299 477981682928225138294029 := by
  unfold tailWord_1396299
  simp only [CollatzResearch.WordTrace]
  refine ⟨50927208368454666728831951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33951472245636444485887967 50927208368454666728831951)
  ·
    refine ⟨76390812552682000093247927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50927208368454666728831951 76390812552682000093247927)
    ·
      refine ⟨114586218829023000139871891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76390812552682000093247927 114586218829023000139871891)
      ·
        refine ⟨171879328243534500209807837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114586218829023000139871891 171879328243534500209807837)
        ·
          refine ⟨64454748091325437578677939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171879328243534500209807837 64454748091325437578677939)
          ·
            refine ⟨96682122136988156368016909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64454748091325437578677939 96682122136988156368016909)
            ·
              refine ⟨36255795801370558638006341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96682122136988156368016909 36255795801370558638006341)
              ·
                refine ⟨6797961712756979744626189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36255795801370558638006341 6797961712756979744626189)
                ·
                  refine ⟨2549235642283867404234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6797961712756979744626189 2549235642283867404234821)
                  ·
                    refine ⟨477981682928225138294029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549235642283867404234821 477981682928225138294029)
                    ·
                      rfl

theorem cell22_1396299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_1396299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396299 prefixEnd_1396299 := by exact prefixLift 1396299
  have htrace : WordTrace (prefixWord ++ tailWord_1396299) baseStart_1396299 baseEnd_1396299 := by
    simpa [prefixWord, tailWord_1396299, baseEnd_1396299] using wordTrace_append hprefix tailTrace_1396299
  have hstable : (prefixWord ++ tailWord_1396299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396299).length < 2 ^ (prefixWord ++ tailWord_1396299).sum := by decide
  have hdescent : baseEnd_1396299 < baseStart_1396299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396314 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_1396314 : Nat := 118140960795 + 1396314 * 2 ^ 59
def prefixEnd_1396314 : Nat := 4983230072969 + 3 ^ 40 * 1396314 * 2
def baseEnd_1396314 : Nat := 159328939244923366389661

theorem tailTrace_1396314 : CollatzResearch.WordTrace tailWord_1396314 prefixEnd_1396314 159328939244923366389661 := by
  unfold tailWord_1396314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731938865850081072656999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33951836975600216193751997 12731938865850081072656999)
  ·
    refine ⟨19097908298775121608985499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12731938865850081072656999 19097908298775121608985499)
    ·
      refine ⟨28646862448162682413478249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19097908298775121608985499 28646862448162682413478249)
      ·
        refine ⟨21485146836122011810108687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28646862448162682413478249 21485146836122011810108687)
        ·
          refine ⟨32227720254183017715163031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21485146836122011810108687 32227720254183017715163031)
          ·
            refine ⟨48341580381274526572744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32227720254183017715163031 48341580381274526572744547)
            ·
              refine ⟨72512370571911789859116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48341580381274526572744547 72512370571911789859116821)
              ·
                refine ⟨3399017370558365149646101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72512370571911789859116821 3399017370558365149646101)
                ·
                  refine ⟨159328939244923366389661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3399017370558365149646101 159328939244923366389661)
                  ·
                    rfl

theorem cell22_1396314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_1396314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396314 prefixEnd_1396314 := by exact prefixLift 1396314
  have htrace : WordTrace (prefixWord ++ tailWord_1396314) baseStart_1396314 baseEnd_1396314 := by
    simpa [prefixWord, tailWord_1396314, baseEnd_1396314] using wordTrace_append hprefix tailTrace_1396314
  have hstable : (prefixWord ++ tailWord_1396314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396314).length < 2 ^ (prefixWord ++ tailWord_1396314).sum := by decide
  have hdescent : baseEnd_1396314 < baseStart_1396314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396329 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_1396329 : Nat := 118140960795 + 1396329 * 2 ^ 59
def prefixEnd_1396329 : Nat := 4983230072969 + 3 ^ 40 * 1396329 * 2
def baseEnd_1396329 : Nat := 477991952541315060043937

theorem tailTrace_1396329 : CollatzResearch.WordTrace tailWord_1396329 prefixEnd_1396329 477991952541315060043937 := by
  unfold tailWord_1396329
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928302558345981852424041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33952201705563987901616027 50928302558345981852424041)
  ·
    refine ⟨38196226918759486389318031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50928302558345981852424041 38196226918759486389318031)
    ·
      refine ⟨57294340378139229583977047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38196226918759486389318031 57294340378139229583977047)
      ·
        refine ⟨85941510567208844375965571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57294340378139229583977047 85941510567208844375965571)
        ·
          refine ⟨128912265850813266563948357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85941510567208844375965571 128912265850813266563948357)
          ·
            refine ⟨24171049847027487480740317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128912265850813266563948357 24171049847027487480740317)
            ·
              refine ⟨9064143692635307805277619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24171049847027487480740317 9064143692635307805277619)
              ·
                refine ⟨13596215538952961707916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9064143692635307805277619 13596215538952961707916429)
                ·
                  refine ⟨5098580827107360640468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13596215538952961707916429 5098580827107360640468661)
                  ·
                    refine ⟨477991952541315060043937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5098580827107360640468661 477991952541315060043937)
                    ·
                      rfl

theorem cell22_1396329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_1396329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396329 prefixEnd_1396329 := by exact prefixLift 1396329
  have htrace : WordTrace (prefixWord ++ tailWord_1396329) baseStart_1396329 baseEnd_1396329 := by
    simpa [prefixWord, tailWord_1396329, baseEnd_1396329] using wordTrace_append hprefix tailTrace_1396329
  have hstable : (prefixWord ++ tailWord_1396329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396329).length < 2 ^ (prefixWord ++ tailWord_1396329).sum := by decide
  have hdescent : baseEnd_1396329 < baseStart_1396329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396442 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_1396442 : Nat := 118140960795 + 1396442 * 2 ^ 59
def prefixEnd_1396442 : Nat := 4983230072969 + 3 ^ 40 * 1396442 * 2
def baseEnd_1396442 : Nat := 478030634750620431968591

theorem tailTrace_1396442 : CollatzResearch.WordTrace tailWord_1396442 prefixEnd_1396442 478030634750620431968591 := by
  unfold tailWord_1396442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733106001734150537821895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33954949337957734767525053 12733106001734150537821895)
  ·
    refine ⟨19099659002601225806732843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12733106001734150537821895 19099659002601225806732843)
    ·
      refine ⟨28649488503901838710099265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19099659002601225806732843 28649488503901838710099265)
      ·
        refine ⟨21487116377926379032574449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28649488503901838710099265 21487116377926379032574449)
        ·
          refine ⟨16115337283444784274430837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21487116377926379032574449 16115337283444784274430837)
          ·
            refine ⟨1510812870322948525727891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16115337283444784274430837 1510812870322948525727891)
            ·
              refine ⟨2266219305484422788591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510812870322948525727891 2266219305484422788591837)
              ·
                refine ⟨849832239556658545721939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266219305484422788591837 849832239556658545721939)
                ·
                  refine ⟨1274748359334987818582909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849832239556658545721939 1274748359334987818582909)
                  ·
                    refine ⟨478030634750620431968591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274748359334987818582909 478030634750620431968591)
                    ·
                      rfl

theorem cell22_1396442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_1396442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396442 prefixEnd_1396442 := by exact prefixLift 1396442
  have htrace : WordTrace (prefixWord ++ tailWord_1396442) baseStart_1396442 baseEnd_1396442 := by
    simpa [prefixWord, tailWord_1396442, baseEnd_1396442] using wordTrace_append hprefix tailTrace_1396442
  have hstable : (prefixWord ++ tailWord_1396442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396442).length < 2 ^ (prefixWord ++ tailWord_1396442).sum := by decide
  have hdescent : baseEnd_1396442 < baseStart_1396442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396510 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1396510 : Nat := 118140960795 + 1396510 * 2 ^ 59
def prefixEnd_1396510 : Nat := 4983230072969 + 3 ^ 40 * 1396510 * 2
def baseEnd_1396510 : Nat := 478053912540290921268383

theorem tailTrace_1396510 : CollatzResearch.WordTrace tailWord_1396510 prefixEnd_1396510 478053912540290921268383 := by
  unfold tailWord_1396510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366863021336281220595373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33956602780460166509841989 6366863021336281220595373)
  ·
    refine ⟨2387573633001105457723265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6366863021336281220595373 2387573633001105457723265)
    ·
      refine ⟨1790680224750829093292449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2387573633001105457723265 1790680224750829093292449)
      ·
        refine ⟨1343010168563121819969337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790680224750829093292449 1343010168563121819969337)
        ·
          refine ⟨1007257626422341364977003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343010168563121819969337 1007257626422341364977003)
          ·
            refine ⟨1510886439633512047465505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007257626422341364977003 1510886439633512047465505)
            ·
              refine ⟨1133164829725134035599129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510886439633512047465505 1133164829725134035599129)
              ·
                refine ⟨849873622293850526699347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133164829725134035599129 849873622293850526699347)
                ·
                  refine ⟨1274810433440775790049021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849873622293850526699347 1274810433440775790049021)
                  ·
                    refine ⟨478053912540290921268383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274810433440775790049021 478053912540290921268383)
                    ·
                      rfl

theorem cell22_1396510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1396510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396510 prefixEnd_1396510 := by exact prefixLift 1396510
  have htrace : WordTrace (prefixWord ++ tailWord_1396510) baseStart_1396510 baseEnd_1396510 := by
    simpa [prefixWord, tailWord_1396510, baseEnd_1396510] using wordTrace_append hprefix tailTrace_1396510
  have hstable : (prefixWord ++ tailWord_1396510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396510).length < 2 ^ (prefixWord ++ tailWord_1396510).sum := by decide
  have hdescent : baseEnd_1396510 < baseStart_1396510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396513 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1396513 : Nat := 118140960795 + 1396513 * 2 ^ 59
def prefixEnd_1396513 : Nat := 4983230072969 + 3 ^ 40 * 1396513 * 2
def baseEnd_1396513 : Nat := 478054939501599913443373

theorem tailTrace_1396513 : CollatzResearch.WordTrace tailWord_1396513 prefixEnd_1396513 478054939501599913443373 := by
  unfold tailWord_1396513
  simp only [CollatzResearch.WordTrace]
  refine ⟨50935013589679381277122193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33956675726452920851414795 50935013589679381277122193)
  ·
    refine ⟨38201260192259535957841645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50935013589679381277122193 38201260192259535957841645)
    ·
      refine ⟨14325472572097325984190617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38201260192259535957841645 14325472572097325984190617)
      ·
        refine ⟨10744104429072994488142963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14325472572097325984190617 10744104429072994488142963)
        ·
          refine ⟨16116156643609491732214445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10744104429072994488142963 16116156643609491732214445)
          ·
            refine ⟨6043558741353559399580417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16116156643609491732214445 6043558741353559399580417)
            ·
              refine ⟨4532669056015169549685313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043558741353559399580417 4532669056015169549685313)
              ·
                refine ⟨3399501792011377162263985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532669056015169549685313 3399501792011377162263985)
                ·
                  refine ⟨2549626344008532871697989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399501792011377162263985 2549626344008532871697989)
                  ·
                    refine ⟨478054939501599913443373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549626344008532871697989 478054939501599913443373)
                    ·
                      rfl

theorem cell22_1396513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1396513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396513 prefixEnd_1396513 := by exact prefixLift 1396513
  have htrace : WordTrace (prefixWord ++ tailWord_1396513) baseStart_1396513 baseEnd_1396513 := by
    simpa [prefixWord, tailWord_1396513, baseEnd_1396513] using wordTrace_append hprefix tailTrace_1396513
  have hstable : (prefixWord ++ tailWord_1396513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396513).length < 2 ^ (prefixWord ++ tailWord_1396513).sum := by decide
  have hdescent : baseEnd_1396513 < baseStart_1396513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396517 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 4]
def baseStart_1396517 : Nat := 118140960795 + 1396517 * 2 ^ 59
def prefixEnd_1396517 : Nat := 4983230072969 + 3 ^ 40 * 1396517 * 2
def baseEnd_1396517 : Nat := 159352102927781745447787

theorem tailTrace_1396517 : CollatzResearch.WordTrace tailWord_1396517 prefixEnd_1396517 159352102927781745447787 := by
  unfold tailWord_1396517
  simp only [CollatzResearch.WordTrace]
  refine ⟨50935159481664889960267805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33956772987776593306845203 50935159481664889960267805)
  ·
    refine ⟨19100684805624333735100427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50935159481664889960267805 19100684805624333735100427)
    ·
      refine ⟨28651027208436500602650641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19100684805624333735100427 28651027208436500602650641)
      ·
        refine ⟨21488270406327375451987981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28651027208436500602650641 21488270406327375451987981)
        ·
          refine ⟨8058101402372765794495493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21488270406327375451987981 8058101402372765794495493)
          ·
            refine ⟨1510894012944893586467905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8058101402372765794495493 1510894012944893586467905)
            ·
              refine ⟨1133170509708670189850929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510894012944893586467905 1133170509708670189850929)
              ·
                refine ⟨849877882281502642388197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133170509708670189850929 849877882281502642388197)
                ·
                  refine ⟨159352102927781745447787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849877882281502642388197 159352102927781745447787)
                  ·
                    rfl

theorem cell22_1396517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_1396517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396517 prefixEnd_1396517 := by exact prefixLift 1396517
  have htrace : WordTrace (prefixWord ++ tailWord_1396517) baseStart_1396517 baseEnd_1396517 := by
    simpa [prefixWord, tailWord_1396517, baseEnd_1396517] using wordTrace_append hprefix tailTrace_1396517
  have hstable : (prefixWord ++ tailWord_1396517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396517).length < 2 ^ (prefixWord ++ tailWord_1396517).sum := by decide
  have hdescent : baseEnd_1396517 < baseStart_1396517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396532 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1396532 : Nat := 118140960795 + 1396532 * 2 ^ 59
def prefixEnd_1396532 : Nat := 4983230072969 + 3 ^ 40 * 1396532 * 2
def baseEnd_1396532 : Nat := 478061443589890197218315

theorem tailTrace_1396532 : CollatzResearch.WordTrace tailWord_1396532 prefixEnd_1396532 478061443589890197218315 := by
  unfold tailWord_1396532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25467853288305273761031925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33957137717740365014709233 25467853288305273761031925)
  ·
    refine ⟨2387611245778619415096743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25467853288305273761031925 2387611245778619415096743)
    ·
      refine ⟨3581416868667929122645115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387611245778619415096743 3581416868667929122645115)
      ·
        refine ⟨5372125303001893683967673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581416868667929122645115 5372125303001893683967673)
        ·
          refine ⟨4029093977251420262975755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5372125303001893683967673 4029093977251420262975755)
          ·
            refine ⟨6043640965877130394463633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029093977251420262975755 6043640965877130394463633)
            ·
              refine ⟨4532730724407847795847725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043640965877130394463633 4532730724407847795847725)
              ·
                refine ⟨1699774021652942923442897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4532730724407847795847725 1699774021652942923442897)
                ·
                  refine ⟨1274830516239707192582173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1699774021652942923442897 1274830516239707192582173)
                  ·
                    refine ⟨478061443589890197218315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274830516239707192582173 478061443589890197218315)
                    ·
                      rfl

theorem cell22_1396532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1396532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396532 prefixEnd_1396532 := by exact prefixLift 1396532
  have htrace : WordTrace (prefixWord ++ tailWord_1396532) baseStart_1396532 baseEnd_1396532 := by
    simpa [prefixWord, tailWord_1396532, baseEnd_1396532] using wordTrace_append hprefix tailTrace_1396532
  have hstable : (prefixWord ++ tailWord_1396532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396532).length < 2 ^ (prefixWord ++ tailWord_1396532).sum := by decide
  have hdescent : baseEnd_1396532 < baseStart_1396532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396588 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1396588 : Nat := 118140960795 + 1396588 * 2 ^ 59
def prefixEnd_1396588 : Nat := 4983230072969 + 3 ^ 40 * 1396588 * 2
def baseEnd_1396588 : Nat := 478080613534324717818143

theorem tailTrace_1396588 : CollatzResearch.WordTrace tailWord_1396588 prefixEnd_1396588 478080613534324717818143 := by
  unfold tailWord_1396588
  simp only [CollatzResearch.WordTrace]
  refine ⟨25468874532203834543051209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33958499376271779390734945 25468874532203834543051209)
  ·
    refine ⟨19101655899152875907288407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25468874532203834543051209 19101655899152875907288407)
    ·
      refine ⟨28652483848729313860932611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19101655899152875907288407 28652483848729313860932611)
      ·
        refine ⟨42978725773093970791398917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28652483848729313860932611 42978725773093970791398917)
        ·
          refine ⟨8058511082455119523387297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42978725773093970791398917 8058511082455119523387297)
          ·
            refine ⟨6043883311841339642540473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8058511082455119523387297 6043883311841339642540473)
            ·
              refine ⟨4532912483881004731905355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043883311841339642540473 4532912483881004731905355)
              ·
                refine ⟨6799368725821507097858033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4532912483881004731905355 6799368725821507097858033)
                ·
                  refine ⟨5099526544366130323393525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6799368725821507097858033 5099526544366130323393525)
                  ·
                    refine ⟨478080613534324717818143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5099526544366130323393525 478080613534324717818143)
                    ·
                      rfl

theorem cell22_1396588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1396588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396588 prefixEnd_1396588 := by exact prefixLift 1396588
  have htrace : WordTrace (prefixWord ++ tailWord_1396588) baseStart_1396588 baseEnd_1396588 := by
    simpa [prefixWord, tailWord_1396588, baseEnd_1396588] using wordTrace_append hprefix tailTrace_1396588
  have hstable : (prefixWord ++ tailWord_1396588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396588).length < 2 ^ (prefixWord ++ tailWord_1396588).sum := by decide
  have hdescent : baseEnd_1396588 < baseStart_1396588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396665 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_1396665 : Nat := 118140960795 + 1396665 * 2 ^ 59
def prefixEnd_1396665 : Nat := 4983230072969 + 3 ^ 40 * 1396665 * 2
def baseEnd_1396665 : Nat := 478106972207922183642907

theorem tailTrace_1396665 : CollatzResearch.WordTrace tailWord_1396665 prefixEnd_1396665 478106972207922183642907 := by
  unfold tailWord_1396665
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940557485128711236655449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33960371656752474157770299 50940557485128711236655449)
  ·
    refine ⟨38205418113846533427491587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50940557485128711236655449 38205418113846533427491587)
    ·
      refine ⟨57308127170769800141237381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38205418113846533427491587 57308127170769800141237381)
      ·
        refine ⟨10745273844519337526482009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57308127170769800141237381 10745273844519337526482009)
        ·
          refine ⟨8058955383389503144861507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10745273844519337526482009 8058955383389503144861507)
          ·
            refine ⟨12088433075084254717292261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058955383389503144861507 12088433075084254717292261)
            ·
              refine ⟨2266581201578297759492299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12088433075084254717292261 2266581201578297759492299)
              ·
                refine ⟨3399871802367446639238449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266581201578297759492299 3399871802367446639238449)
                ·
                  refine ⟨2549903851775584979428837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399871802367446639238449 2549903851775584979428837)
                  ·
                    refine ⟨478106972207922183642907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2549903851775584979428837 478106972207922183642907)
                    ·
                      rfl

theorem cell22_1396665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_1396665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396665 prefixEnd_1396665 := by exact prefixLift 1396665
  have htrace : WordTrace (prefixWord ++ tailWord_1396665) baseStart_1396665 baseEnd_1396665 := by
    simpa [prefixWord, tailWord_1396665, baseEnd_1396665] using wordTrace_append hprefix tailTrace_1396665
  have hstable : (prefixWord ++ tailWord_1396665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396665).length < 2 ^ (prefixWord ++ tailWord_1396665).sum := by decide
  have hdescent : baseEnd_1396665 < baseStart_1396665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396695 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 3, 3]
def baseStart_1396695 : Nat := 118140960795 + 1396695 * 2 ^ 59
def prefixEnd_1396695 : Nat := 4983230072969 + 3 ^ 40 * 1396695 * 2
def baseEnd_1396695 : Nat := 478117241821012105392815

theorem tailTrace_1396695 : CollatzResearch.WordTrace tailWord_1396695 prefixEnd_1396695 478117241821012105392815 := by
  unfold tailWord_1396695
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941651675020026360247539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33961101116680017573498359 50941651675020026360247539)
  ·
    refine ⟨76412477512530039540371309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50941651675020026360247539 76412477512530039540371309)
    ·
      refine ⟨28654679067198764827639241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76412477512530039540371309 28654679067198764827639241)
      ·
        refine ⟨21491009300399073620729431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28654679067198764827639241 21491009300399073620729431)
        ·
          refine ⟨32236513950598610431094147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491009300399073620729431 32236513950598610431094147)
          ·
            refine ⟨48354770925897915646641221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32236513950598610431094147 48354770925897915646641221)
            ·
              refine ⟨9066519548605859183745229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48354770925897915646641221 9066519548605859183745229)
              ·
                refine ⟨3399944830727197193904461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9066519548605859183745229 3399944830727197193904461)
                ·
                  refine ⟨1274979311522698947714173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3399944830727197193904461 1274979311522698947714173)
                  ·
                    refine ⟨478117241821012105392815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1274979311522698947714173 478117241821012105392815)
                    ·
                      rfl

theorem cell22_1396695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_1396695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396695 prefixEnd_1396695 := by exact prefixLift 1396695
  have htrace : WordTrace (prefixWord ++ tailWord_1396695) baseStart_1396695 baseEnd_1396695 := by
    simpa [prefixWord, tailWord_1396695, baseEnd_1396695] using wordTrace_append hprefix tailTrace_1396695
  have hstable : (prefixWord ++ tailWord_1396695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396695).length < 2 ^ (prefixWord ++ tailWord_1396695).sum := by decide
  have hdescent : baseEnd_1396695 < baseStart_1396695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396697 : List Nat := [1, 2, 1, 2, 7, 1, 1, 7]
def baseStart_1396697 : Nat := 118140960795 + 1396697 * 2 ^ 59
def prefixEnd_1396697 : Nat := 4983230072969 + 3 ^ 40 * 1396697 * 2
def baseEnd_1396697 : Nat := 53124214051320529649201

theorem tailTrace_1396697 : CollatzResearch.WordTrace tailWord_1396697 prefixEnd_1396697 53124214051320529649201 := by
  unfold tailWord_1396697
  simp only [CollatzResearch.WordTrace]
  refine ⟨50941724621012780701820345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33961149747341853801213563 50941724621012780701820345)
  ·
    refine ⟨38206293465759585526365259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50941724621012780701820345 38206293465759585526365259)
    ·
      refine ⟨57309440198639378289547889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38206293465759585526365259 57309440198639378289547889)
      ·
        refine ⟨42982080148979533717160917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57309440198639378289547889 42982080148979533717160917)
        ·
          refine ⟨1007392503491707821495959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42982080148979533717160917 1007392503491707821495959)
          ·
            refine ⟨1511088755237561732243939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007392503491707821495959 1511088755237561732243939)
            ·
              refine ⟨2266633132856342598365909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511088755237561732243939 2266633132856342598365909)
              ·
                refine ⟨53124214051320529649201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2266633132856342598365909 53124214051320529649201)
                ·
                  rfl

theorem cell22_1396697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 7].length) (baseStart_1396697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396697 prefixEnd_1396697 := by exact prefixLift 1396697
  have htrace : WordTrace (prefixWord ++ tailWord_1396697) baseStart_1396697 baseEnd_1396697 := by
    simpa [prefixWord, tailWord_1396697, baseEnd_1396697] using wordTrace_append hprefix tailTrace_1396697
  have hstable : (prefixWord ++ tailWord_1396697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396697).length < 2 ^ (prefixWord ++ tailWord_1396697).sum := by decide
  have hdescent : baseEnd_1396697 < baseStart_1396697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396729 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_1396729 : Nat := 118140960795 + 1396729 * 2 ^ 59
def prefixEnd_1396729 : Nat := 4983230072969 + 3 ^ 40 * 1396729 * 2
def baseEnd_1396729 : Nat := 478128880715847350042711

theorem tailTrace_1396729 : CollatzResearch.WordTrace tailWord_1396729 prefixEnd_1396729 478128880715847350042711 := by
  unfold tailWord_1396729
  simp only [CollatzResearch.WordTrace]
  refine ⟨50942891756896850166985241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33961927837931233444656827 50942891756896850166985241)
  ·
    refine ⟨38207168817672637625238931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50942891756896850166985241 38207168817672637625238931)
    ·
      refine ⟨57310753226508956437858397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38207168817672637625238931 57310753226508956437858397)
      ·
        refine ⟨21491532459940858664196899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57310753226508956437858397 21491532459940858664196899)
        ·
          refine ⟨32237298689911287996295349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491532459940858664196899 32237298689911287996295349)
          ·
            refine ⟨3022246752179183249652689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32237298689911287996295349 3022246752179183249652689)
            ·
              refine ⟨2266685064134387437239517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022246752179183249652689 2266685064134387437239517)
              ·
                refine ⟨850006899050395288964819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266685064134387437239517 850006899050395288964819)
                ·
                  refine ⟨1275010348575592933447229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850006899050395288964819 1275010348575592933447229)
                  ·
                    refine ⟨478128880715847350042711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275010348575592933447229 478128880715847350042711)
                    ·
                      rfl

theorem cell22_1396729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_1396729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396729 prefixEnd_1396729 := by exact prefixLift 1396729
  have htrace : WordTrace (prefixWord ++ tailWord_1396729) baseStart_1396729 baseEnd_1396729 := by
    simpa [prefixWord, tailWord_1396729, baseEnd_1396729] using wordTrace_append hprefix tailTrace_1396729
  have hstable : (prefixWord ++ tailWord_1396729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396729).length < 2 ^ (prefixWord ++ tailWord_1396729).sum := by decide
  have hdescent : baseEnd_1396729 < baseStart_1396729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396759 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 5]
def baseStart_1396759 : Nat := 118140960795 + 1396759 * 2 ^ 59
def prefixEnd_1396759 : Nat := 4983230072969 + 3 ^ 40 * 1396759 * 2
def baseEnd_1396759 : Nat := 159379716776312423930873

theorem tailTrace_1396759 : CollatzResearch.WordTrace tailWord_1396759 prefixEnd_1396759 159379716776312423930873 := by
  unfold tailWord_1396759
  simp only [CollatzResearch.WordTrace]
  refine ⟨50943985946788165290577331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33962657297858776860384887 50943985946788165290577331)
  ·
    refine ⟨76415978920182247935865997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50943985946788165290577331 76415978920182247935865997)
    ·
      refine ⟨28655992095068342975949749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76415978920182247935865997 28655992095068342975949749)
      ·
        refine ⟨2686499258912657153995289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28655992095068342975949749 2686499258912657153995289)
        ·
          refine ⟨2014874444184492865496467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2686499258912657153995289 2014874444184492865496467)
          ·
            refine ⟨3022311666276739298244701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014874444184492865496467 3022311666276739298244701)
            ·
              refine ⟨1133366874853777236841763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3022311666276739298244701 1133366874853777236841763)
              ·
                refine ⟨1700050312280665855262645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133366874853777236841763 1700050312280665855262645)
                ·
                  refine ⟨159379716776312423930873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700050312280665855262645 159379716776312423930873)
                  ·
                    rfl

theorem cell22_1396759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 5].length) (baseStart_1396759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396759 prefixEnd_1396759 := by exact prefixLift 1396759
  have htrace : WordTrace (prefixWord ++ tailWord_1396759) baseStart_1396759 baseEnd_1396759 := by
    simpa [prefixWord, tailWord_1396759, baseEnd_1396759] using wordTrace_append hprefix tailTrace_1396759
  have hstable : (prefixWord ++ tailWord_1396759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396759).length < 2 ^ (prefixWord ++ tailWord_1396759).sum := by decide
  have hdescent : baseEnd_1396759 < baseStart_1396759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396770 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1396770 : Nat := 118140960795 + 1396770 * 2 ^ 59
def prefixEnd_1396770 : Nat := 4983230072969 + 3 ^ 40 * 1396770 * 2
def baseEnd_1396770 : Nat := 159380971951245636589195

theorem tailTrace_1396770 : CollatzResearch.WordTrace tailWord_1396770 prefixEnd_1396770 159380971951245636589195 := by
  unfold tailWord_1396770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736096787437078542306941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33962924766498876112818509 12736096787437078542306941)
  ·
    refine ⟨4776036295288904453365103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12736096787437078542306941 4776036295288904453365103)
    ·
      refine ⟨7164054442933356680047655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776036295288904453365103 7164054442933356680047655)
      ·
        refine ⟨10746081664400035020071483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7164054442933356680047655 10746081664400035020071483)
        ·
          refine ⟨16119122496600052530107225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746081664400035020071483 16119122496600052530107225)
          ·
            refine ⟨12089341872450039397580419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16119122496600052530107225 12089341872450039397580419)
            ·
              refine ⟨18134012808675059096370629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089341872450039397580419 18134012808675059096370629)
              ·
                refine ⟨3400127401626573580569493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18134012808675059096370629 3400127401626573580569493)
                ·
                  refine ⟨159380971951245636589195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3400127401626573580569493 159380971951245636589195)
                  ·
                    rfl

theorem cell22_1396770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1396770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396770 prefixEnd_1396770 := by exact prefixLift 1396770
  have htrace : WordTrace (prefixWord ++ tailWord_1396770) baseStart_1396770 baseEnd_1396770 := by
    simpa [prefixWord, tailWord_1396770, baseEnd_1396770] using wordTrace_append hprefix tailTrace_1396770
  have hstable : (prefixWord ++ tailWord_1396770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396770).length < 2 ^ (prefixWord ++ tailWord_1396770).sum := by decide
  have hdescent : baseEnd_1396770 < baseStart_1396770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396787 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 4]
def baseStart_1396787 : Nat := 118140960795 + 1396787 * 2 ^ 59
def prefixEnd_1396787 : Nat := 4983230072969 + 3 ^ 40 * 1396787 * 2
def baseEnd_1396787 : Nat := 159382911767051510697511

theorem tailTrace_1396787 : CollatzResearch.WordTrace tailWord_1396787 prefixEnd_1396787 159382911767051510697511 := by
  unfold tailWord_1396787
  simp only [CollatzResearch.WordTrace]
  refine ⟨50945007190686726072596615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33963338127124484048397743 50945007190686726072596615)
  ·
    refine ⟨76417510786030089108894923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50945007190686726072596615 76417510786030089108894923)
    ·
      refine ⟨114626266179045133663342385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76417510786030089108894923 114626266179045133663342385)
      ·
        refine ⟨85969699634283850247506789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114626266179045133663342385 85969699634283850247506789)
        ·
          refine ⟨16119318681428221921407523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85969699634283850247506789 16119318681428221921407523)
          ·
            refine ⟨24178978022142332882111285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16119318681428221921407523 24178978022142332882111285)
            ·
              refine ⟨2266779189575843707697933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24178978022142332882111285 2266779189575843707697933)
              ·
                refine ⟨850042196090941390386725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266779189575843707697933 850042196090941390386725)
                ·
                  refine ⟨159382911767051510697511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850042196090941390386725 159382911767051510697511)
                  ·
                    rfl

theorem cell22_1396787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 4].length) (baseStart_1396787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396787 prefixEnd_1396787 := by exact prefixLift 1396787
  have htrace : WordTrace (prefixWord ++ tailWord_1396787) baseStart_1396787 baseEnd_1396787 := by
    simpa [prefixWord, tailWord_1396787, baseEnd_1396787] using wordTrace_append hprefix tailTrace_1396787
  have hstable : (prefixWord ++ tailWord_1396787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396787).length < 2 ^ (prefixWord ++ tailWord_1396787).sum := by decide
  have hdescent : baseEnd_1396787 < baseStart_1396787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396800 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_1396800 : Nat := 118140960795 + 1396800 * 2 ^ 59
def prefixEnd_1396800 : Nat := 4983230072969 + 3 ^ 40 * 1396800 * 2
def baseEnd_1396800 : Nat := 478153185466826831517493

theorem tailTrace_1396800 : CollatzResearch.WordTrace tailWord_1396800 prefixEnd_1396800 478153185466826831517493 := by
  unfold tailWord_1396800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25472740669819814646409927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33963654226426419528546569 25472740669819814646409927)
  ·
    refine ⟨38209111004729721969614891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25472740669819814646409927 38209111004729721969614891)
    ·
      refine ⟨57313666507094582954422337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38209111004729721969614891 57313666507094582954422337)
      ·
        refine ⟨42985249880320937215816753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57313666507094582954422337 42985249880320937215816753)
        ·
          refine ⟨32238937410240702911862565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42985249880320937215816753 32238937410240702911862565)
          ·
            refine ⟨6044800764420131795974231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32238937410240702911862565 6044800764420131795974231)
            ·
              refine ⟨9067201146630197693961347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044800764420131795974231 9067201146630197693961347)
              ·
                refine ⟨13600801719945296540942021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9067201146630197693961347 13600801719945296540942021)
                ·
                  refine ⟨2550150322489743101426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13600801719945296540942021 2550150322489743101426629)
                  ·
                    refine ⟨478153185466826831517493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550150322489743101426629 478153185466826831517493)
                    ·
                      rfl

theorem cell22_1396800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_1396800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396800 prefixEnd_1396800 := by exact prefixLift 1396800
  have htrace : WordTrace (prefixWord ++ tailWord_1396800) baseStart_1396800 baseEnd_1396800 := by
    simpa [prefixWord, tailWord_1396800, baseEnd_1396800] using wordTrace_append hprefix tailTrace_1396800
  have hstable : (prefixWord ++ tailWord_1396800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396800).length < 2 ^ (prefixWord ++ tailWord_1396800).sum := by decide
  have hdescent : baseEnd_1396800 < baseStart_1396800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396898 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1396898 : Nat := 118140960795 + 1396898 * 2 ^ 59
def prefixEnd_1396898 : Nat := 4983230072969 + 3 ^ 40 * 1396898 * 2
def baseEnd_1396898 : Nat := 478186732869587242567193

theorem tailTrace_1396898 : CollatzResearch.WordTrace tailWord_1396898 prefixEnd_1396898 478186732869587242567193 := by
  unfold tailWord_1396898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737263923321148007471837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33966037128856394686591565 12737263923321148007471837)
  ·
    refine ⟨4776473971245430502801939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12737263923321148007471837 4776473971245430502801939)
    ·
      refine ⟨7164710956868145754202909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776473971245430502801939 7164710956868145754202909)
      ·
        refine ⟨2686766608825554657826091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7164710956868145754202909 2686766608825554657826091)
        ·
          refine ⟨4030149913238331986739137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686766608825554657826091 4030149913238331986739137)
          ·
            refine ⟨3022612434928748990054353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030149913238331986739137 3022612434928748990054353)
            ·
              refine ⟨2266959326196561742540765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022612434928748990054353 2266959326196561742540765)
              ·
                refine ⟨850109747323710653452787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266959326196561742540765 850109747323710653452787)
                ·
                  refine ⟨1275164620985565980179181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850109747323710653452787 1275164620985565980179181)
                  ·
                    refine ⟨478186732869587242567193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275164620985565980179181 478186732869587242567193)
                    ·
                      rfl

theorem cell22_1396898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1396898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396898 prefixEnd_1396898 := by exact prefixLift 1396898
  have htrace : WordTrace (prefixWord ++ tailWord_1396898) baseStart_1396898 baseEnd_1396898 := by
    simpa [prefixWord, tailWord_1396898, baseEnd_1396898] using wordTrace_append hprefix tailTrace_1396898
  have hstable : (prefixWord ++ tailWord_1396898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396898).length < 2 ^ (prefixWord ++ tailWord_1396898).sum := by decide
  have hdescent : baseEnd_1396898 < baseStart_1396898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396952 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1396952 : Nat := 118140960795 + 1396952 * 2 ^ 59
def prefixEnd_1396952 : Nat := 4983230072969 + 3 ^ 40 * 1396952 * 2
def baseEnd_1396952 : Nat := 478205218173149101717027

theorem tailTrace_1396952 : CollatzResearch.WordTrace tailWord_1396952 prefixEnd_1396952 478205218173149101717027 := by
  unfold tailWord_1396952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25475512617544479626176555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33967350156725972834902073 25475512617544479626176555)
  ·
    refine ⟨38213268926316719439264833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25475512617544479626176555 38213268926316719439264833)
    ·
      refine ⟨28659951694737539579448625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38213268926316719439264833 28659951694737539579448625)
      ·
        refine ⟨21494963771053154684586469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28659951694737539579448625 21494963771053154684586469)
        ·
          refine ⟨4030305707072466503359963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21494963771053154684586469 4030305707072466503359963)
          ·
            refine ⟨6045458560608699755039945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030305707072466503359963 6045458560608699755039945)
            ·
              refine ⟨4534093920456524816279959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6045458560608699755039945 4534093920456524816279959)
              ·
                refine ⟨6801140880684787224419939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4534093920456524816279959 6801140880684787224419939)
                ·
                  refine ⟨10201711321027180836629909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801140880684787224419939 10201711321027180836629909)
                  ·
                    refine ⟨478205218173149101717027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10201711321027180836629909 478205218173149101717027)
                    ·
                      rfl

theorem cell22_1396952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1396952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396952 prefixEnd_1396952 := by exact prefixLift 1396952
  have htrace : WordTrace (prefixWord ++ tailWord_1396952) baseStart_1396952 baseEnd_1396952 := by
    simpa [prefixWord, tailWord_1396952, baseEnd_1396952] using wordTrace_append hprefix tailTrace_1396952
  have hstable : (prefixWord ++ tailWord_1396952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396952).length < 2 ^ (prefixWord ++ tailWord_1396952).sum := by decide
  have hdescent : baseEnd_1396952 < baseStart_1396952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396967 : List Nat := [1, 1, 5, 3, 1, 1, 10]
def baseStart_1396967 : Nat := 118140960795 + 1396967 * 2 ^ 59
def prefixEnd_1396967 : Nat := 4983230072969 + 3 ^ 40 * 1396967 * 2
def baseEnd_1396967 : Nat := 17711494554803483799703

theorem tailTrace_1396967 : CollatzResearch.WordTrace tailWord_1396967 prefixEnd_1396967 17711494554803483799703 := by
  unfold tailWord_1396967
  simp only [CollatzResearch.WordTrace]
  refine ⟨50951572330034616814149155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33967714886689744542766103 50951572330034616814149155)
  ·
    refine ⟨76427358495051925221223733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50951572330034616814149155 76427358495051925221223733)
    ·
      refine ⟨7165064858911117989489725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76427358495051925221223733 7165064858911117989489725)
      ·
        refine ⟨2686899322091669246058647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7165064858911117989489725 2686899322091669246058647)
        ·
          refine ⟨4030348983137503869087971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686899322091669246058647 4030348983137503869087971)
          ·
            refine ⟨6045523474706255803631957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030348983137503869087971 6045523474706255803631957)
            ·
              refine ⟨17711494554803483799703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6045523474706255803631957 17711494554803483799703)
              ·
                rfl

theorem cell22_1396967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 10].length) (baseStart_1396967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396967 prefixEnd_1396967 := by exact prefixLift 1396967
  have htrace : WordTrace (prefixWord ++ tailWord_1396967) baseStart_1396967 baseEnd_1396967 := by
    simpa [prefixWord, tailWord_1396967, baseEnd_1396967] using wordTrace_append hprefix tailTrace_1396967
  have hstable : (prefixWord ++ tailWord_1396967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396967).length < 2 ^ (prefixWord ++ tailWord_1396967).sum := by decide
  have hdescent : baseEnd_1396967 < baseStart_1396967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396973 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1396973 : Nat := 118140960795 + 1396973 * 2 ^ 59
def prefixEnd_1396973 : Nat := 4983230072969 + 3 ^ 40 * 1396973 * 2
def baseEnd_1396973 : Nat := 159404135634104015647321

theorem tailTrace_1396973 : CollatzResearch.WordTrace tailWord_1396973 prefixEnd_1396973 159404135634104015647321 := by
  unfold tailWord_1396973
  simp only [CollatzResearch.WordTrace]
  refine ⟨50951791168012879838867573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33967860778675253225911715 50951791168012879838867573)
  ·
    refine ⟨4776730422001207484893835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50951791168012879838867573 4776730422001207484893835)
    ·
      refine ⟨7165095633001811227340753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776730422001207484893835 7165095633001811227340753)
      ·
        refine ⟨5373821724751358420505565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7165095633001811227340753 5373821724751358420505565)
        ·
          refine ⟨2015183146781759407689587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5373821724751358420505565 2015183146781759407689587)
          ·
            refine ⟨3022774720172639111534381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015183146781759407689587 3022774720172639111534381)
            ·
              refine ⟨1133540520064739666825393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3022774720172639111534381 1133540520064739666825393)
              ·
                refine ⟨850155390048554750119045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133540520064739666825393 850155390048554750119045)
                ·
                  refine ⟨159404135634104015647321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850155390048554750119045 159404135634104015647321)
                  ·
                    rfl

theorem cell22_1396973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1396973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396973 prefixEnd_1396973 := by exact prefixLift 1396973
  have htrace : WordTrace (prefixWord ++ tailWord_1396973) baseStart_1396973 baseEnd_1396973 := by
    simpa [prefixWord, tailWord_1396973, baseEnd_1396973] using wordTrace_append hprefix tailTrace_1396973
  have hstable : (prefixWord ++ tailWord_1396973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396973).length < 2 ^ (prefixWord ++ tailWord_1396973).sum := by decide
  have hdescent : baseEnd_1396973 < baseStart_1396973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396988 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_1396988 : Nat := 118140960795 + 1396988 * 2 ^ 59
def prefixEnd_1396988 : Nat := 4983230072969 + 3 ^ 40 * 1396988 * 2
def baseEnd_1396988 : Nat := 478217541708857007816917

theorem tailTrace_1396988 : CollatzResearch.WordTrace tailWord_1396988 prefixEnd_1396988 478217541708857007816917 := by
  unfold tailWord_1396988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476169131479268700331809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33968225508639024933775745 25476169131479268700331809)
  ·
    refine ⟨19107126848609451525248857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25476169131479268700331809 19107126848609451525248857)
    ·
      refine ⟨14330345136457088643936643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19107126848609451525248857 14330345136457088643936643)
      ·
        refine ⟨21495517704685632965904965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14330345136457088643936643 21495517704685632965904965)
        ·
          refine ⟨4030409569628556181107181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21495517704685632965904965 4030409569628556181107181)
          ·
            refine ⟨1511403588610708567915193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4030409569628556181107181 1511403588610708567915193)
            ·
              refine ⟨1133552691458031425936395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511403588610708567915193 1133552691458031425936395)
              ·
                refine ⟨1700329037187047138904593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133552691458031425936395 1700329037187047138904593)
                ·
                  refine ⟨1275246777890285354178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700329037187047138904593 1275246777890285354178445)
                  ·
                    refine ⟨478217541708857007816917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275246777890285354178445 478217541708857007816917)
                    ·
                      rfl

theorem cell22_1396988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_1396988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1396988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1396988 prefixEnd_1396988 := by exact prefixLift 1396988
  have htrace : WordTrace (prefixWord ++ tailWord_1396988) baseStart_1396988 baseEnd_1396988 := by
    simpa [prefixWord, tailWord_1396988, baseEnd_1396988] using wordTrace_append hprefix tailTrace_1396988
  have hstable : (prefixWord ++ tailWord_1396988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396988).length < 2 ^ (prefixWord ++ tailWord_1396988).sum := by decide
  have hdescent : baseEnd_1396988 < baseStart_1396988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397016 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_1397016 : Nat := 118140960795 + 1397016 * 2 ^ 59
def prefixEnd_1397016 : Nat := 4983230072969 + 3 ^ 40 * 1397016 * 2
def baseEnd_1397016 : Nat := 478227126681074268116831

theorem tailTrace_1397016 : CollatzResearch.WordTrace tailWord_1397016 prefixEnd_1397016 478227126681074268116831 := by
  unfold tailWord_1397016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476679753428549091341451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33968906337904732121788601 25476679753428549091341451)
  ·
    refine ⟨38215019630142823637012177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25476679753428549091341451 38215019630142823637012177)
    ·
      refine ⟨28661264722607117727759133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38215019630142823637012177 28661264722607117727759133)
      ·
        refine ⟨10747974270977669147909675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28661264722607117727759133 10747974270977669147909675)
        ·
          refine ⟨16121961406466503721864513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10747974270977669147909675 16121961406466503721864513)
          ·
            refine ⟨12091471054849877791398385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16121961406466503721864513 12091471054849877791398385)
            ·
              refine ⟨9068603291137408343548789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12091471054849877791398385 9068603291137408343548789)
              ·
                refine ⟨850181558544132032207699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9068603291137408343548789 850181558544132032207699)
                ·
                  refine ⟨1275272337816198048311549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850181558544132032207699 1275272337816198048311549)
                  ·
                    refine ⟨478227126681074268116831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275272337816198048311549 478227126681074268116831)
                    ·
                      rfl

theorem cell22_1397016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_1397016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397016 prefixEnd_1397016 := by exact prefixLift 1397016
  have htrace : WordTrace (prefixWord ++ tailWord_1397016) baseStart_1397016 baseEnd_1397016 := by
    simpa [prefixWord, tailWord_1397016, baseEnd_1397016] using wordTrace_append hprefix tailTrace_1397016
  have hstable : (prefixWord ++ tailWord_1397016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397016).length < 2 ^ (prefixWord ++ tailWord_1397016).sum := by decide
  have hdescent : baseEnd_1397016 < baseStart_1397016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397027 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_1397027 : Nat := 118140960795 + 1397027 * 2 ^ 59
def prefixEnd_1397027 : Nat := 4983230072969 + 3 ^ 40 * 1397027 * 2
def baseEnd_1397027 : Nat := 478230892205873906091797

theorem tailTrace_1397027 : CollatzResearch.WordTrace tailWord_1397027 prefixEnd_1397027 478230892205873906091797 := by
  unfold tailWord_1397027
  simp only [CollatzResearch.WordTrace]
  refine ⟨50953760709817247061333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33969173806544831374222223 50953760709817247061333335)
  ·
    refine ⟨76430641064725870592000003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50953760709817247061333335 76430641064725870592000003)
    ·
      refine ⟨114645961597088805888000005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76430641064725870592000003 114645961597088805888000005)
      ·
        refine ⟨21496117799454151104000001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114645961597088805888000005 21496117799454151104000001)
        ·
          refine ⟨16122088349590613328000001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21496117799454151104000001 16122088349590613328000001)
          ·
            refine ⟨12091566262192959996000001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16122088349590613328000001 12091566262192959996000001)
            ·
              refine ⟨9068674696644719997000001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12091566262192959996000001 9068674696644719997000001)
              ·
                refine ⟨6801506022483539997750001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068674696644719997000001 6801506022483539997750001)
                ·
                  refine ⟨5101129516862654998312501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6801506022483539997750001 5101129516862654998312501)
                  ·
                    refine ⟨478230892205873906091797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5101129516862654998312501 478230892205873906091797)
                    ·
                      rfl

theorem cell22_1397027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_1397027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397027 prefixEnd_1397027 := by exact prefixLift 1397027
  have htrace : WordTrace (prefixWord ++ tailWord_1397027) baseStart_1397027 baseEnd_1397027 := by
    simpa [prefixWord, tailWord_1397027, baseEnd_1397027] using wordTrace_append hprefix tailTrace_1397027
  have hstable : (prefixWord ++ tailWord_1397027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397027).length < 2 ^ (prefixWord ++ tailWord_1397027).sum := by decide
  have hdescent : baseEnd_1397027 < baseStart_1397027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397044 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1397044 : Nat := 118140960795 + 1397044 * 2 ^ 59
def prefixEnd_1397044 : Nat := 4983230072969 + 3 ^ 40 * 1397044 * 2
def baseEnd_1397044 : Nat := 478236711653291528416745

theorem tailTrace_1397044 : CollatzResearch.WordTrace tailWord_1397044 prefixEnd_1397044 478236711653291528416745 := by
  unfold tailWord_1397044
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477190375377829482351093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33969587167170439309801457 25477190375377829482351093)
  ·
    refine ⟨2388486597691671513970415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25477190375377829482351093 2388486597691671513970415)
    ·
      refine ⟨3582729896537507270955623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388486597691671513970415 3582729896537507270955623)
      ·
        refine ⟨5374094844806260906433435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582729896537507270955623 5374094844806260906433435)
        ·
          refine ⟨8061142267209391359650153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374094844806260906433435 8061142267209391359650153)
          ·
            refine ⟨6045856700407043519737615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8061142267209391359650153 6045856700407043519737615)
            ·
              refine ⟨9068785050610565279606423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045856700407043519737615 9068785050610565279606423)
              ·
                refine ⟨13603177575915847919409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9068785050610565279606423 13603177575915847919409635)
                ·
                  refine ⟨20404766363873771879114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13603177575915847919409635 20404766363873771879114453)
                  ·
                    refine ⟨478236711653291528416745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20404766363873771879114453 478236711653291528416745)
                    ·
                      rfl

theorem cell22_1397044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1397044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397044 prefixEnd_1397044 := by exact prefixLift 1397044
  have htrace : WordTrace (prefixWord ++ tailWord_1397044) baseStart_1397044 baseEnd_1397044 := by
    simpa [prefixWord, tailWord_1397044, baseEnd_1397044] using wordTrace_append hprefix tailTrace_1397044
  have hstable : (prefixWord ++ tailWord_1397044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397044).length < 2 ^ (prefixWord ++ tailWord_1397044).sum := by decide
  have hdescent : baseEnd_1397044 < baseStart_1397044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397076 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1397076 : Nat := 118140960795 + 1397076 * 2 ^ 59
def prefixEnd_1397076 : Nat := 4983230072969 + 3 ^ 40 * 1397076 * 2
def baseEnd_1397076 : Nat := 478247665907254111616647

theorem tailTrace_1397076 : CollatzResearch.WordTrace tailWord_1397076 prefixEnd_1397076 478247665907254111616647 := by
  unfold tailWord_1397076
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477773943319864214933541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33970365257759818953244721 25477773943319864214933541)
  ·
    refine ⟨4777082614372474540300039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25477773943319864214933541 4777082614372474540300039)
    ·
      refine ⟨7165623921558711810450059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4777082614372474540300039 7165623921558711810450059)
      ·
        refine ⟨10748435882338067715675089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165623921558711810450059 10748435882338067715675089)
        ·
          refine ⟨8061326911753550786756317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10748435882338067715675089 8061326911753550786756317)
          ·
            refine ⟨3022997591907581545033619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8061326911753550786756317 3022997591907581545033619)
            ·
              refine ⟨4534496387861372317550429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022997591907581545033619 4534496387861372317550429)
              ·
                refine ⟨1700436145448014619081411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534496387861372317550429 1700436145448014619081411)
                ·
                  refine ⟨2550654218172021928622117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700436145448014619081411 2550654218172021928622117)
                  ·
                    refine ⟨478247665907254111616647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550654218172021928622117 478247665907254111616647)
                    ·
                      rfl

theorem cell22_1397076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1397076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397076 prefixEnd_1397076 := by exact prefixLift 1397076
  have htrace : WordTrace (prefixWord ++ tailWord_1397076) baseStart_1397076 baseEnd_1397076 := by
    simpa [prefixWord, tailWord_1397076, baseEnd_1397076] using wordTrace_append hprefix tailTrace_1397076
  have hstable : (prefixWord ++ tailWord_1397076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397076).length < 2 ^ (prefixWord ++ tailWord_1397076).sum := by decide
  have hdescent : baseEnd_1397076 < baseStart_1397076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397106 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1397106 : Nat := 118140960795 + 1397106 * 2 ^ 59
def prefixEnd_1397106 : Nat := 4983230072969 + 3 ^ 40 * 1397106 * 2
def baseEnd_1397106 : Nat := 478257935520344033366555

theorem tailTrace_1397106 : CollatzResearch.WordTrace tailWord_1397106 prefixEnd_1397106 478257935520344033366555 := by
  unfold tailWord_1397106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739160519132760888364793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33971094717687362368972781 12739160519132760888364793)
  ·
    refine ⟨9554370389349570666273595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12739160519132760888364793 9554370389349570666273595)
    ·
      refine ⟨14331555584024355999410393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9554370389349570666273595 14331555584024355999410393)
      ·
        refine ⟨10748666688018266999557795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14331555584024355999410393 10748666688018266999557795)
        ·
          refine ⟨16123000032027400499336693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10748666688018266999557795 16123000032027400499336693)
          ·
            refine ⟨1511531253002568796812815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16123000032027400499336693 1511531253002568796812815)
            ·
              refine ⟨2267296879503853195219223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511531253002568796812815 2267296879503853195219223)
              ·
                refine ⟨3400945319255779792828835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267296879503853195219223 3400945319255779792828835)
                ·
                  refine ⟨5101417978883669689243253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400945319255779792828835 5101417978883669689243253)
                  ·
                    refine ⟨478257935520344033366555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5101417978883669689243253 478257935520344033366555)
                    ·
                      rfl

theorem cell22_1397106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1397106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397106 prefixEnd_1397106 := by exact prefixLift 1397106
  have htrace : WordTrace (prefixWord ++ tailWord_1397106) baseStart_1397106 baseEnd_1397106 := by
    simpa [prefixWord, tailWord_1397106, baseEnd_1397106] using wordTrace_append hprefix tailTrace_1397106
  have hstable : (prefixWord ++ tailWord_1397106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397106).length < 2 ^ (prefixWord ++ tailWord_1397106).sum := by decide
  have hdescent : baseEnd_1397106 < baseStart_1397106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397110 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1397110 : Nat := 118140960795 + 1397110 * 2 ^ 59
def prefixEnd_1397110 : Nat := 4983230072969 + 3 ^ 40 * 1397110 * 2
def baseEnd_1397110 : Nat := 478259304802089356266543

theorem tailTrace_1397110 : CollatzResearch.WordTrace tailWord_1397110 prefixEnd_1397110 478259304802089356266543 := by
  unfold tailWord_1397110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184799248032284514787799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33971191979011034824403189 3184799248032284514787799)
  ·
    refine ⟨4777198872048426772181699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184799248032284514787799 4777198872048426772181699)
    ·
      refine ⟨7165798308072640158272549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4777198872048426772181699 7165798308072640158272549)
      ·
        refine ⟨1343587182763620029676103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7165798308072640158272549 1343587182763620029676103)
        ·
          refine ⟨2015380774145430044514155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343587182763620029676103 2015380774145430044514155)
          ·
            refine ⟨3023071161218145066771233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015380774145430044514155 3023071161218145066771233)
            ·
              refine ⟨2267303370913608800078425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023071161218145066771233 2267303370913608800078425)
              ·
                refine ⟨1700477528185206600058819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267303370913608800078425 1700477528185206600058819)
                ·
                  refine ⟨2550716292277809900088229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700477528185206600058819 2550716292277809900088229)
                  ·
                    refine ⟨478259304802089356266543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2550716292277809900088229 478259304802089356266543)
                    ·
                      rfl

theorem cell22_1397110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1397110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397110 prefixEnd_1397110 := by exact prefixLift 1397110
  have htrace : WordTrace (prefixWord ++ tailWord_1397110) baseStart_1397110 baseEnd_1397110 := by
    simpa [prefixWord, tailWord_1397110, baseEnd_1397110] using wordTrace_append hprefix tailTrace_1397110
  have hstable : (prefixWord ++ tailWord_1397110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397110).length < 2 ^ (prefixWord ++ tailWord_1397110).sum := by decide
  have hdescent : baseEnd_1397110 < baseStart_1397110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397142 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1397142 : Nat := 118140960795 + 1397142 * 2 ^ 59
def prefixEnd_1397142 : Nat := 4983230072969 + 3 ^ 40 * 1397142 * 2
def baseEnd_1397142 : Nat := 159423419685350646488815

theorem tailTrace_1397142 : CollatzResearch.WordTrace tailWord_1397142 prefixEnd_1397142 159423419685350646488815 := by
  unfold tailWord_1397142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184872194025038856360605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33971970069600414467846453 3184872194025038856360605)
  ·
    refine ⟨1194327072759389571135227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3184872194025038856360605 1194327072759389571135227)
    ·
      refine ⟨1791490609139084356702841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194327072759389571135227 1791490609139084356702841)
      ·
        refine ⟨1343617956854313267527131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791490609139084356702841 1343617956854313267527131)
        ·
          refine ⟨2015426935281469901290697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343617956854313267527131 2015426935281469901290697)
          ·
            refine ⟨1511570201461102425968023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015426935281469901290697 1511570201461102425968023)
            ·
              refine ⟨2267355302191653638952035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511570201461102425968023 2267355302191653638952035)
              ·
                refine ⟨3401032953287480458428053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267355302191653638952035 3401032953287480458428053)
                ·
                  refine ⟨159423419685350646488815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3401032953287480458428053 159423419685350646488815)
                  ·
                    rfl

theorem cell22_1397142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1397142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397142 prefixEnd_1397142 := by exact prefixLift 1397142
  have htrace : WordTrace (prefixWord ++ tailWord_1397142) baseStart_1397142 baseEnd_1397142 := by
    simpa [prefixWord, tailWord_1397142, baseEnd_1397142] using wordTrace_append hprefix tailTrace_1397142
  have hstable : (prefixWord ++ tailWord_1397142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397142).length < 2 ^ (prefixWord ++ tailWord_1397142).sum := by decide
  have hdescent : baseEnd_1397142 < baseStart_1397142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397202 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1397202 : Nat := 118140960795 + 1397202 * 2 ^ 59
def prefixEnd_1397202 : Nat := 4983230072969 + 3 ^ 40 * 1397202 * 2
def baseEnd_1397202 : Nat := 478290798282231782966261

theorem tailTrace_1397202 : CollatzResearch.WordTrace tailWord_1397202 prefixEnd_1397202 478290798282231782966261 := by
  unfold tailWord_1397202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740035871045812987238465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33973428989455501299302573 12740035871045812987238465)
  ·
    refine ⟨9555026903284359740428849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12740035871045812987238465 9555026903284359740428849)
    ·
      refine ⟨7166270177463269805321637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9555026903284359740428849 7166270177463269805321637)
      ·
        refine ⟨1343675658274363088497807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7166270177463269805321637 1343675658274363088497807)
        ·
          refine ⟨2015513487411544632746711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343675658274363088497807 2015513487411544632746711)
          ·
            refine ⟨3023270231117316949120067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015513487411544632746711 3023270231117316949120067)
            ·
              refine ⟨4534905346675975423680101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023270231117316949120067 4534905346675975423680101)
              ·
                refine ⟨850294752501745391940019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4534905346675975423680101 850294752501745391940019)
                ·
                  refine ⟨1275442128752618087910029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850294752501745391940019 1275442128752618087910029)
                  ·
                    refine ⟨478290798282231782966261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275442128752618087910029 478290798282231782966261)
                    ·
                      rfl

theorem cell22_1397202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1397202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397202 prefixEnd_1397202 := by exact prefixLift 1397202
  have htrace : WordTrace (prefixWord ++ tailWord_1397202) baseStart_1397202 baseEnd_1397202 := by
    simpa [prefixWord, tailWord_1397202, baseEnd_1397202] using wordTrace_append hprefix tailTrace_1397202
  have hstable : (prefixWord ++ tailWord_1397202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397202).length < 2 ^ (prefixWord ++ tailWord_1397202).sum := by decide
  have hdescent : baseEnd_1397202 < baseStart_1397202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397209 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 6]
def baseStart_1397209 : Nat := 118140960795 + 1397209 * 2 ^ 59
def prefixEnd_1397209 : Nat := 4983230072969 + 3 ^ 40 * 1397209 * 2
def baseEnd_1397209 : Nat := 159431064841762032680413

theorem tailTrace_1397209 : CollatzResearch.WordTrace tailWord_1397209 prefixEnd_1397209 159431064841762032680413 := by
  unfold tailWord_1397209
  simp only [CollatzResearch.WordTrace]
  refine ⟨50960398795157892144458681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33973599196771928096305787 50960398795157892144458681)
  ·
    refine ⟨38220299096368419108344011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50960398795157892144458681 38220299096368419108344011)
    ·
      refine ⟨57330448644552628662516017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38220299096368419108344011 57330448644552628662516017)
      ·
        refine ⟨42997836483414471496887013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57330448644552628662516017 42997836483414471496887013)
        ·
          refine ⟨8062094340640213405666315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42997836483414471496887013 8062094340640213405666315)
          ·
            refine ⟨12093141510960320108499473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062094340640213405666315 12093141510960320108499473)
            ·
              refine ⟨9069856133220240081374605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12093141510960320108499473 9069856133220240081374605)
              ·
                refine ⟨3401196049957590030515477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9069856133220240081374605 3401196049957590030515477)
                ·
                  refine ⟨159431064841762032680413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3401196049957590030515477 159431064841762032680413)
                  ·
                    rfl

theorem cell22_1397209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_1397209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397209 prefixEnd_1397209 := by exact prefixLift 1397209
  have htrace : WordTrace (prefixWord ++ tailWord_1397209) baseStart_1397209 baseEnd_1397209 := by
    simpa [prefixWord, tailWord_1397209, baseEnd_1397209] using wordTrace_append hprefix tailTrace_1397209
  have hstable : (prefixWord ++ tailWord_1397209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397209).length < 2 ^ (prefixWord ++ tailWord_1397209).sum := by decide
  have hdescent : baseEnd_1397209 < baseStart_1397209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397226 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_1397226 : Nat := 118140960795 + 1397226 * 2 ^ 59
def prefixEnd_1397226 : Nat := 4983230072969 + 3 ^ 40 * 1397226 * 2
def baseEnd_1397226 : Nat := 159433004657567906788729

theorem tailTrace_1397226 : CollatzResearch.WordTrace tailWord_1397226 prefixEnd_1397226 159433004657567906788729 := by
  unfold tailWord_1397226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740254709024076011956883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33974012557397536031885021 12740254709024076011956883)
  ·
    refine ⟨19110382063536114017935325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12740254709024076011956883 19110382063536114017935325)
    ·
      refine ⟨7166393273826042756725747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19110382063536114017935325 7166393273826042756725747)
      ·
        refine ⟨10749589910739064135088621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7166393273826042756725747 10749589910739064135088621)
        ·
          refine ⟨4031096216527149050658233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10749589910739064135088621 4031096216527149050658233)
          ·
            refine ⟨3023322162395361787993675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031096216527149050658233 3023322162395361787993675)
            ·
              refine ⟨4534983243593042681990513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023322162395361787993675 4534983243593042681990513)
              ·
                refine ⟨3401237432694782011492885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4534983243593042681990513 3401237432694782011492885)
                ·
                  refine ⟨159433004657567906788729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3401237432694782011492885 159433004657567906788729)
                  ·
                    rfl

theorem cell22_1397226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_1397226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397226 prefixEnd_1397226 := by exact prefixLift 1397226
  have htrace : WordTrace (prefixWord ++ tailWord_1397226) baseStart_1397226 baseEnd_1397226 := by
    simpa [prefixWord, tailWord_1397226, baseEnd_1397226] using wordTrace_append hprefix tailTrace_1397226
  have hstable : (prefixWord ++ tailWord_1397226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397226).length < 2 ^ (prefixWord ++ tailWord_1397226).sum := by decide
  have hdescent : baseEnd_1397226 < baseStart_1397226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397288 : List Nat := [2, 1, 5, 2, 1, 1, 4, 6]
def baseStart_1397288 : Nat := 118140960795 + 1397288 * 2 ^ 59
def prefixEnd_1397288 : Nat := 4983230072969 + 3 ^ 40 * 1397288 * 2
def baseEnd_1397288 : Nat := 53146693093306247257333

theorem tailTrace_1397288 : CollatzResearch.WordTrace tailWord_1397288 prefixEnd_1397288 53146693093306247257333 := by
  unfold tailWord_1397288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481640080935844318292259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33975520107914459091056345 25481640080935844318292259)
  ·
    refine ⟨38222460121403766477438389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25481640080935844318292259 38222460121403766477438389)
    ·
      refine ⟨3583355636381603107259849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38222460121403766477438389 3583355636381603107259849)
      ·
        refine ⟨2687516727286202330444887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583355636381603107259849 2687516727286202330444887)
        ·
          refine ⟨4031275090929303495667331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687516727286202330444887 4031275090929303495667331)
          ·
            refine ⟨6046912636393955243500997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031275090929303495667331 6046912636393955243500997)
            ·
              refine ⟨1133796119323866608156437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6046912636393955243500997 1133796119323866608156437)
              ·
                refine ⟨53146693093306247257333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1133796119323866608156437 53146693093306247257333)
                ·
                  rfl

theorem cell22_1397288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_1397288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397288 prefixEnd_1397288 := by exact prefixLift 1397288
  have htrace : WordTrace (prefixWord ++ tailWord_1397288) baseStart_1397288 baseEnd_1397288 := by
    simpa [prefixWord, tailWord_1397288, baseEnd_1397288] using wordTrace_append hprefix tailTrace_1397288
  have hstable : (prefixWord ++ tailWord_1397288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397288).length < 2 ^ (prefixWord ++ tailWord_1397288).sum := by decide
  have hdescent : baseEnd_1397288 < baseStart_1397288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397299 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 9]
def baseStart_1397299 : Nat := 118140960795 + 1397299 * 2 ^ 59
def prefixEnd_1397299 : Nat := 4983230072969 + 3 ^ 40 * 1397299 * 2
def baseEnd_1397299 : Nat := 159441334454851954430321

theorem tailTrace_1397299 : CollatzResearch.WordTrace tailWord_1397299 prefixEnd_1397299 159441334454851954430321 := by
  unfold tailWord_1397299
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963681364831837515234951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33975787576554558343489967 50963681364831837515234951)
  ·
    refine ⟨76445522047247756272852427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50963681364831837515234951 76445522047247756272852427)
    ·
      refine ⟨114668283070871634409278641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76445522047247756272852427 114668283070871634409278641)
      ·
        refine ⟨86001212303153725806958981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114668283070871634409278641 86001212303153725806958981)
        ·
          refine ⟨16125227306841323588804809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86001212303153725806958981 16125227306841323588804809)
          ·
            refine ⟨12093920480130992691603607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16125227306841323588804809 12093920480130992691603607)
            ·
              refine ⟨18140880720196489037405411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093920480130992691603607 18140880720196489037405411)
              ·
                refine ⟨27211321080294733556108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18140880720196489037405411 27211321080294733556108117)
                ·
                  refine ⟨159441334454851954430321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27211321080294733556108117 159441334454851954430321)
                  ·
                    rfl

theorem cell22_1397299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_1397299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397299 prefixEnd_1397299 := by exact prefixLift 1397299
  have htrace : WordTrace (prefixWord ++ tailWord_1397299) baseStart_1397299 baseEnd_1397299 := by
    simpa [prefixWord, tailWord_1397299, baseEnd_1397299] using wordTrace_append hprefix tailTrace_1397299
  have hstable : (prefixWord ++ tailWord_1397299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397299).length < 2 ^ (prefixWord ++ tailWord_1397299).sum := by decide
  have hdescent : baseEnd_1397299 < baseStart_1397299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397333 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 5]
def baseStart_1397333 : Nat := 118140960795 + 1397333 * 2 ^ 59
def prefixEnd_1397333 : Nat := 4983230072969 + 3 ^ 40 * 1397333 * 2
def baseEnd_1397333 : Nat := 159445214086463702646953

theorem tailTrace_1397333 : CollatzResearch.WordTrace tailWord_1397333 prefixEnd_1397333 159445214086463702646953 := by
  unfold tailWord_1397333
  simp only [CollatzResearch.WordTrace]
  refine ⟨50964921446708661321972653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33976614297805774214648435 50964921446708661321972653)
  ·
    refine ⟨19111845542515747995739745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50964921446708661321972653 19111845542515747995739745)
    ·
      refine ⟨14333884156886810996804809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19111845542515747995739745 14333884156886810996804809)
      ·
        refine ⟨10750413117665108247603607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14333884156886810996804809 10750413117665108247603607)
        ·
          refine ⟨16125619676497662371405411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10750413117665108247603607 16125619676497662371405411)
          ·
            refine ⟨24188429514746493557108117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16125619676497662371405411 24188429514746493557108117)
            ·
              refine ⟨1133832633503741885489443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24188429514746493557108117 1133832633503741885489443)
              ·
                refine ⟨1700748950255612828234165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133832633503741885489443 1700748950255612828234165)
                ·
                  refine ⟨159445214086463702646953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700748950255612828234165 159445214086463702646953)
                  ·
                    rfl

theorem cell22_1397333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_1397333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397333 prefixEnd_1397333 := by exact prefixLift 1397333
  have htrace : WordTrace (prefixWord ++ tailWord_1397333) baseStart_1397333 baseEnd_1397333 := by
    simpa [prefixWord, tailWord_1397333, baseEnd_1397333] using wordTrace_append hprefix tailTrace_1397333
  have hstable : (prefixWord ++ tailWord_1397333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397333).length < 2 ^ (prefixWord ++ tailWord_1397333).sum := by decide
  have hdescent : baseEnd_1397333 < baseStart_1397333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397408 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_1397408 : Nat := 118140960795 + 1397408 * 2 ^ 59
def prefixEnd_1397408 : Nat := 4983230072969 + 3 ^ 40 * 1397408 * 2
def baseEnd_1397408 : Nat := 478361316292115912315629

theorem tailTrace_1397408 : CollatzResearch.WordTrace tailWord_1397408 prefixEnd_1397408 478361316292115912315629 := by
  unfold tailWord_1397408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483828460718474565476439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33978437947624632753968585 25483828460718474565476439)
  ·
    refine ⟨38225742691077711848214659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25483828460718474565476439 38225742691077711848214659)
    ·
      refine ⟨57338614036616567772321989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38225742691077711848214659 57338614036616567772321989)
      ·
        refine ⟨10750990131865606457310373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57338614036616567772321989 10750990131865606457310373)
        ·
          refine ⟨2015810649724801210745695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10750990131865606457310373 2015810649724801210745695)
          ·
            refine ⟨3023715974587201816118543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015810649724801210745695 3023715974587201816118543)
            ·
              refine ⟨4535573961880802724177815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023715974587201816118543 4535573961880802724177815)
              ·
                refine ⟨6803360942821204086266723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535573961880802724177815 6803360942821204086266723)
                ·
                  refine ⟨10205041414231806129400085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6803360942821204086266723 10205041414231806129400085)
                  ·
                    refine ⟨478361316292115912315629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10205041414231806129400085 478361316292115912315629)
                    ·
                      rfl

theorem cell22_1397408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_1397408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397408 prefixEnd_1397408 := by exact prefixLift 1397408
  have htrace : WordTrace (prefixWord ++ tailWord_1397408) baseStart_1397408 baseEnd_1397408 := by
    simpa [prefixWord, tailWord_1397408, baseEnd_1397408] using wordTrace_append hprefix tailTrace_1397408
  have hstable : (prefixWord ++ tailWord_1397408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397408).length < 2 ^ (prefixWord ++ tailWord_1397408).sum := by decide
  have hdescent : baseEnd_1397408 < baseStart_1397408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397502 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1397502 : Nat := 118140960795 + 1397502 * 2 ^ 59
def prefixEnd_1397502 : Nat := 4983230072969 + 3 ^ 40 * 1397502 * 2
def baseEnd_1397502 : Nat := 159464498137710333488447

theorem tailTrace_1397502 : CollatzResearch.WordTrace tailWord_1397502 prefixEnd_1397502 159464498137710333488447 := by
  unfold tailWord_1397502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6371385672887050398109345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33980723588730935456583173 6371385672887050398109345)
  ·
    refine ⟨4778539254665287798582009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6371385672887050398109345 4778539254665287798582009)
    ·
      refine ⟨3583904440998965848936507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4778539254665287798582009 3583904440998965848936507)
      ·
        refine ⟨5375856661498448773404761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583904440998965848936507 5375856661498448773404761)
        ·
          refine ⟨4031892496123836580053571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5375856661498448773404761 4031892496123836580053571)
          ·
            refine ⟨6047838744185754870080357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031892496123836580053571 6047838744185754870080357)
            ·
              refine ⟨1133969764534829038140067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6047838744185754870080357 1133969764534829038140067)
              ·
                refine ⟨1700954646802243557210101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133969764534829038140067 1700954646802243557210101)
                ·
                  refine ⟨159464498137710333488447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700954646802243557210101 159464498137710333488447)
                  ·
                    rfl

theorem cell22_1397502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1397502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397502 prefixEnd_1397502 := by exact prefixLift 1397502
  have htrace : WordTrace (prefixWord ++ tailWord_1397502) baseStart_1397502 baseEnd_1397502 := by
    simpa [prefixWord, tailWord_1397502, baseEnd_1397502] using wordTrace_append hprefix tailTrace_1397502
  have hstable : (prefixWord ++ tailWord_1397502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397502).length < 2 ^ (prefixWord ++ tailWord_1397502).sum := by decide
  have hdescent : baseEnd_1397502 < baseStart_1397502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397530 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_1397530 : Nat := 118140960795 + 1397530 * 2 ^ 59
def prefixEnd_1397530 : Nat := 4983230072969 + 3 ^ 40 * 1397530 * 2
def baseEnd_1397530 : Nat := 159467693128449420255085

theorem tailTrace_1397530 : CollatzResearch.WordTrace tailWord_1397530 prefixEnd_1397530 159467693128449420255085 := by
  unfold tailWord_1397530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743026656748740991723511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33981404417996642644596029 12743026656748740991723511)
  ·
    refine ⟨19114539985123111487585267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12743026656748740991723511 19114539985123111487585267)
    ·
      refine ⟨28671809977684667231377901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19114539985123111487585267 28671809977684667231377901)
      ·
        refine ⟨10751928741631750211766713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28671809977684667231377901 10751928741631750211766713)
        ·
          refine ⟨8063946556223812658825035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10751928741631750211766713 8063946556223812658825035)
          ·
            refine ⟨12095919834335718988237553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063946556223812658825035 12095919834335718988237553)
            ·
              refine ⟨9071939875751789241178165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12095919834335718988237553 9071939875751789241178165)
              ·
                refine ⟨850494363351730241360453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9071939875751789241178165 850494363351730241360453)
                ·
                  refine ⟨159467693128449420255085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850494363351730241360453 159467693128449420255085)
                  ·
                    rfl

theorem cell22_1397530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_1397530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397530 prefixEnd_1397530 := by exact prefixLift 1397530
  have htrace : WordTrace (prefixWord ++ tailWord_1397530) baseStart_1397530 baseEnd_1397530 := by
    simpa [prefixWord, tailWord_1397530, baseEnd_1397530] using wordTrace_append hprefix tailTrace_1397530
  have hstable : (prefixWord ++ tailWord_1397530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397530).length < 2 ^ (prefixWord ++ tailWord_1397530).sum := by decide
  have hdescent : baseEnd_1397530 < baseStart_1397530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397532 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_1397532 : Nat := 118140960795 + 1397532 * 2 ^ 59
def prefixEnd_1397532 : Nat := 4983230072969 + 3 ^ 40 * 1397532 * 2
def baseEnd_1397532 : Nat := 478403764026220922215249

theorem tailTrace_1397532 : CollatzResearch.WordTrace tailWord_1397532 prefixEnd_1397532 478403764026220922215249 := by
  unfold tailWord_1397532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25486089786493859154233425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33981453048658478872311233 25486089786493859154233425)
  ·
    refine ⟨19114567339870394365675069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25486089786493859154233425 19114567339870394365675069)
    ·
      refine ⟨7167962752451397887128151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19114567339870394365675069 7167962752451397887128151)
      ·
        refine ⟨10751944128677096830692227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7167962752451397887128151 10751944128677096830692227)
        ·
          refine ⟨16127916193015645246038341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10751944128677096830692227 16127916193015645246038341)
          ·
            refine ⟨3023984286190433483632189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16127916193015645246038341 3023984286190433483632189)
            ·
              refine ⟨1133994107321412556362071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3023984286190433483632189 1133994107321412556362071)
              ·
                refine ⟨1700991160982118834543107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133994107321412556362071 1700991160982118834543107)
                ·
                  refine ⟨2551486741473178251814661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700991160982118834543107 2551486741473178251814661)
                  ·
                    refine ⟨478403764026220922215249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551486741473178251814661 478403764026220922215249)
                    ·
                      rfl

theorem cell22_1397532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_1397532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397532 prefixEnd_1397532 := by exact prefixLift 1397532
  have htrace : WordTrace (prefixWord ++ tailWord_1397532) baseStart_1397532 baseEnd_1397532 := by
    simpa [prefixWord, tailWord_1397532, baseEnd_1397532] using wordTrace_append hprefix tailTrace_1397532
  have hstable : (prefixWord ++ tailWord_1397532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397532).length < 2 ^ (prefixWord ++ tailWord_1397532).sum := by decide
  have hdescent : baseEnd_1397532 < baseStart_1397532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397607 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1397607 : Nat := 118140960795 + 1397607 * 2 ^ 59
def prefixEnd_1397607 : Nat := 4983230072969 + 3 ^ 40 * 1397607 * 2
def baseEnd_1397607 : Nat := 478429438058945726590019

theorem tailTrace_1397607 : CollatzResearch.WordTrace tailWord_1397607 prefixEnd_1397607 478429438058945726590019 := by
  unfold tailWord_1397607
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974915047716006117447075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33983276698477337411631383 50974915047716006117447075)
  ·
    refine ⟨76462372571574009176170613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50974915047716006117447075 76462372571574009176170613)
    ·
      refine ⟨7168347428585063360265995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76462372571574009176170613 7168347428585063360265995)
      ·
        refine ⟨10752521142877595040398993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168347428585063360265995 10752521142877595040398993)
        ·
          refine ⟨8064390857158196280299245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10752521142877595040398993 8064390857158196280299245)
          ·
            refine ⟨3024146571434323605112217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8064390857158196280299245 3024146571434323605112217)
            ·
              refine ⟨2268109928575742703834163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024146571434323605112217 2268109928575742703834163)
              ·
                refine ⟨3402164892863614055751245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268109928575742703834163 3402164892863614055751245)
                ·
                  refine ⟨1275811834823855270906717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3402164892863614055751245 1275811834823855270906717)
                  ·
                    refine ⟨478429438058945726590019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275811834823855270906717 478429438058945726590019)
                    ·
                      rfl

theorem cell22_1397607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1397607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397607 prefixEnd_1397607 := by exact prefixLift 1397607
  have htrace : WordTrace (prefixWord ++ tailWord_1397607) baseStart_1397607 baseEnd_1397607 := by
    simpa [prefixWord, tailWord_1397607, baseEnd_1397607] using wordTrace_append hprefix tailTrace_1397607
  have hstable : (prefixWord ++ tailWord_1397607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397607).length < 2 ^ (prefixWord ++ tailWord_1397607).sum := by decide
  have hdescent : baseEnd_1397607 < baseStart_1397607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397654 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1397654 : Nat := 118140960795 + 1397654 * 2 ^ 59
def prefixEnd_1397654 : Nat := 4983230072969 + 3 ^ 40 * 1397654 * 2
def baseEnd_1397654 : Nat := 159481842373151090221625

theorem tailTrace_1397654 : CollatzResearch.WordTrace tailWord_1397654 prefixEnd_1397654 159481842373151090221625 := by
  unfold tailWord_1397654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186039329909108321525501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33984419519030488762938677 3186039329909108321525501)
  ·
    refine ⟨1194764748715915620572063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3186039329909108321525501 1194764748715915620572063)
    ·
      refine ⟨1792147123073873430858095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194764748715915620572063 1792147123073873430858095)
      ·
        refine ⟨2688220684610810146287143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792147123073873430858095 2688220684610810146287143)
        ·
          refine ⟨4032331026916215219430715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688220684610810146287143 4032331026916215219430715)
          ·
            refine ⟨6048496540374322829146073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032331026916215219430715 6048496540374322829146073)
            ·
              refine ⟨4536372405280742121859555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048496540374322829146073 4536372405280742121859555)
              ·
                refine ⟨6804558607921113182789333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536372405280742121859555 6804558607921113182789333)
                ·
                  refine ⟨159481842373151090221625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6804558607921113182789333 159481842373151090221625)
                  ·
                    rfl

theorem cell22_1397654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1397654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397654 prefixEnd_1397654 := by exact prefixLift 1397654
  have htrace : WordTrace (prefixWord ++ tailWord_1397654) baseStart_1397654 baseEnd_1397654 := by
    simpa [prefixWord, tailWord_1397654, baseEnd_1397654] using wordTrace_append hprefix tailTrace_1397654
  have hstable : (prefixWord ++ tailWord_1397654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397654).length < 2 ^ (prefixWord ++ tailWord_1397654).sum := by decide
  have hdescent : baseEnd_1397654 < baseStart_1397654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397671 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 5]
def baseStart_1397671 : Nat := 118140960795 + 1397671 * 2 ^ 59
def prefixEnd_1397671 : Nat := 4983230072969 + 3 ^ 40 * 1397671 * 2
def baseEnd_1397671 : Nat := 159483782188956964329941

theorem tailTrace_1397671 : CollatzResearch.WordTrace tailWord_1397671 prefixEnd_1397671 159483782188956964329941 := by
  unfold tailWord_1397671
  simp only [CollatzResearch.WordTrace]
  refine ⟨50977249319484145047776867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33984832879656096698517911 50977249319484145047776867)
  ·
    refine ⟨76465873979226217571665301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50977249319484145047776867 76465873979226217571665301)
    ·
      refine ⟨3584337842776228948671811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76465873979226217571665301 3584337842776228948671811)
      ·
        refine ⟨5376506764164343423007717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584337842776228948671811 5376506764164343423007717)
        ·
          refine ⟨1008095018280814391813947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5376506764164343423007717 1008095018280814391813947)
          ·
            refine ⟨1512142527421221587720921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008095018280814391813947 1512142527421221587720921)
            ·
              refine ⟨1134106895565916190790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512142527421221587720921 1134106895565916190790691)
              ·
                refine ⟨1701160343348874286186037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134106895565916190790691 1701160343348874286186037)
                ·
                  refine ⟨159483782188956964329941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701160343348874286186037 159483782188956964329941)
                  ·
                    rfl

theorem cell22_1397671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 5].length) (baseStart_1397671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397671 prefixEnd_1397671 := by exact prefixLift 1397671
  have htrace : WordTrace (prefixWord ++ tailWord_1397671) baseStart_1397671 baseEnd_1397671 := by
    simpa [prefixWord, tailWord_1397671, baseEnd_1397671] using wordTrace_append hprefix tailTrace_1397671
  have hstable : (prefixWord ++ tailWord_1397671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397671).length < 2 ^ (prefixWord ++ tailWord_1397671).sum := by decide
  have hdescent : baseEnd_1397671 < baseStart_1397671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397684 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1397684 : Nat := 118140960795 + 1397684 * 2 ^ 59
def prefixEnd_1397684 : Nat := 4983230072969 + 3 ^ 40 * 1397684 * 2
def baseEnd_1397684 : Nat := 478455796732543192414783

theorem tailTrace_1397684 : CollatzResearch.WordTrace tailWord_1397684 prefixEnd_1397684 478455796732543192414783 := by
  unfold tailWord_1397684
  simp only [CollatzResearch.WordTrace]
  refine ⟨25488861734218524134000053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33985148978958032178666737 25488861734218524134000053)
  ·
    refine ⟨2389580787582986637562505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25488861734218524134000053 2389580787582986637562505)
    ·
      refine ⟨1792185590687239978171879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2389580787582986637562505 1792185590687239978171879)
      ·
        refine ⟨2688278386030859967257819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792185590687239978171879 2688278386030859967257819)
        ·
          refine ⟨4032417579046289950886729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688278386030859967257819 4032417579046289950886729)
          ·
            refine ⟨3024313184284717463165047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4032417579046289950886729 3024313184284717463165047)
            ·
              refine ⟨4536469776427076194747571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024313184284717463165047 4536469776427076194747571)
              ·
                refine ⟨6804704664640614292121357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536469776427076194747571 6804704664640614292121357)
                ·
                  refine ⟨2551764249240230359545509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6804704664640614292121357 2551764249240230359545509)
                  ·
                    refine ⟨478455796732543192414783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551764249240230359545509 478455796732543192414783)
                    ·
                      rfl

theorem cell22_1397684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1397684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397684 prefixEnd_1397684 := by exact prefixLift 1397684
  have htrace : WordTrace (prefixWord ++ tailWord_1397684) baseStart_1397684 baseEnd_1397684 := by
    simpa [prefixWord, tailWord_1397684, baseEnd_1397684] using wordTrace_append hprefix tailTrace_1397684
  have hstable : (prefixWord ++ tailWord_1397684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397684).length < 2 ^ (prefixWord ++ tailWord_1397684).sum := by decide
  have hdescent : baseEnd_1397684 < baseStart_1397684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397709 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1397709 : Nat := 118140960795 + 1397709 * 2 ^ 59
def prefixEnd_1397709 : Nat := 4983230072969 + 3 ^ 40 * 1397709 * 2
def baseEnd_1397709 : Nat := 478464354743451460539707

theorem tailTrace_1397709 : CollatzResearch.WordTrace tailWord_1397709 prefixEnd_1397709 478464354743451460539707 := by
  unfold tailWord_1397709
  simp only [CollatzResearch.WordTrace]
  refine ⟨50978635293346477537660181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33985756862230985025106787 50978635293346477537660181)
  ·
    refine ⟨2389623529375616134577821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50978635293346477537660181 2389623529375616134577821)
    ·
      refine ⟨896108823515856050466683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2389623529375616134577821 896108823515856050466683)
      ·
        refine ⟨1344163235273784075700025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896108823515856050466683 1344163235273784075700025)
        ·
          refine ⟨1008122426455338056775019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1344163235273784075700025 1008122426455338056775019)
          ·
            refine ⟨1512183639683007085162529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008122426455338056775019 1512183639683007085162529)
            ·
              refine ⟨1134137729762255313871897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512183639683007085162529 1134137729762255313871897)
              ·
                refine ⟨850603297321691485403923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134137729762255313871897 850603297321691485403923)
                ·
                  refine ⟨1275904945982537228105885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850603297321691485403923 1275904945982537228105885)
                  ·
                    refine ⟨478464354743451460539707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275904945982537228105885 478464354743451460539707)
                    ·
                      rfl

theorem cell22_1397709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1397709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397709 prefixEnd_1397709 := by exact prefixLift 1397709
  have htrace : WordTrace (prefixWord ++ tailWord_1397709) baseStart_1397709 baseEnd_1397709 := by
    simpa [prefixWord, tailWord_1397709, baseEnd_1397709] using wordTrace_append hprefix tailTrace_1397709
  have hstable : (prefixWord ++ tailWord_1397709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397709).length < 2 ^ (prefixWord ++ tailWord_1397709).sum := by decide
  have hdescent : baseEnd_1397709 < baseStart_1397709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397714 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1397714 : Nat := 118140960795 + 1397714 * 2 ^ 59
def prefixEnd_1397714 : Nat := 4983230072969 + 3 ^ 40 * 1397714 * 2
def baseEnd_1397714 : Nat := 478466066345633114164691

theorem tailTrace_1397714 : CollatzResearch.WordTrace tailWord_1397714 prefixEnd_1397714 478466066345633114164691 := by
  unfold tailWord_1397714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744704414582090847898049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33985878438885575594394797 12744704414582090847898049)
  ·
    refine ⟨9558528310936568135923537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12744704414582090847898049 9558528310936568135923537)
    ·
      refine ⟨7168896233202426101942653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9558528310936568135923537 7168896233202426101942653)
      ·
        refine ⟨2688336087450909788228495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7168896233202426101942653 2688336087450909788228495)
        ·
          refine ⟨4032504131176364682342743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688336087450909788228495 4032504131176364682342743)
          ·
            refine ⟨6048756196764547023514115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032504131176364682342743 6048756196764547023514115)
            ·
              refine ⟨9073134295146820535271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048756196764547023514115 9073134295146820535271173)
              ·
                refine ⟨1701212680340028850363345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9073134295146820535271173 1701212680340028850363345)
                ·
                  refine ⟨1275909510255021637772509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1701212680340028850363345 1275909510255021637772509)
                  ·
                    refine ⟨478466066345633114164691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1275909510255021637772509 478466066345633114164691)
                    ·
                      rfl

theorem cell22_1397714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1397714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397714 prefixEnd_1397714 := by exact prefixLift 1397714
  have htrace : WordTrace (prefixWord ++ tailWord_1397714) baseStart_1397714 baseEnd_1397714 := by
    simpa [prefixWord, tailWord_1397714, baseEnd_1397714] using wordTrace_append hprefix tailTrace_1397714
  have hstable : (prefixWord ++ tailWord_1397714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397714).length < 2 ^ (prefixWord ++ tailWord_1397714).sum := by decide
  have hdescent : baseEnd_1397714 < baseStart_1397714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397716 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1397716 : Nat := 118140960795 + 1397716 * 2 ^ 59
def prefixEnd_1397716 : Nat := 4983230072969 + 3 ^ 40 * 1397716 * 2
def baseEnd_1397716 : Nat := 159488916995501925204895

theorem tailTrace_1397716 : CollatzResearch.WordTrace tailWord_1397716 prefixEnd_1397716 159488916995501925204895 := by
  unfold tailWord_1397716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489445302160558866582501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33985927069547411822110001 25489445302160558866582501)
  ·
    refine ⟨4779270994155104787484219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25489445302160558866582501 4779270994155104787484219)
    ·
      refine ⟨7168906491232657181226329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779270994155104787484219 7168906491232657181226329)
      ·
        refine ⟨5376679868424492885919747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168906491232657181226329 5376679868424492885919747)
        ·
          refine ⟨8065019802636739328879621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376679868424492885919747 8065019802636739328879621)
          ·
            refine ⟨1512191212994388624164929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8065019802636739328879621 1512191212994388624164929)
            ·
              refine ⟨1134143409745791468123697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512191212994388624164929 1134143409745791468123697)
              ·
                refine ⟨850607557309343601092773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134143409745791468123697 850607557309343601092773)
                ·
                  refine ⟨159488916995501925204895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850607557309343601092773 159488916995501925204895)
                  ·
                    rfl

theorem cell22_1397716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1397716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397716 prefixEnd_1397716 := by exact prefixLift 1397716
  have htrace : WordTrace (prefixWord ++ tailWord_1397716) baseStart_1397716 baseEnd_1397716 := by
    simpa [prefixWord, tailWord_1397716, baseEnd_1397716] using wordTrace_append hprefix tailTrace_1397716
  have hstable : (prefixWord ++ tailWord_1397716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397716).length < 2 ^ (prefixWord ++ tailWord_1397716).sum := by decide
  have hdescent : baseEnd_1397716 < baseStart_1397716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397727 : List Nat := [1, 1, 2, 3, 5, 2, 1, 7]
def baseStart_1397727 : Nat := 118140960795 + 1397727 * 2 ^ 59
def prefixEnd_1397727 : Nat := 4983230072969 + 3 ^ 40 * 1397727 * 2
def baseEnd_1397727 : Nat := 53163390723478379287739

theorem tailTrace_1397727 : CollatzResearch.WordTrace tailWord_1397727 prefixEnd_1397727 53163390723478379287739 := by
  unfold tailWord_1397727
  simp only [CollatzResearch.WordTrace]
  refine ⟨50979291807281266611815435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33986194538187511074543623 50979291807281266611815435)
  ·
    refine ⟨76468937710921899917723153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50979291807281266611815435 76468937710921899917723153)
    ·
      refine ⟨57351703283191424938292365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76468937710921899917723153 57351703283191424938292365)
      ·
        refine ⟨21506888731196784351859637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57351703283191424938292365 21506888731196784351859637)
        ·
          refine ⟨2016270818549698532986841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21506888731196784351859637 2016270818549698532986841)
          ·
            refine ⟨1512203113912273899740131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016270818549698532986841 1512203113912273899740131)
            ·
              refine ⟨2268304670868410849610197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512203113912273899740131 2268304670868410849610197)
              ·
                refine ⟨53163390723478379287739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2268304670868410849610197 53163390723478379287739)
                ·
                  rfl

theorem cell22_1397727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 7].length) (baseStart_1397727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397727 prefixEnd_1397727 := by exact prefixLift 1397727
  have htrace : WordTrace (prefixWord ++ tailWord_1397727) baseStart_1397727 baseEnd_1397727 := by
    simpa [prefixWord, tailWord_1397727, baseEnd_1397727] using wordTrace_append hprefix tailTrace_1397727
  have hstable : (prefixWord ++ tailWord_1397727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397727).length < 2 ^ (prefixWord ++ tailWord_1397727).sum := by decide
  have hdescent : baseEnd_1397727 < baseStart_1397727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397746 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_1397746 : Nat := 118140960795 + 1397746 * 2 ^ 59
def prefixEnd_1397746 : Nat := 4983230072969 + 3 ^ 40 * 1397746 * 2
def baseEnd_1397746 : Nat := 478477020599595697364593

theorem tailTrace_1397746 : CollatzResearch.WordTrace tailWord_1397746 prefixEnd_1397746 478477020599595697364593 := by
  unfold tailWord_1397746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744996198553108214189273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33986656529474955237838061 12744996198553108214189273)
  ·
    refine ⟨9558747148914831160641955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12744996198553108214189273 9558747148914831160641955)
    ·
      refine ⟨14338120723372246740962933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9558747148914831160641955 14338120723372246740962933)
      ·
        refine ⟨1344198817816148131965275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14338120723372246740962933 1344198817816148131965275)
        ·
          refine ⟨2016298226724222197947913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344198817816148131965275 2016298226724222197947913)
          ·
            refine ⟨1512223670043166648460935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016298226724222197947913 1512223670043166648460935)
            ·
              refine ⟨2268335505064749972691403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512223670043166648460935 2268335505064749972691403)
              ·
                refine ⟨3402503257597124959037105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268335505064749972691403 3402503257597124959037105)
                ·
                  refine ⟨2551877443197843719277829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402503257597124959037105 2551877443197843719277829)
                  ·
                    refine ⟨478477020599595697364593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551877443197843719277829 478477020599595697364593)
                    ·
                      rfl

theorem cell22_1397746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_1397746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397746 prefixEnd_1397746 := by exact prefixLift 1397746
  have htrace : WordTrace (prefixWord ++ tailWord_1397746) baseStart_1397746 baseEnd_1397746 := by
    simpa [prefixWord, tailWord_1397746, baseEnd_1397746] using wordTrace_append hprefix tailTrace_1397746
  have hstable : (prefixWord ++ tailWord_1397746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397746).length < 2 ^ (prefixWord ++ tailWord_1397746).sum := by decide
  have hdescent : baseEnd_1397746 < baseStart_1397746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397772 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1397772 : Nat := 118140960795 + 1397772 * 2 ^ 59
def prefixEnd_1397772 : Nat := 4983230072969 + 3 ^ 40 * 1397772 * 2
def baseEnd_1397772 : Nat := 159495306976980098738171

theorem tailTrace_1397772 : CollatzResearch.WordTrace tailWord_1397772 prefixEnd_1397772 159495306976980098738171 := by
  unfold tailWord_1397772
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490466546059119648601785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33987288728078826198135713 25490466546059119648601785)
  ·
    refine ⟨19117849909544339736451339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25490466546059119648601785 19117849909544339736451339)
    ·
      refine ⟨28676774864316509604677009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117849909544339736451339 28676774864316509604677009)
      ·
        refine ⟨21507581148237382203507757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28676774864316509604677009 21507581148237382203507757)
        ·
          refine ⟨8065342930589018326315409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21507581148237382203507757 8065342930589018326315409)
          ·
            refine ⟨6049007197941763744736557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8065342930589018326315409 6049007197941763744736557)
            ·
              refine ⟨2268377699228161404276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6049007197941763744736557 2268377699228161404276209)
              ·
                refine ⟨1701283274421121053207157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268377699228161404276209 1701283274421121053207157)
                ·
                  refine ⟨159495306976980098738171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701283274421121053207157 159495306976980098738171)
                  ·
                    rfl

theorem cell22_1397772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1397772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397772 prefixEnd_1397772 := by exact prefixLift 1397772
  have htrace : WordTrace (prefixWord ++ tailWord_1397772) baseStart_1397772 baseEnd_1397772 := by
    simpa [prefixWord, tailWord_1397772, baseEnd_1397772] using wordTrace_append hprefix tailTrace_1397772
  have hstable : (prefixWord ++ tailWord_1397772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397772).length < 2 ^ (prefixWord ++ tailWord_1397772).sum := by decide
  have hdescent : baseEnd_1397772 < baseStart_1397772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397785 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_1397785 : Nat := 118140960795 + 1397785 * 2 ^ 59
def prefixEnd_1397785 : Nat := 4983230072969 + 3 ^ 40 * 1397785 * 2
def baseEnd_1397785 : Nat := 478490371096612595639473

theorem tailTrace_1397785 : CollatzResearch.WordTrace tailWord_1397785 prefixEnd_1397785 478490371096612595639473 := by
  unfold tailWord_1397785
  simp only [CollatzResearch.WordTrace]
  refine ⟨50981407241071142517426809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33987604827380761678284539 50981407241071142517426809)
  ·
    refine ⟨38236055430803356888070107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50981407241071142517426809 38236055430803356888070107)
    ·
      refine ⟨57354083146205035332105161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38236055430803356888070107 57354083146205035332105161)
      ·
        refine ⟨43015562359653776499078871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57354083146205035332105161 43015562359653776499078871)
        ·
          refine ⟨64523343539480664748618307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43015562359653776499078871 64523343539480664748618307)
          ·
            refine ⟨96785015309220997122927461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64523343539480664748618307 96785015309220997122927461)
            ·
              refine ⟨18147190370478936960548899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96785015309220997122927461 18147190370478936960548899)
              ·
                refine ⟨27220785555718405440823349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18147190370478936960548899 27220785555718405440823349)
                ·
                  refine ⟨2551948645848600510077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27220785555718405440823349 2551948645848600510077189)
                  ·
                    refine ⟨478490371096612595639473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2551948645848600510077189 478490371096612595639473)
                    ·
                      rfl

theorem cell22_1397785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_1397785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397785 prefixEnd_1397785 := by exact prefixLift 1397785
  have htrace : WordTrace (prefixWord ++ tailWord_1397785) baseStart_1397785 baseEnd_1397785 := by
    simpa [prefixWord, tailWord_1397785, baseEnd_1397785] using wordTrace_append hprefix tailTrace_1397785
  have hstable : (prefixWord ++ tailWord_1397785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397785).length < 2 ^ (prefixWord ++ tailWord_1397785).sum := by decide
  have hdescent : baseEnd_1397785 < baseStart_1397785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397815 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1397815 : Nat := 118140960795 + 1397815 * 2 ^ 59
def prefixEnd_1397815 : Nat := 4983230072969 + 3 ^ 40 * 1397815 * 2
def baseEnd_1397815 : Nat := 478500640709702517389381

theorem tailTrace_1397815 : CollatzResearch.WordTrace tailWord_1397815 prefixEnd_1397815 478500640709702517389381 := by
  unfold tailWord_1397815
  simp only [CollatzResearch.WordTrace]
  refine ⟨50982501430962457641018899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33988334287308305094012599 50982501430962457641018899)
  ·
    refine ⟨76473752146443686461528349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50982501430962457641018899 76473752146443686461528349)
    ·
      refine ⟨28677657054916382423073131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76473752146443686461528349 28677657054916382423073131)
      ·
        refine ⟨43016485582374573634609697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28677657054916382423073131 43016485582374573634609697)
        ·
          refine ⟨32262364186780930225957273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43016485582374573634609697 32262364186780930225957273)
          ·
            refine ⟨24196773140085697669467955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32262364186780930225957273 24196773140085697669467955)
            ·
              refine ⟨36295159710128546504201933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24196773140085697669467955 36295159710128546504201933)
              ·
                refine ⟨13610684891298204939075725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36295159710128546504201933 13610684891298204939075725)
                ·
                  refine ⟨5104006834236826852153397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13610684891298204939075725 5104006834236826852153397)
                  ·
                    refine ⟨478500640709702517389381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104006834236826852153397 478500640709702517389381)
                    ·
                      rfl

theorem cell22_1397815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1397815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397815 prefixEnd_1397815 := by exact prefixLift 1397815
  have htrace : WordTrace (prefixWord ++ tailWord_1397815) baseStart_1397815 baseEnd_1397815 := by
    simpa [prefixWord, tailWord_1397815, baseEnd_1397815] using wordTrace_append hprefix tailTrace_1397815
  have hstable : (prefixWord ++ tailWord_1397815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397815).length < 2 ^ (prefixWord ++ tailWord_1397815).sum := by decide
  have hdescent : baseEnd_1397815 < baseStart_1397815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397832 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1397832 : Nat := 118140960795 + 1397832 * 2 ^ 59
def prefixEnd_1397832 : Nat := 4983230072969 + 3 ^ 40 * 1397832 * 2
def baseEnd_1397832 : Nat := 478506460157120139714329

theorem tailTrace_1397832 : CollatzResearch.WordTrace tailWord_1397832 prefixEnd_1397832 478506460157120139714329 := by
  unfold tailWord_1397832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491560735950434772193875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33988747647933913029591833 25491560735950434772193875)
  ·
    refine ⟨38237341103925652158290813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25491560735950434772193875 38237341103925652158290813)
    ·
      refine ⟨14339002913972119559359055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38237341103925652158290813 14339002913972119559359055)
      ·
        refine ⟨21508504370958179339038583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14339002913972119559359055 21508504370958179339038583)
        ·
          refine ⟨32262756556437269008557875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21508504370958179339038583 32262756556437269008557875)
          ·
            refine ⟨48394134834655903512836813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32262756556437269008557875 48394134834655903512836813)
            ·
              refine ⟨18147800562995963817313805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48394134834655903512836813 18147800562995963817313805)
              ·
                refine ⟨6805425211123486431492677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18147800562995963817313805 6805425211123486431492677)
                ·
                  refine ⟨1276017227085653705904877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6805425211123486431492677 1276017227085653705904877)
                  ·
                    refine ⟨478506460157120139714329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276017227085653705904877 478506460157120139714329)
                    ·
                      rfl

theorem cell22_1397832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1397832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397832 prefixEnd_1397832 := by exact prefixLift 1397832
  have htrace : WordTrace (prefixWord ++ tailWord_1397832) baseStart_1397832 baseEnd_1397832 := by
    simpa [prefixWord, tailWord_1397832, baseEnd_1397832] using wordTrace_append hprefix tailTrace_1397832
  have hstable : (prefixWord ++ tailWord_1397832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397832).length < 2 ^ (prefixWord ++ tailWord_1397832).sum := by decide
  have hdescent : baseEnd_1397832 < baseStart_1397832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397853 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1397853 : Nat := 118140960795 + 1397853 * 2 ^ 59
def prefixEnd_1397853 : Nat := 4983230072969 + 3 ^ 40 * 1397853 * 2
def baseEnd_1397853 : Nat := 478513648886283084939265

theorem tailTrace_1397853 : CollatzResearch.WordTrace tailWord_1397853 prefixEnd_1397853 478513648886283084939265 := by
  unfold tailWord_1397853
  simp only [CollatzResearch.WordTrace]
  refine ⟨50983887404824790130902213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33989258269883193420601475 50983887404824790130902213)
  ·
    refine ⟨9559478888404648149544165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50983887404824790130902213 9559478888404648149544165)
    ·
      refine ⟨1792402291575871528039531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9559478888404648149544165 1792402291575871528039531)
      ·
        refine ⟨2688603437363807292059297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792402291575871528039531 2688603437363807292059297)
        ·
          refine ⟨2016452578022855469044473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688603437363807292059297 2016452578022855469044473)
          ·
            refine ⟨1512339433517141601783355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016452578022855469044473 1512339433517141601783355)
            ·
              refine ⟨2268509150275712402675033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512339433517141601783355 2268509150275712402675033)
              ·
                refine ⟨1701381862706784302006275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268509150275712402675033 1701381862706784302006275)
                ·
                  refine ⟨2552072794060176453009413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701381862706784302006275 2552072794060176453009413)
                  ·
                    refine ⟨478513648886283084939265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552072794060176453009413 478513648886283084939265)
                    ·
                      rfl

theorem cell22_1397853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1397853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397853 prefixEnd_1397853 := by exact prefixLift 1397853
  have htrace : WordTrace (prefixWord ++ tailWord_1397853) baseStart_1397853 baseEnd_1397853 := by
    simpa [prefixWord, tailWord_1397853, baseEnd_1397853] using wordTrace_append hprefix tailTrace_1397853
  have hstable : (prefixWord ++ tailWord_1397853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397853).length < 2 ^ (prefixWord ++ tailWord_1397853).sum := by decide
  have hdescent : baseEnd_1397853 < baseStart_1397853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397875 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_1397875 : Nat := 118140960795 + 1397875 * 2 ^ 59
def prefixEnd_1397875 : Nat := 4983230072969 + 3 ^ 40 * 1397875 * 2
def baseEnd_1397875 : Nat := 478521179935882360889197

theorem tailTrace_1397875 : CollatzResearch.WordTrace tailWord_1397875 prefixEnd_1397875 478521179935882360889197 := by
  unfold tailWord_1397875
  simp only [CollatzResearch.WordTrace]
  refine ⟨50984689810745087888203079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33989793207163391925468719 50984689810745087888203079)
  ·
    refine ⟨76477034716117631832304619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50984689810745087888203079 76477034716117631832304619)
    ·
      refine ⟨114715552074176447748456929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76477034716117631832304619 114715552074176447748456929)
      ·
        refine ⟨86036664055632335811342697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114715552074176447748456929 86036664055632335811342697)
        ·
          refine ⟨64527498041724251858507023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86036664055632335811342697 64527498041724251858507023)
          ·
            refine ⟨96791247062586377787760535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64527498041724251858507023 96791247062586377787760535)
            ·
              refine ⟨145186870593879566681640803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96791247062586377787760535 145186870593879566681640803)
              ·
                refine ⟨217780305890819350022461205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145186870593879566681640803 217780305890819350022461205)
                ·
                  refine ⟨10208451838632157032302869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217780305890819350022461205 10208451838632157032302869)
                  ·
                    refine ⟨478521179935882360889197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10208451838632157032302869 478521179935882360889197)
                    ·
                      rfl

theorem cell22_1397875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_1397875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397875 prefixEnd_1397875 := by exact prefixLift 1397875
  have htrace : WordTrace (prefixWord ++ tailWord_1397875) baseStart_1397875 baseEnd_1397875 := by
    simpa [prefixWord, tailWord_1397875, baseEnd_1397875] using wordTrace_append hprefix tailTrace_1397875
  have hstable : (prefixWord ++ tailWord_1397875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397875).length < 2 ^ (prefixWord ++ tailWord_1397875).sum := by decide
  have hdescent : baseEnd_1397875 < baseStart_1397875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397892 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1397892 : Nat := 118140960795 + 1397892 * 2 ^ 59
def prefixEnd_1397892 : Nat := 4983230072969 + 3 ^ 40 * 1397892 * 2
def baseEnd_1397892 : Nat := 478526999383299983214145

theorem tailTrace_1397892 : CollatzResearch.WordTrace tailWord_1397892 prefixEnd_1397892 478526999383299983214145 := by
  unfold tailWord_1397892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492654925841749895785965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33990206567788999861047953 25492654925841749895785965)
  ·
    refine ⟨9559745597190656210919737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25492654925841749895785965 9559745597190656210919737)
    ·
      refine ⟨7169809197892992158189803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9559745597190656210919737 7169809197892992158189803)
      ·
        refine ⟨10754713796839488237284705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169809197892992158189803 10754713796839488237284705)
        ·
          refine ⟨8066035347629616177963529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10754713796839488237284705 8066035347629616177963529)
          ·
            refine ⟨6049526510722212133472647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066035347629616177963529 6049526510722212133472647)
            ·
              refine ⟨9074289766083318200208971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049526510722212133472647 9074289766083318200208971)
              ·
                refine ⟨13611434649124977300313457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074289766083318200208971 13611434649124977300313457)
                ·
                  refine ⟨10208575986843732975235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13611434649124977300313457 10208575986843732975235093)
                  ·
                    refine ⟨478526999383299983214145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10208575986843732975235093 478526999383299983214145)
                    ·
                      rfl

theorem cell22_1397892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1397892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397892 prefixEnd_1397892 := by exact prefixLift 1397892
  have htrace : WordTrace (prefixWord ++ tailWord_1397892) baseStart_1397892 baseEnd_1397892 := by
    simpa [prefixWord, tailWord_1397892, baseEnd_1397892] using wordTrace_append hprefix tailTrace_1397892
  have hstable : (prefixWord ++ tailWord_1397892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397892).length < 2 ^ (prefixWord ++ tailWord_1397892).sum := by decide
  have hdescent : baseEnd_1397892 < baseStart_1397892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397896 : List Nat := [2, 1, 3, 4, 3, 1, 1, 7]
def baseStart_1397896 : Nat := 118140960795 + 1397896 * 2 ^ 59
def prefixEnd_1397896 : Nat := 4983230072969 + 3 ^ 40 * 1397896 * 2
def baseEnd_1397896 : Nat := 53169818740560589568237

theorem tailTrace_1397896 : CollatzResearch.WordTrace tailWord_1397896 prefixEnd_1397896 53169818740560589568237 := by
  unfold tailWord_1397896
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492727871834504237358771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33990303829112672316478361 25492727871834504237358771)
  ·
    refine ⟨38239091807751756356038157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25492727871834504237358771 38239091807751756356038157)
    ·
      refine ⟨14339659427906908633514309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38239091807751756356038157 14339659427906908633514309)
      ·
        refine ⟨2688686142732545368783933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14339659427906908633514309 2688686142732545368783933)
        ·
          refine ⟨1008257303524704513293975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2688686142732545368783933 1008257303524704513293975)
          ·
            refine ⟨1512385955287056769940963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008257303524704513293975 1512385955287056769940963)
            ·
              refine ⟨2268578932930585154911445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512385955287056769940963 2268578932930585154911445)
              ·
                refine ⟨53169818740560589568237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2268578932930585154911445 53169818740560589568237)
                ·
                  rfl

theorem cell22_1397896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_1397896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397896 prefixEnd_1397896 := by exact prefixLift 1397896
  have htrace : WordTrace (prefixWord ++ tailWord_1397896) baseStart_1397896 baseEnd_1397896 := by
    simpa [prefixWord, tailWord_1397896, baseEnd_1397896] using wordTrace_append hprefix tailTrace_1397896
  have hstable : (prefixWord ++ tailWord_1397896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397896).length < 2 ^ (prefixWord ++ tailWord_1397896).sum := by decide
  have hdescent : baseEnd_1397896 < baseStart_1397896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397907 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 5]
def baseStart_1397907 : Nat := 118140960795 + 1397907 * 2 ^ 59
def prefixEnd_1397907 : Nat := 4983230072969 + 3 ^ 40 * 1397907 * 2
def baseEnd_1397907 : Nat := 159510711396614981363033

theorem tailTrace_1397907 : CollatzResearch.WordTrace tailWord_1397907 prefixEnd_1397907 159510711396614981363033 := by
  unfold tailWord_1397907
  simp only [CollatzResearch.WordTrace]
  refine ⟨50985856946629157353367975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33990571297752771568911983 50985856946629157353367975)
  ·
    refine ⟨76478785419943736030051963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50985856946629157353367975 76478785419943736030051963)
    ·
      refine ⟨114718178129915604045077945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76478785419943736030051963 114718178129915604045077945)
      ·
        refine ⟨86038633597436703033808459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114718178129915604045077945 86038633597436703033808459)
        ·
          refine ⟨129057950396155054550712689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86038633597436703033808459 129057950396155054550712689)
          ·
            refine ⟨96793462797116290913034517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129057950396155054550712689 96793462797116290913034517)
            ·
              refine ⟨4537193568614826136548493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96793462797116290913034517 4537193568614826136548493)
              ·
                refine ⟨1701447588230559801205685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4537193568614826136548493 1701447588230559801205685)
                ·
                  refine ⟨159510711396614981363033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701447588230559801205685 159510711396614981363033)
                  ·
                    rfl

theorem cell22_1397907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].length) (baseStart_1397907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397907 prefixEnd_1397907 := by exact prefixLift 1397907
  have htrace : WordTrace (prefixWord ++ tailWord_1397907) baseStart_1397907 baseEnd_1397907 := by
    simpa [prefixWord, tailWord_1397907, baseEnd_1397907] using wordTrace_append hprefix tailTrace_1397907
  have hstable : (prefixWord ++ tailWord_1397907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397907).length < 2 ^ (prefixWord ++ tailWord_1397907).sum := by decide
  have hdescent : baseEnd_1397907 < baseStart_1397907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397967 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_1397967 : Nat := 118140960795 + 1397967 * 2 ^ 59
def prefixEnd_1397967 : Nat := 4983230072969 + 3 ^ 40 * 1397967 * 2
def baseEnd_1397967 : Nat := 478552673416024787588915

theorem tailTrace_1397967 : CollatzResearch.WordTrace tailWord_1397967 prefixEnd_1397967 478552673416024787588915 := by
  unfold tailWord_1397967
  simp only [CollatzResearch.WordTrace]
  refine ⟨50988045326411787600552155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33992030217607858400368103 50988045326411787600552155)
  ·
    refine ⟨76482067989617681400828233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50988045326411787600552155 76482067989617681400828233)
    ·
      refine ⟨57361550992213261050621175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76482067989617681400828233 57361550992213261050621175)
      ·
        refine ⟨86042326488319891575931763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57361550992213261050621175 86042326488319891575931763)
        ·
          refine ⟨129063489732479837363897645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86042326488319891575931763 129063489732479837363897645)
          ·
            refine ⟨48398808649679939011461617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129063489732479837363897645 48398808649679939011461617)
            ·
              refine ⟨36299106487259954258596213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48398808649679939011461617 36299106487259954258596213)
              ·
                refine ⟨3403041233180620711743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36299106487259954258596213 3403041233180620711743395)
                ·
                  refine ⟨5104561849770931067615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403041233180620711743395 5104561849770931067615093)
                  ·
                    refine ⟨478552673416024787588915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104561849770931067615093 478552673416024787588915)
                    ·
                      rfl

theorem cell22_1397967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_1397967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397967 prefixEnd_1397967 := by exact prefixLift 1397967
  have htrace : WordTrace (prefixWord ++ tailWord_1397967) baseStart_1397967 baseEnd_1397967 := by
    simpa [prefixWord, tailWord_1397967, baseEnd_1397967] using wordTrace_append hprefix tailTrace_1397967
  have hstable : (prefixWord ++ tailWord_1397967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397967).length < 2 ^ (prefixWord ++ tailWord_1397967).sum := by decide
  have hdescent : baseEnd_1397967 < baseStart_1397967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397984 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_1397984 : Nat := 118140960795 + 1397984 * 2 ^ 59
def prefixEnd_1397984 : Nat := 4983230072969 + 3 ^ 40 * 1397984 * 2
def baseEnd_1397984 : Nat := 478558492863442409913863

theorem tailTrace_1397984 : CollatzResearch.WordTrace tailWord_1397984 prefixEnd_1397984 478558492863442409913863 := by
  unfold tailWord_1397984
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494332683675099751960503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33992443578233466335947337 25494332683675099751960503)
  ·
    refine ⟨38241499025512649627940755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494332683675099751960503 38241499025512649627940755)
    ·
      refine ⟨57362248538268974441911133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38241499025512649627940755 57362248538268974441911133)
      ·
        refine ⟨21510843201850865415716675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57362248538268974441911133 21510843201850865415716675)
        ·
          refine ⟨32266264802776298123575013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21510843201850865415716675 32266264802776298123575013)
          ·
            refine ⟨6049924650520555898170315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32266264802776298123575013 6049924650520555898170315)
            ·
              refine ⟨9074886975780833847255473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049924650520555898170315 9074886975780833847255473)
              ·
                refine ⟨6806165231835625385441605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9074886975780833847255473 6806165231835625385441605)
                ·
                  refine ⟨1276155980969179759770301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6806165231835625385441605 1276155980969179759770301)
                  ·
                    refine ⟨478558492863442409913863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276155980969179759770301 478558492863442409913863)
                    ·
                      rfl

theorem cell22_1397984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_1397984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1397984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1397984 prefixEnd_1397984 := by exact prefixLift 1397984
  have htrace : WordTrace (prefixWord ++ tailWord_1397984) baseStart_1397984 baseEnd_1397984 := by
    simpa [prefixWord, tailWord_1397984, baseEnd_1397984] using wordTrace_append hprefix tailTrace_1397984
  have hstable : (prefixWord ++ tailWord_1397984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397984).length < 2 ^ (prefixWord ++ tailWord_1397984).sum := by decide
  have hdescent : baseEnd_1397984 < baseStart_1397984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398014 : List Nat := [4, 2, 2, 1, 1, 2, 1, 9]
def baseStart_1398014 : Nat := 118140960795 + 1398014 * 2 ^ 59
def prefixEnd_1398014 : Nat := 4983230072969 + 3 ^ 40 * 1398014 * 2
def baseEnd_1398014 : Nat := 53174306941836925740419

theorem tailTrace_1398014 : CollatzResearch.WordTrace tailWord_1398014 prefixEnd_1398014 53174306941836925740419 := by
  unfold tailWord_1398014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373719944655189328439137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33993173038161009751675397 6373719944655189328439137)
  ·
    refine ⟨4780289958491391996329353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6373719944655189328439137 4780289958491391996329353)
    ·
      refine ⟨3585217468868543997247015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4780289958491391996329353 3585217468868543997247015)
      ·
        refine ⟨5377826203302815995870523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585217468868543997247015 5377826203302815995870523)
        ·
          refine ⟨8066739304954223993805785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377826203302815995870523 8066739304954223993805785)
          ·
            refine ⟨6050054478715667995354339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8066739304954223993805785 6050054478715667995354339)
            ·
              refine ⟨9075081718073501993031509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050054478715667995354339 9075081718073501993031509)
              ·
                refine ⟨53174306941836925740419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9075081718073501993031509 53174306941836925740419)
                ·
                  rfl

theorem cell22_1398014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_1398014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398014 prefixEnd_1398014 := by exact prefixLift 1398014
  have htrace : WordTrace (prefixWord ++ tailWord_1398014) baseStart_1398014 baseEnd_1398014 := by
    simpa [prefixWord, tailWord_1398014, baseEnd_1398014] using wordTrace_append hprefix tailTrace_1398014
  have hstable : (prefixWord ++ tailWord_1398014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398014).length < 2 ^ (prefixWord ++ tailWord_1398014).sum := by decide
  have hdescent : baseEnd_1398014 < baseStart_1398014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398061 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1398061 : Nat := 118140960795 + 1398061 * 2 ^ 59
def prefixEnd_1398061 : Nat := 4983230072969 + 3 ^ 40 * 1398061 * 2
def baseEnd_1398061 : Nat := 478584851537039875738627

theorem tailTrace_1398061 : CollatzResearch.WordTrace tailWord_1398061 prefixEnd_1398061 478584851537039875738627 := by
  unfold tailWord_1398061
  simp only [CollatzResearch.WordTrace]
  refine ⟨50991473788071241654474037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33994315858714161102982691 50991473788071241654474037)
  ·
    refine ⟨4780450667631678905106941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50991473788071241654474037 4780450667631678905106941)
    ·
      refine ⟨1792669000361879589415103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4780450667631678905106941 1792669000361879589415103)
      ·
        refine ⟨2689003500542819384122655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792669000361879589415103 2689003500542819384122655)
        ·
          refine ⟨4033505250814229076183983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689003500542819384122655 4033505250814229076183983)
          ·
            refine ⟨6050257876221343614275975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033505250814229076183983 6050257876221343614275975)
            ·
              refine ⟨9075386814332015421413963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050257876221343614275975 9075386814332015421413963)
              ·
                refine ⟨13613080221498023132120945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9075386814332015421413963 13613080221498023132120945)
                ·
                  refine ⟨10209810166123517349090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13613080221498023132120945 10209810166123517349090709)
                  ·
                    refine ⟨478584851537039875738627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10209810166123517349090709 478584851537039875738627)
                    ·
                      rfl

theorem cell22_1398061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1398061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398061 prefixEnd_1398061 := by exact prefixLift 1398061
  have htrace : WordTrace (prefixWord ++ tailWord_1398061) baseStart_1398061 baseEnd_1398061 := by
    simpa [prefixWord, tailWord_1398061, baseEnd_1398061] using wordTrace_append hprefix tailTrace_1398061
  have hstable : (prefixWord ++ tailWord_1398061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398061).length < 2 ^ (prefixWord ++ tailWord_1398061).sum := by decide
  have hdescent : baseEnd_1398061 < baseStart_1398061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398074 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_1398074 : Nat := 118140960795 + 1398074 * 2 ^ 59
def prefixEnd_1398074 : Nat := 4983230072969 + 3 ^ 40 * 1398074 * 2
def baseEnd_1398074 : Nat := 478589301702712175163587

theorem tailTrace_1398074 : CollatzResearch.WordTrace tailWord_1398074 prefixEnd_1398074 478589301702712175163587 := by
  unfold tailWord_1398074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747986984256036218674319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33994631958016096583131517 12747986984256036218674319)
  ·
    refine ⟨19121980476384054328011479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12747986984256036218674319 19121980476384054328011479)
    ·
      refine ⟨28682970714576081492017219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19121980476384054328011479 28682970714576081492017219)
      ·
        refine ⟨43024456071864122238025829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28682970714576081492017219 43024456071864122238025829)
        ·
          refine ⟨8067085513474522919629843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43024456071864122238025829 8067085513474522919629843)
          ·
            refine ⟨12100628270211784379444765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8067085513474522919629843 12100628270211784379444765)
            ·
              refine ⟨4537735601329419142291787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12100628270211784379444765 4537735601329419142291787)
              ·
                refine ⟨6806603401994128713437681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537735601329419142291787 6806603401994128713437681)
                ·
                  refine ⟨5104952551495596535078261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806603401994128713437681 5104952551495596535078261)
                  ·
                    refine ⟨478589301702712175163587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5104952551495596535078261 478589301702712175163587)
                    ·
                      rfl

theorem cell22_1398074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_1398074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398074 prefixEnd_1398074 := by exact prefixLift 1398074
  have htrace : WordTrace (prefixWord ++ tailWord_1398074) baseStart_1398074 baseEnd_1398074 := by
    simpa [prefixWord, tailWord_1398074, baseEnd_1398074] using wordTrace_append hprefix tailTrace_1398074
  have hstable : (prefixWord ++ tailWord_1398074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398074).length < 2 ^ (prefixWord ++ tailWord_1398074).sum := by decide
  have hdescent : baseEnd_1398074 < baseStart_1398074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398089 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_1398089 : Nat := 118140960795 + 1398089 * 2 ^ 59
def prefixEnd_1398089 : Nat := 4983230072969 + 3 ^ 40 * 1398089 * 2
def baseEnd_1398089 : Nat := 478594436509257136038541

theorem tailTrace_1398089 : CollatzResearch.WordTrace tailWord_1398089 prefixEnd_1398089 478594436509257136038541 := by
  unfold tailWord_1398089
  simp only [CollatzResearch.WordTrace]
  refine ⟨50992495031969802436493321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33994996687979868290995547 50992495031969802436493321)
  ·
    refine ⟨38244371273977351827369991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50992495031969802436493321 38244371273977351827369991)
    ·
      refine ⟨57366556910966027741054987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38244371273977351827369991 57366556910966027741054987)
      ·
        refine ⟨86049835366449041611582481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57366556910966027741054987 86049835366449041611582481)
        ·
          refine ⟨64537376524836781208686861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86049835366449041611582481 64537376524836781208686861)
          ·
            refine ⟨24201516196813792953257573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64537376524836781208686861 24201516196813792953257573)
            ·
              refine ⟨4537784286902586178735795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24201516196813792953257573 4537784286902586178735795)
              ·
                refine ⟨6806676430353879268103693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537784286902586178735795 6806676430353879268103693)
                ·
                  refine ⟨2552503661382704725538885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6806676430353879268103693 2552503661382704725538885)
                  ·
                    refine ⟨478594436509257136038541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552503661382704725538885 478594436509257136038541)
                    ·
                      rfl

theorem cell22_1398089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_1398089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398089 prefixEnd_1398089 := by exact prefixLift 1398089
  have htrace : WordTrace (prefixWord ++ tailWord_1398089) baseStart_1398089 baseEnd_1398089 := by
    simpa [prefixWord, tailWord_1398089, baseEnd_1398089] using wordTrace_append hprefix tailTrace_1398089
  have hstable : (prefixWord ++ tailWord_1398089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398089).length < 2 ^ (prefixWord ++ tailWord_1398089).sum := by decide
  have hdescent : baseEnd_1398089 < baseStart_1398089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398168 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1398168 : Nat := 118140960795 + 1398168 * 2 ^ 59
def prefixEnd_1398168 : Nat := 4983230072969 + 3 ^ 40 * 1398168 * 2
def baseEnd_1398168 : Nat := 478621479823727263313299

theorem tailTrace_1398168 : CollatzResearch.WordTrace tailWord_1398168 prefixEnd_1398168 478621479823727263313299 := by
  unfold tailWord_1398168
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497688199341799464309579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33996917599122399285746105 25497688199341799464309579)
  ·
    refine ⟨38246532299012699196464369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25497688199341799464309579 38246532299012699196464369)
    ·
      refine ⟨28684899224259524397348277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38246532299012699196464369 28684899224259524397348277)
      ·
        refine ⟨2689209302274330412251401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28684899224259524397348277 2689209302274330412251401)
        ·
          refine ⟨2016906976705747809188551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2689209302274330412251401 2016906976705747809188551)
          ·
            refine ⟨3025360465058621713782827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016906976705747809188551 3025360465058621713782827)
            ·
              refine ⟨4538040697587932570674241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025360465058621713782827 4538040697587932570674241)
              ·
                refine ⟨3403530523190949428005681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538040697587932570674241 3403530523190949428005681)
                ·
                  refine ⟨2552647892393212071004261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403530523190949428005681 2552647892393212071004261)
                  ·
                    refine ⟨478621479823727263313299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552647892393212071004261 478621479823727263313299)
                    ·
                      rfl

theorem cell22_1398168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1398168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398168 prefixEnd_1398168 := by exact prefixLift 1398168
  have htrace : WordTrace (prefixWord ++ tailWord_1398168) baseStart_1398168 baseEnd_1398168 := by
    simpa [prefixWord, tailWord_1398168, baseEnd_1398168] using wordTrace_append hprefix tailTrace_1398168
  have hstable : (prefixWord ++ tailWord_1398168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398168).length < 2 ^ (prefixWord ++ tailWord_1398168).sum := by decide
  have hdescent : baseEnd_1398168 < baseStart_1398168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398172 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_1398172 : Nat := 118140960795 + 1398172 * 2 ^ 59
def prefixEnd_1398172 : Nat := 4983230072969 + 3 ^ 40 * 1398172 * 2
def baseEnd_1398172 : Nat := 159540949701824195404429

theorem tailTrace_1398172 : CollatzResearch.WordTrace tailWord_1398172 prefixEnd_1398172 159540949701824195404429 := by
  unfold tailWord_1398172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497761145334553805882385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33997014860446071741176513 25497761145334553805882385)
  ·
    refine ⟨19123320859000915354411789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25497761145334553805882385 19123320859000915354411789)
    ·
      refine ⟨7171245322125343257904421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19123320859000915354411789 7171245322125343257904421)
      ·
        refine ⟨1344608497898501860857079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7171245322125343257904421 1344608497898501860857079)
        ·
          refine ⟨2016912746847752791285619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344608497898501860857079 2016912746847752791285619)
          ·
            refine ⟨3025369120271629186928429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016912746847752791285619 3025369120271629186928429)
            ·
              refine ⟨1134513420101860945098161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3025369120271629186928429 1134513420101860945098161)
              ·
                refine ⟨850885065076395708823621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134513420101860945098161 850885065076395708823621)
                ·
                  refine ⟨159540949701824195404429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850885065076395708823621 159540949701824195404429)
                  ·
                    rfl

theorem cell22_1398172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_1398172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398172 prefixEnd_1398172 := by exact prefixLift 1398172
  have htrace : WordTrace (prefixWord ++ tailWord_1398172) baseStart_1398172 baseEnd_1398172 := by
    simpa [prefixWord, tailWord_1398172, baseEnd_1398172] using wordTrace_append hprefix tailTrace_1398172
  have hstable : (prefixWord ++ tailWord_1398172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398172).length < 2 ^ (prefixWord ++ tailWord_1398172).sum := by decide
  have hdescent : baseEnd_1398172 < baseStart_1398172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398179 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_1398179 : Nat := 118140960795 + 1398179 * 2 ^ 59
def prefixEnd_1398179 : Nat := 4983230072969 + 3 ^ 40 * 1398179 * 2
def baseEnd_1398179 : Nat := 478625245348526901288265

theorem tailTrace_1398179 : CollatzResearch.WordTrace tailWord_1398179 prefixEnd_1398179 478625245348526901288265 := by
  unfold tailWord_1398179
  simp only [CollatzResearch.WordTrace]
  refine ⟨50995777601643747807269591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33997185067762498538179727 50995777601643747807269591)
  ·
    refine ⟨76493666402465621710904387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50995777601643747807269591 76493666402465621710904387)
    ·
      refine ⟨114740499603698432566356581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76493666402465621710904387 114740499603698432566356581)
      ·
        refine ⟨21513843675693456106191859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114740499603698432566356581 21513843675693456106191859)
        ·
          refine ⟨32270765513540184159287789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21513843675693456106191859 32270765513540184159287789)
          ·
            refine ⟨12101537067577569059732921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32270765513540184159287789 12101537067577569059732921)
            ·
              refine ⟨9076152800683176794799691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12101537067577569059732921 9076152800683176794799691)
              ·
                refine ⟨13614229201024765192199537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076152800683176794799691 13614229201024765192199537)
                ·
                  refine ⟨10210671900768573894149653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13614229201024765192199537 10210671900768573894149653)
                  ·
                    refine ⟨478625245348526901288265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10210671900768573894149653 478625245348526901288265)
                    ·
                      rfl

theorem cell22_1398179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_1398179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398179 prefixEnd_1398179 := by exact prefixLift 1398179
  have htrace : WordTrace (prefixWord ++ tailWord_1398179) baseStart_1398179 baseEnd_1398179 := by
    simpa [prefixWord, tailWord_1398179, baseEnd_1398179] using wordTrace_append hprefix tailTrace_1398179
  have hstable : (prefixWord ++ tailWord_1398179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398179).length < 2 ^ (prefixWord ++ tailWord_1398179).sum := by decide
  have hdescent : baseEnd_1398179 < baseStart_1398179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398181 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1398181 : Nat := 118140960795 + 1398181 * 2 ^ 59
def prefixEnd_1398181 : Nat := 4983230072969 + 3 ^ 40 * 1398181 * 2
def baseEnd_1398181 : Nat := 478625929989399562738259

theorem tailTrace_1398181 : CollatzResearch.WordTrace tailWord_1398181 prefixEnd_1398181 478625929989399562738259 := by
  unfold tailWord_1398181
  simp only [CollatzResearch.WordTrace]
  refine ⟨50995850547636502148842397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33997233698424334765894931 50995850547636502148842397)
  ·
    refine ⟨19123443955363688305815899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50995850547636502148842397 19123443955363688305815899)
    ·
      refine ⟨28685165933045532458723849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19123443955363688305815899 28685165933045532458723849)
      ·
        refine ⟨21513874449784149344042887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28685165933045532458723849 21513874449784149344042887)
        ·
          refine ⟨32270811674676224016064331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21513874449784149344042887 32270811674676224016064331)
          ·
            refine ⟨48406217512014336024096497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32270811674676224016064331 48406217512014336024096497)
            ·
              refine ⟨36304663134010752018072373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48406217512014336024096497 36304663134010752018072373)
              ·
                refine ⟨3403562168813508001694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36304663134010752018072373 3403562168813508001694285)
                ·
                  refine ⟨1276335813305065500635357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3403562168813508001694285 1276335813305065500635357)
                  ·
                    refine ⟨478625929989399562738259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276335813305065500635357 478625929989399562738259)
                    ·
                      rfl

theorem cell22_1398181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1398181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398181 prefixEnd_1398181 := by exact prefixLift 1398181
  have htrace : WordTrace (prefixWord ++ tailWord_1398181) baseStart_1398181 baseEnd_1398181 := by
    simpa [prefixWord, tailWord_1398181, baseEnd_1398181] using wordTrace_append hprefix tailTrace_1398181
  have hstable : (prefixWord ++ tailWord_1398181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398181).length < 2 ^ (prefixWord ++ tailWord_1398181).sum := by decide
  have hdescent : baseEnd_1398181 < baseStart_1398181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398194 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1398194 : Nat := 118140960795 + 1398194 * 2 ^ 59
def prefixEnd_1398194 : Nat := 4983230072969 + 3 ^ 40 * 1398194 * 2
def baseEnd_1398194 : Nat := 159543460051690620721073

theorem tailTrace_1398194 : CollatzResearch.WordTrace tailWord_1398194 prefixEnd_1398194 159543460051690620721073 := by
  unfold tailWord_1398194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749081174147351342266409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33997549797726270246043757 12749081174147351342266409)
  ·
    refine ⟨9561810880610513506699807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12749081174147351342266409 9561810880610513506699807)
    ·
      refine ⟨14342716320915770260049711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561810880610513506699807 14342716320915770260049711)
      ·
        refine ⟨21514074481373655390074567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14342716320915770260049711 21514074481373655390074567)
        ·
          refine ⟨32271111722060483085111851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21514074481373655390074567 32271111722060483085111851)
          ·
            refine ⟨48406667583090724627667777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32271111722060483085111851 48406667583090724627667777)
            ·
              refine ⟨36305000687318043470750833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48406667583090724627667777 36305000687318043470750833)
              ·
                refine ⟨27228750515488532603063125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36305000687318043470750833 27228750515488532603063125)
                ·
                  refine ⟨159543460051690620721073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27228750515488532603063125 159543460051690620721073)
                  ·
                    rfl

theorem cell22_1398194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1398194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398194 prefixEnd_1398194 := by exact prefixLift 1398194
  have htrace : WordTrace (prefixWord ++ tailWord_1398194) baseStart_1398194 baseEnd_1398194 := by
    simpa [prefixWord, tailWord_1398194, baseEnd_1398194] using wordTrace_append hprefix tailTrace_1398194
  have hstable : (prefixWord ++ tailWord_1398194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398194).length < 2 ^ (prefixWord ++ tailWord_1398194).sum := by decide
  have hdescent : baseEnd_1398194 < baseStart_1398194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398241 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1398241 : Nat := 118140960795 + 1398241 * 2 ^ 59
def prefixEnd_1398241 : Nat := 4983230072969 + 3 ^ 40 * 1398241 * 2
def baseEnd_1398241 : Nat := 478646469215579406238075

theorem tailTrace_1398241 : CollatzResearch.WordTrace tailWord_1398241 prefixEnd_1398241 478646469215579406238075 := by
  unfold tailWord_1398241
  simp only [CollatzResearch.WordTrace]
  refine ⟨50998038927419132396026577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33998692618279421597351051 50998038927419132396026577)
  ·
    refine ⟨38248529195564349297019933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50998038927419132396026577 38248529195564349297019933)
    ·
      refine ⟨14343198448336630986382475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38248529195564349297019933 14343198448336630986382475)
      ·
        refine ⟨21514797672504946479573713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14343198448336630986382475 21514797672504946479573713)
        ·
          refine ⟨16136098254378709859680285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21514797672504946479573713 16136098254378709859680285)
          ·
            refine ⟨6051036845392016197380107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16136098254378709859680285 6051036845392016197380107)
            ·
              refine ⟨9076555268088024296070161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051036845392016197380107 9076555268088024296070161)
              ·
                refine ⟨6807416451066018222052621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9076555268088024296070161 6807416451066018222052621)
                ·
                  refine ⟨2552781169149756833269733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6807416451066018222052621 2552781169149756833269733)
                  ·
                    refine ⟨478646469215579406238075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552781169149756833269733 478646469215579406238075)
                    ·
                      rfl

theorem cell22_1398241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1398241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398241 prefixEnd_1398241 := by exact prefixLift 1398241
  have htrace : WordTrace (prefixWord ++ tailWord_1398241) baseStart_1398241 baseEnd_1398241 := by
    simpa [prefixWord, tailWord_1398241, baseEnd_1398241] using wordTrace_append hprefix tailTrace_1398241
  have hstable : (prefixWord ++ tailWord_1398241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398241).length < 2 ^ (prefixWord ++ tailWord_1398241).sum := by decide
  have hdescent : baseEnd_1398241 < baseStart_1398241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398256 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_1398256 : Nat := 118140960795 + 1398256 * 2 ^ 59
def prefixEnd_1398256 : Nat := 4983230072969 + 3 ^ 40 * 1398256 * 2
def baseEnd_1398256 : Nat := 159550534674041455704343

theorem tailTrace_1398256 : CollatzResearch.WordTrace tailWord_1398256 prefixEnd_1398256 159550534674041455704343 := by
  unfold tailWord_1398256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25499293011182394978911311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33999057348243193305215081 25499293011182394978911311)
  ·
    refine ⟨38248939516773592468366967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25499293011182394978911311 38248939516773592468366967)
    ·
      refine ⟨57373409275160388702550451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38248939516773592468366967 57373409275160388702550451)
      ·
        refine ⟨86060113912740583053825677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57373409275160388702550451 86060113912740583053825677)
        ·
          refine ⟨32272542717277718645184629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86060113912740583053825677 32272542717277718645184629)
          ·
            refine ⟨3025550879744786122986059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32272542717277718645184629 3025550879744786122986059)
            ·
              refine ⟨4538326319617179184479089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025550879744786122986059 4538326319617179184479089)
              ·
                refine ⟨3403744739712884388359317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538326319617179184479089 3403744739712884388359317)
                ·
                  refine ⟨159550534674041455704343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3403744739712884388359317 159550534674041455704343)
                  ·
                    rfl

theorem cell22_1398256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_1398256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398256 prefixEnd_1398256 := by exact prefixLift 1398256
  have htrace : WordTrace (prefixWord ++ tailWord_1398256) baseStart_1398256 baseEnd_1398256 := by
    simpa [prefixWord, tailWord_1398256, baseEnd_1398256] using wordTrace_append hprefix tailTrace_1398256
  have hstable : (prefixWord ++ tailWord_1398256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398256).length < 2 ^ (prefixWord ++ tailWord_1398256).sum := by decide
  have hdescent : baseEnd_1398256 < baseStart_1398256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398258 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1398258 : Nat := 118140960795 + 1398258 * 2 ^ 59
def prefixEnd_1398258 : Nat := 4983230072969 + 3 ^ 40 * 1398258 * 2
def baseEnd_1398258 : Nat := 478652288662997028563023

theorem tailTrace_1398258 : CollatzResearch.WordTrace tailWord_1398258 prefixEnd_1398258 478652288662997028563023 := by
  unfold tailWord_1398258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749664742089386074848857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33999105978905029532930285 12749664742089386074848857)
  ·
    refine ⟨9562248556567039556136643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12749664742089386074848857 9562248556567039556136643)
    ·
      refine ⟨14343372834850559334204965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9562248556567039556136643 14343372834850559334204965)
      ·
        refine ⟨2689382406534479875163431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14343372834850559334204965 2689382406534479875163431)
        ·
          refine ⟨4034073609801719812745147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689382406534479875163431 4034073609801719812745147)
          ·
            refine ⟨6051110414702579719117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034073609801719812745147 6051110414702579719117721)
            ·
              refine ⟨4538332811026934789338291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051110414702579719117721 4538332811026934789338291)
              ·
                refine ⟨6807499216540402184007437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538332811026934789338291 6807499216540402184007437)
                ·
                  refine ⟨2552812206202650819002789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6807499216540402184007437 2552812206202650819002789)
                  ·
                    refine ⟨478652288662997028563023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2552812206202650819002789 478652288662997028563023)
                    ·
                      rfl

theorem cell22_1398258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1398258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398258 prefixEnd_1398258 := by exact prefixLift 1398258
  have htrace : WordTrace (prefixWord ++ tailWord_1398258) baseStart_1398258 baseEnd_1398258 := by
    simpa [prefixWord, tailWord_1398258, baseEnd_1398258] using wordTrace_append hprefix tailTrace_1398258
  have hstable : (prefixWord ++ tailWord_1398258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398258).length < 2 ^ (prefixWord ++ tailWord_1398258).sum := by decide
  have hdescent : baseEnd_1398258 < baseStart_1398258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398301 : List Nat := [1, 4, 2, 2, 1, 1, 2, 9]
def baseStart_1398301 : Nat := 118140960795 + 1398301 * 2 ^ 59
def prefixEnd_1398301 : Nat := 4983230072969 + 3 ^ 40 * 1398301 * 2
def baseEnd_1398301 : Nat := 53185223160195472193099

theorem tailTrace_1398301 : CollatzResearch.WordTrace tailWord_1398301 prefixEnd_1398301 53185223160195472193099 := by
  unfold tailWord_1398301
  simp only [CollatzResearch.WordTrace]
  refine ⟨51000227307201762643210757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34000151538134508428807171 51000227307201762643210757)
  ·
    refine ⟨9562542620100330495602017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51000227307201762643210757 9562542620100330495602017)
    ·
      refine ⟨7171906965075247871701513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9562542620100330495602017 7171906965075247871701513)
      ·
        refine ⟨5378930223806435903776135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7171906965075247871701513 5378930223806435903776135)
        ·
          refine ⟨8068395335709653855664203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378930223806435903776135 8068395335709653855664203)
          ·
            refine ⟨12102593003564480783496305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8068395335709653855664203 12102593003564480783496305)
            ·
              refine ⟨9076944752673360587622229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12102593003564480783496305 9076944752673360587622229)
              ·
                refine ⟨53185223160195472193099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9076944752673360587622229 53185223160195472193099)
                ·
                  rfl

theorem cell22_1398301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 9].length) (baseStart_1398301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398301 prefixEnd_1398301 := by exact prefixLift 1398301
  have htrace : WordTrace (prefixWord ++ tailWord_1398301) baseStart_1398301 baseEnd_1398301 := by
    simpa [prefixWord, tailWord_1398301, baseEnd_1398301] using wordTrace_append hprefix tailTrace_1398301
  have hstable : (prefixWord ++ tailWord_1398301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398301).length < 2 ^ (prefixWord ++ tailWord_1398301).sum := by decide
  have hdescent : baseEnd_1398301 < baseStart_1398301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398318 : List Nat := [4, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1398318 : Nat := 118140960795 + 1398318 * 2 ^ 59
def prefixEnd_1398318 : Nat := 4983230072969 + 3 ^ 40 * 1398318 * 2
def baseEnd_1398318 : Nat := 53185869765464096895871

theorem tailTrace_1398318 : CollatzResearch.WordTrace tailWord_1398318 prefixEnd_1398318 53185869765464096895871 := by
  unfold tailWord_1398318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375105918517521818322451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34000564898760116364386405 6375105918517521818322451)
  ·
    refine ⟨9562658877776282727483677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6375105918517521818322451 9562658877776282727483677)
    ·
      refine ⟨3585997079166106022806379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9562658877776282727483677 3585997079166106022806379)
      ·
        refine ⟨5378995618749159034209569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585997079166106022806379 5378995618749159034209569)
        ·
          refine ⟨4034246714061869275657177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5378995618749159034209569 4034246714061869275657177)
          ·
            refine ⟨3025685035546401956742883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034246714061869275657177 3025685035546401956742883)
            ·
              refine ⟨4538527553319602935114325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025685035546401956742883 4538527553319602935114325)
              ·
                refine ⟨53185869765464096895871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4538527553319602935114325 53185869765464096895871)
                ·
                  rfl

theorem cell22_1398318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1398318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398318 prefixEnd_1398318 := by exact prefixLift 1398318
  have htrace : WordTrace (prefixWord ++ tailWord_1398318) baseStart_1398318 baseEnd_1398318 := by
    simpa [prefixWord, tailWord_1398318, baseEnd_1398318] using wordTrace_append hprefix tailTrace_1398318
  have hstable : (prefixWord ++ tailWord_1398318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398318).length < 2 ^ (prefixWord ++ tailWord_1398318).sum := by decide
  have hdescent : baseEnd_1398318 < baseStart_1398318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398346 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1398346 : Nat := 118140960795 + 1398346 * 2 ^ 59
def prefixEnd_1398346 : Nat := 4983230072969 + 3 ^ 40 * 1398346 * 2
def baseEnd_1398346 : Nat := 159560804287131377454251

theorem tailTrace_1398346 : CollatzResearch.WordTrace tailWord_1398346 prefixEnd_1398346 159560804287131377454251 := by
  unfold tailWord_1398346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750467148009683832149723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34001245728025823552399261 12750467148009683832149723)
  ·
    refine ⟨19125700722014525748224585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12750467148009683832149723 19125700722014525748224585)
    ·
      refine ⟨14344275541510894311168439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19125700722014525748224585 14344275541510894311168439)
      ·
        refine ⟨21516413312266341466752659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14344275541510894311168439 21516413312266341466752659)
        ·
          refine ⟨32274619968399512200128989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21516413312266341466752659 32274619968399512200128989)
          ·
            refine ⟨12102982488149817075048371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32274619968399512200128989 12102982488149817075048371)
            ·
              refine ⟨18154473732224725612572557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12102982488149817075048371 18154473732224725612572557)
              ·
                refine ⟨6807927649584272104714709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18154473732224725612572557 6807927649584272104714709)
                ·
                  refine ⟨159560804287131377454251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6807927649584272104714709 159560804287131377454251)
                  ·
                    rfl

theorem cell22_1398346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1398346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398346 prefixEnd_1398346 := by exact prefixLift 1398346
  have htrace : WordTrace (prefixWord ++ tailWord_1398346) baseStart_1398346 baseEnd_1398346 := by
    simpa [prefixWord, tailWord_1398346, baseEnd_1398346] using wordTrace_append hprefix tailTrace_1398346
  have hstable : (prefixWord ++ tailWord_1398346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398346).length < 2 ^ (prefixWord ++ tailWord_1398346).sum := by decide
  have hdescent : baseEnd_1398346 < baseStart_1398346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398361 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_1398361 : Nat := 118140960795 + 1398361 * 2 ^ 59
def prefixEnd_1398361 : Nat := 4983230072969 + 3 ^ 40 * 1398361 * 2
def baseEnd_1398361 : Nat := 478687547667939093237707

theorem tailTrace_1398361 : CollatzResearch.WordTrace tailWord_1398361 prefixEnd_1398361 478687547667939093237707 := by
  unfold tailWord_1398361
  simp only [CollatzResearch.WordTrace]
  refine ⟨51002415686984392890394937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34001610457989595260263291 51002415686984392890394937)
  ·
    refine ⟨38251811765238294667796203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51002415686984392890394937 38251811765238294667796203)
    ·
      refine ⟨57377717647857442001694305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38251811765238294667796203 57377717647857442001694305)
      ·
        refine ⟨43033288235893081501270729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57377717647857442001694305 43033288235893081501270729)
        ·
          refine ⟨32274966176919811125953047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43033288235893081501270729 32274966176919811125953047)
          ·
            refine ⟨48412449265379716688929571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32274966176919811125953047 48412449265379716688929571)
            ·
              refine ⟨72618673898069575033394357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48412449265379716688929571 72618673898069575033394357)
              ·
                refine ⟨6808000677944022659380721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72618673898069575033394357 6808000677944022659380721)
                ·
                  refine ⟨5106000508458016994535541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6808000677944022659380721 5106000508458016994535541)
                  ·
                    refine ⟨478687547667939093237707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5106000508458016994535541 478687547667939093237707)
                    ·
                      rfl

theorem cell22_1398361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_1398361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398361 prefixEnd_1398361 := by exact prefixLift 1398361
  have htrace : WordTrace (prefixWord ++ tailWord_1398361) baseStart_1398361 baseEnd_1398361 := by
    simpa [prefixWord, tailWord_1398361, baseEnd_1398361] using wordTrace_append hprefix tailTrace_1398361
  have hstable : (prefixWord ++ tailWord_1398361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398361).length < 2 ^ (prefixWord ++ tailWord_1398361).sum := by decide
  have hdescent : baseEnd_1398361 < baseStart_1398361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398423 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_1398423 : Nat := 118140960795 + 1398423 * 2 ^ 59
def prefixEnd_1398423 : Nat := 4983230072969 + 3 ^ 40 * 1398423 * 2
def baseEnd_1398423 : Nat := 478708771534991598187517

theorem tailTrace_1398423 : CollatzResearch.WordTrace tailWord_1398423 prefixEnd_1398423 478708771534991598187517 := by
  unfold tailWord_1398423
  simp only [CollatzResearch.WordTrace]
  refine ⟨51004677012759777479151923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34003118008506518319434615 51004677012759777479151923)
  ·
    refine ⟨76507015519139666218727885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51004677012759777479151923 76507015519139666218727885)
    ·
      refine ⟨28690130819677374832022957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76507015519139666218727885 28690130819677374832022957)
      ·
        refine ⟨10758799057379015562008609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28690130819677374832022957 10758799057379015562008609)
        ·
          refine ⟨8069099293034261671506457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10758799057379015562008609 8069099293034261671506457)
          ·
            refine ⟨6051824469775696253629843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8069099293034261671506457 6051824469775696253629843)
            ·
              refine ⟨9077736704663544380444765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051824469775696253629843 9077736704663544380444765)
              ·
                refine ⟨3404151264248829142666787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9077736704663544380444765 3404151264248829142666787)
                ·
                  refine ⟨5106226896373243714000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404151264248829142666787 5106226896373243714000181)
                  ·
                    refine ⟨478708771534991598187517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5106226896373243714000181 478708771534991598187517)
                    ·
                      rfl

theorem cell22_1398423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_1398423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398423 prefixEnd_1398423 := by exact prefixLift 1398423
  have htrace : WordTrace (prefixWord ++ tailWord_1398423) baseStart_1398423 baseEnd_1398423 := by
    simpa [prefixWord, tailWord_1398423, baseEnd_1398423] using wordTrace_append hprefix tailTrace_1398423
  have hstable : (prefixWord ++ tailWord_1398423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398423).length < 2 ^ (prefixWord ++ tailWord_1398423).sum := by decide
  have hdescent : baseEnd_1398423 < baseStart_1398423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398474 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_1398474 : Nat := 118140960795 + 1398474 * 2 ^ 59
def prefixEnd_1398474 : Nat := 4983230072969 + 3 ^ 40 * 1398474 * 2
def baseEnd_1398474 : Nat := 478726229877244465162361

theorem tailTrace_1398474 : CollatzResearch.WordTrace tailWord_1398474 prefixEnd_1398474 478726229877244465162361 := by
  unfold tailWord_1398474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12751634283893753297314619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34004358090383342126172317 12751634283893753297314619)
  ·
    refine ⟨19127451425840629945971929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12751634283893753297314619 19127451425840629945971929)
    ·
      refine ⟨14345588569380472459478947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19127451425840629945971929 14345588569380472459478947)
      ·
        refine ⟨21518382854070708689218421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345588569380472459478947 21518382854070708689218421)
        ·
          refine ⟨2017348392569128939614227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21518382854070708689218421 2017348392569128939614227)
          ·
            refine ⟨3026022588853693409421341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017348392569128939614227 3026022588853693409421341)
            ·
              refine ⟨1134758470820135028533003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3026022588853693409421341 1134758470820135028533003)
              ·
                refine ⟨1702137706230202542799505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134758470820135028533003 1702137706230202542799505)
                ·
                  refine ⟨1276603279672651907099629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702137706230202542799505 1276603279672651907099629)
                  ·
                    refine ⟨478726229877244465162361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276603279672651907099629 478726229877244465162361)
                    ·
                      rfl

theorem cell22_1398474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_1398474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398474 prefixEnd_1398474 := by exact prefixLift 1398474
  have htrace : WordTrace (prefixWord ++ tailWord_1398474) baseStart_1398474 baseEnd_1398474 := by
    simpa [prefixWord, tailWord_1398474, baseEnd_1398474] using wordTrace_append hprefix tailTrace_1398474
  have hstable : (prefixWord ++ tailWord_1398474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398474).length < 2 ^ (prefixWord ++ tailWord_1398474).sum := by decide
  have hdescent : baseEnd_1398474 < baseStart_1398474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_1398528 : Nat := 118140960795 + 1398528 * 2 ^ 59
def prefixEnd_1398528 : Nat := 4983230072969 + 3 ^ 40 * 1398528 * 2
def baseEnd_1398528 : Nat := 478744715180806324312195

theorem tailTrace_1398528 : CollatzResearch.WordTrace tailWord_1398528 prefixEnd_1398528 478744715180806324312195 := by
  unfold tailWord_1398528
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504253338689690205862119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34005671118252920274482825 25504253338689690205862119)
  ·
    refine ⟨38256380008034535308793179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25504253338689690205862119 38256380008034535308793179)
    ·
      refine ⟨57384570012051802963189769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38256380008034535308793179 57384570012051802963189769)
      ·
        refine ⟨43038427509038852222392327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57384570012051802963189769 43038427509038852222392327)
        ·
          refine ⟨64557641263558278333588491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43038427509038852222392327 64557641263558278333588491)
          ·
            refine ⟨96836461895337417500382737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64557641263558278333588491 96836461895337417500382737)
            ·
              refine ⟨72627346421503063125287053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96836461895337417500382737 72627346421503063125287053)
              ·
                refine ⟨27235254908063648671982645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72627346421503063125287053 27235254908063648671982645)
                ·
                  refine ⟨2553305147630967062998373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27235254908063648671982645 2553305147630967062998373)
                  ·
                    refine ⟨478744715180806324312195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2553305147630967062998373 478744715180806324312195)
                    ·
                      rfl

theorem cell22_1398528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_1398528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398528 prefixEnd_1398528 := by exact prefixLift 1398528
  have htrace : WordTrace (prefixWord ++ tailWord_1398528) baseStart_1398528 baseEnd_1398528 := by
    simpa [prefixWord, tailWord_1398528, baseEnd_1398528] using wordTrace_append hprefix tailTrace_1398528
  have hstable : (prefixWord ++ tailWord_1398528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398528).length < 2 ^ (prefixWord ++ tailWord_1398528).sum := by decide
  have hdescent : baseEnd_1398528 < baseStart_1398528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398530 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1398530 : Nat := 118140960795 + 1398530 * 2 ^ 59
def prefixEnd_1398530 : Nat := 4983230072969 + 3 ^ 40 * 1398530 * 2
def baseEnd_1398530 : Nat := 478745399821678985762189

theorem tailTrace_1398530 : CollatzResearch.WordTrace tailWord_1398530 prefixEnd_1398530 478745399821678985762189 := by
  unfold tailWord_1398530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12752144905843033688324261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34005719748914756502198029 12752144905843033688324261)
  ·
    refine ⟨2391027169845568816560799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12752144905843033688324261 2391027169845568816560799)
    ·
      refine ⟨3586540754768353224841199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391027169845568816560799 3586540754768353224841199)
      ·
        refine ⟨5379811132152529837261799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586540754768353224841199 5379811132152529837261799)
        ·
          refine ⟨8069716698228794755892699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379811132152529837261799 8069716698228794755892699)
          ·
            refine ⟨12104575047343192133839049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069716698228794755892699 12104575047343192133839049)
            ·
              refine ⟨9078431285507394100379287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12104575047343192133839049 9078431285507394100379287)
              ·
                refine ⟨13617646928261091150568931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9078431285507394100379287 13617646928261091150568931)
                ·
                  refine ⟨20426470392391636725853397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13617646928261091150568931 20426470392391636725853397)
                  ·
                    refine ⟨478745399821678985762189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20426470392391636725853397 478745399821678985762189)
                    ·
                      rfl

theorem cell22_1398530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1398530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398530 prefixEnd_1398530 := by exact prefixLift 1398530
  have htrace : WordTrace (prefixWord ++ tailWord_1398530) baseStart_1398530 baseEnd_1398530 := by
    simpa [prefixWord, tailWord_1398530, baseEnd_1398530] using wordTrace_append hprefix tailTrace_1398530
  have hstable : (prefixWord ++ tailWord_1398530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398530).length < 2 ^ (prefixWord ++ tailWord_1398530).sum := by decide
  have hdescent : baseEnd_1398530 < baseStart_1398530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398532 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1398532 : Nat := 118140960795 + 1398532 * 2 ^ 59
def prefixEnd_1398532 : Nat := 4983230072969 + 3 ^ 40 * 1398532 * 2
def baseEnd_1398532 : Nat := 159582028154183882404061

theorem tailTrace_1398532 : CollatzResearch.WordTrace tailWord_1398532 prefixEnd_1398532 159582028154183882404061 := by
  unfold tailWord_1398532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504326284682444547434925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34005768379576592729913233 25504326284682444547434925)
  ·
    refine ⟨9564122356755916705288097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25504326284682444547434925 9564122356755916705288097)
    ·
      refine ⟨7173091767566937528966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9564122356755916705288097 7173091767566937528966073)
      ·
        refine ⟨5379818825675203146724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7173091767566937528966073 5379818825675203146724555)
        ·
          refine ⟨8069728238512804720086833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379818825675203146724555 8069728238512804720086833)
          ·
            refine ⟨6052296178884603540065125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8069728238512804720086833 6052296178884603540065125)
            ·
              refine ⟨1134805533540863163762211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6052296178884603540065125 1134805533540863163762211)
              ·
                refine ⟨1702208300311294745643317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134805533540863163762211 1702208300311294745643317)
                ·
                  refine ⟨159582028154183882404061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702208300311294745643317 159582028154183882404061)
                  ·
                    rfl

theorem cell22_1398532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1398532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398532 prefixEnd_1398532 := by exact prefixLift 1398532
  have htrace : WordTrace (prefixWord ++ tailWord_1398532) baseStart_1398532 baseEnd_1398532 := by
    simpa [prefixWord, tailWord_1398532, baseEnd_1398532] using wordTrace_append hprefix tailTrace_1398532
  have hstable : (prefixWord ++ tailWord_1398532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398532).length < 2 ^ (prefixWord ++ tailWord_1398532).sum := by decide
  have hdescent : baseEnd_1398532 < baseStart_1398532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398577 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 4]
def baseStart_1398577 : Nat := 118140960795 + 1398577 * 2 ^ 59
def prefixEnd_1398577 : Nat := 4983230072969 + 3 ^ 40 * 1398577 * 2
def baseEnd_1398577 : Nat := 159587162960728843279015

theorem tailTrace_1398577 : CollatzResearch.WordTrace tailWord_1398577 prefixEnd_1398577 159587162960728843279015 := by
  unfold tailWord_1398577
  simp only [CollatzResearch.WordTrace]
  refine ⟨51010293854201861780257985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34006862569467907853505323 51010293854201861780257985)
  ·
    refine ⟨38257720390651396335193489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51010293854201861780257985 38257720390651396335193489)
    ·
      refine ⟨28693290292988547251395117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38257720390651396335193489 28693290292988547251395117)
      ·
        refine ⟨10759983859870705219273169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28693290292988547251395117 10759983859870705219273169)
        ·
          refine ⟨8069987894903028914454877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10759983859870705219273169 8069987894903028914454877)
          ·
            refine ⟨3026245460588635842920579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8069987894903028914454877 3026245460588635842920579)
            ·
              refine ⟨4539368190882953764380869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026245460588635842920579 4539368190882953764380869)
              ·
                refine ⟨851131535790553830821413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4539368190882953764380869 851131535790553830821413)
                ·
                  refine ⟨159587162960728843279015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851131535790553830821413 159587162960728843279015)
                  ·
                    rfl

theorem cell22_1398577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_1398577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398577 prefixEnd_1398577 := by exact prefixLift 1398577
  have htrace : WordTrace (prefixWord ++ tailWord_1398577) baseStart_1398577 baseEnd_1398577 := by
    simpa [prefixWord, tailWord_1398577, baseEnd_1398577] using wordTrace_append hprefix tailTrace_1398577
  have hstable : (prefixWord ++ tailWord_1398577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398577).length < 2 ^ (prefixWord ++ tailWord_1398577).sum := by decide
  have hdescent : baseEnd_1398577 < baseStart_1398577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398626 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1398626 : Nat := 118140960795 + 1398626 * 2 ^ 59
def prefixEnd_1398626 : Nat := 4983230072969 + 3 ^ 40 * 1398626 * 2
def baseEnd_1398626 : Nat := 478778262583566735361895

theorem tailTrace_1398626 : CollatzResearch.WordTrace tailWord_1398626 prefixEnd_1398626 478778262583566735361895 := by
  unfold tailWord_1398626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753020257756085787197933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34008054020682895432527821 12753020257756085787197933)
  ·
    refine ⟨4782382596658532170199225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12753020257756085787197933 4782382596658532170199225)
    ·
      refine ⟨3586786947493899127649419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782382596658532170199225 3586786947493899127649419)
      ·
        refine ⟨5380180421240848691474129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586786947493899127649419 5380180421240848691474129)
        ·
          refine ⟨4035135315930636518605597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5380180421240848691474129 4035135315930636518605597)
          ·
            refine ⟨1513175743473988694477099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4035135315930636518605597 1513175743473988694477099)
            ·
              refine ⟨2269763615210983041715649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513175743473988694477099 2269763615210983041715649)
              ·
                refine ⟨1702322711408237281286737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269763615210983041715649 1702322711408237281286737)
                ·
                  refine ⟨1276742033556177960965053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702322711408237281286737 1276742033556177960965053)
                  ·
                    refine ⟨478778262583566735361895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276742033556177960965053 478778262583566735361895)
                    ·
                      rfl

theorem cell22_1398626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1398626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398626 prefixEnd_1398626 := by exact prefixLift 1398626
  have htrace : WordTrace (prefixWord ++ tailWord_1398626) baseStart_1398626 baseEnd_1398626 := by
    simpa [prefixWord, tailWord_1398626, baseEnd_1398626] using wordTrace_append hprefix tailTrace_1398626
  have hstable : (prefixWord ++ tailWord_1398626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398626).length < 2 ^ (prefixWord ++ tailWord_1398626).sum := by decide
  have hdescent : baseEnd_1398626 < baseStart_1398626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398637 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1398637 : Nat := 118140960795 + 1398637 * 2 ^ 59
def prefixEnd_1398637 : Nat := 4983230072969 + 3 ^ 40 * 1398637 * 2
def baseEnd_1398637 : Nat := 478782028108366373336861

theorem tailTrace_1398637 : CollatzResearch.WordTrace tailWord_1398637 prefixEnd_1398637 478782028108366373336861 := by
  unfold tailWord_1398637
  simp only [CollatzResearch.WordTrace]
  refine ⟨51012482233984492027442165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34008321489322994684961443 51012482233984492027442165)
  ·
    refine ⟨4782420209436046127572703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51012482233984492027442165 4782420209436046127572703)
    ·
      refine ⟨7173630314154069191359055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4782420209436046127572703 7173630314154069191359055)
      ·
        refine ⟨10760445471231103787038583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7173630314154069191359055 10760445471231103787038583)
        ·
          refine ⟨16140668206846655680557875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760445471231103787038583 16140668206846655680557875)
          ·
            refine ⟨24211002310269983520836813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16140668206846655680557875 24211002310269983520836813)
            ·
              refine ⟨9079125866351243820313805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24211002310269983520836813 9079125866351243820313805)
              ·
                refine ⟨3404672199881716432617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9079125866351243820313805 3404672199881716432617677)
                ·
                  refine ⟨1276752074955643662231629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3404672199881716432617677 1276752074955643662231629)
                  ·
                    refine ⟨478782028108366373336861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276752074955643662231629 478782028108366373336861)
                    ·
                      rfl

theorem cell22_1398637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1398637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398637 prefixEnd_1398637 := by exact prefixLift 1398637
  have htrace : WordTrace (prefixWord ++ tailWord_1398637) baseStart_1398637 baseEnd_1398637 := by
    simpa [prefixWord, tailWord_1398637, baseEnd_1398637] using wordTrace_append hprefix tailTrace_1398637
  have hstable : (prefixWord ++ tailWord_1398637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398637).length < 2 ^ (prefixWord ++ tailWord_1398637).sum := by decide
  have hdescent : baseEnd_1398637 < baseStart_1398637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398650 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_1398650 : Nat := 118140960795 + 1398650 * 2 ^ 59
def prefixEnd_1398650 : Nat := 4983230072969 + 3 ^ 40 * 1398650 * 2
def baseEnd_1398650 : Nat := 159595492758012890920607

theorem tailTrace_1398650 : CollatzResearch.WordTrace tailWord_1398650 prefixEnd_1398650 159595492758012890920607 := by
  unfold tailWord_1398650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753239095734348811916351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34008637588624930165110269 12753239095734348811916351)
  ·
    refine ⟨19129858643601523217874527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12753239095734348811916351 19129858643601523217874527)
    ·
      refine ⟨28694787965402284826811791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19129858643601523217874527 28694787965402284826811791)
      ·
        refine ⟨43042181948103427240217687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28694787965402284826811791 43042181948103427240217687)
        ·
          refine ⟨64563272922155140860326531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43042181948103427240217687 64563272922155140860326531)
          ·
            refine ⟨96844909383232711290489797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64563272922155140860326531 96844909383232711290489797)
            ·
              refine ⟨18158420509356133366966837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96844909383232711290489797 18158420509356133366966837)
              ·
                refine ⟨1702351922752137503153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18158420509356133366966837 1702351922752137503153141)
                ·
                  refine ⟨159595492758012890920607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702351922752137503153141 159595492758012890920607)
                  ·
                    rfl

theorem cell22_1398650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_1398650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398650 prefixEnd_1398650 := by exact prefixLift 1398650
  have htrace : WordTrace (prefixWord ++ tailWord_1398650) baseStart_1398650 baseEnd_1398650 := by
    simpa [prefixWord, tailWord_1398650, baseEnd_1398650] using wordTrace_append hprefix tailTrace_1398650
  have hstable : (prefixWord ++ tailWord_1398650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398650).length < 2 ^ (prefixWord ++ tailWord_1398650).sum := by decide
  have hdescent : baseEnd_1398650 < baseStart_1398650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398744 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1398744 : Nat := 118140960795 + 1398744 * 2 ^ 59
def prefixEnd_1398744 : Nat := 4983230072969 + 3 ^ 40 * 1398744 * 2
def baseEnd_1398744 : Nat := 478818656395053760911533

theorem tailTrace_1398744 : CollatzResearch.WordTrace tailWord_1398744 prefixEnd_1398744 478818656395053760911533 := by
  unfold tailWord_1398744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25508192422298424650793643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34010923229731232867724857 25508192422298424650793643)
  ·
    refine ⟨38262288633447636976190465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25508192422298424650793643 38262288633447636976190465)
    ·
      refine ⟨28696716475085727732142849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38262288633447636976190465 28696716475085727732142849)
      ·
        refine ⟨21522537356314295799107137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28696716475085727732142849 21522537356314295799107137)
        ·
          refine ⟨16141903017235721849330353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21522537356314295799107137 16141903017235721849330353)
          ·
            refine ⟨12106427262926791386997765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16141903017235721849330353 12106427262926791386997765)
            ·
              refine ⟨2269955111798773385062081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12106427262926791386997765 2269955111798773385062081)
              ·
                refine ⟨1702466333849080038796561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269955111798773385062081 1702466333849080038796561)
                ·
                  refine ⟨1276849750386810029097421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702466333849080038796561 1276849750386810029097421)
                  ·
                    refine ⟨478818656395053760911533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276849750386810029097421 478818656395053760911533)
                    ·
                      rfl

theorem cell22_1398744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1398744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398744 prefixEnd_1398744 := by exact prefixLift 1398744
  have htrace : WordTrace (prefixWord ++ tailWord_1398744) baseStart_1398744 baseEnd_1398744 := by
    simpa [prefixWord, tailWord_1398744, baseEnd_1398744] using wordTrace_append hprefix tailTrace_1398744
  have hstable : (prefixWord ++ tailWord_1398744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398744).length < 2 ^ (prefixWord ++ tailWord_1398744).sum := by decide
  have hdescent : baseEnd_1398744 < baseStart_1398744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_1398800 : Nat := 118140960795 + 1398800 * 2 ^ 59
def prefixEnd_1398800 : Nat := 4983230072969 + 3 ^ 40 * 1398800 * 2
def baseEnd_1398800 : Nat := 478837826339488281511361

theorem tailTrace_1398800 : CollatzResearch.WordTrace tailWord_1398800 prefixEnd_1398800 478837826339488281511361 := by
  unfold tailWord_1398800
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509213666196985432812927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34012284888262647243750569 25509213666196985432812927)
  ·
    refine ⟨38263820499295478149219391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25509213666196985432812927 38263820499295478149219391)
    ·
      refine ⟨57395730748943217223829087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38263820499295478149219391 57395730748943217223829087)
      ·
        refine ⟨86093596123414825835743631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57395730748943217223829087 86093596123414825835743631)
        ·
          refine ⟨129140394185122238753615447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86093596123414825835743631 129140394185122238753615447)
          ·
            refine ⟨193710591277683358130423171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129140394185122238753615447 193710591277683358130423171)
            ·
              refine ⟨290565886916525037195634757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193710591277683358130423171 290565886916525037195634757)
              ·
                refine ⟨54481103796848444474181517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290565886916525037195634757 54481103796848444474181517)
                ·
                  refine ⟨20430413923818166677818069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54481103796848444474181517 20430413923818166677818069)
                  ·
                    refine ⟨478837826339488281511361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20430413923818166677818069 478837826339488281511361)
                    ·
                      rfl

theorem cell22_1398800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_1398800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398800 prefixEnd_1398800 := by exact prefixLift 1398800
  have htrace : WordTrace (prefixWord ++ tailWord_1398800) baseStart_1398800 baseEnd_1398800 := by
    simpa [prefixWord, tailWord_1398800, baseEnd_1398800] using wordTrace_append hprefix tailTrace_1398800
  have hstable : (prefixWord ++ tailWord_1398800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398800).length < 2 ^ (prefixWord ++ tailWord_1398800).sum := by decide
  have hdescent : baseEnd_1398800 < baseStart_1398800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398819 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 5]
def baseStart_1398819 : Nat := 118140960795 + 1398819 * 2 ^ 59
def prefixEnd_1398819 : Nat := 4983230072969 + 3 ^ 40 * 1398819 * 2
def baseEnd_1398819 : Nat := 159614776809259521762101

theorem tailTrace_1398819 : CollatzResearch.WordTrace tailWord_1398819 prefixEnd_1398819 159614776809259521762101 := by
  unfold tailWord_1398819
  simp only [CollatzResearch.WordTrace]
  refine ⟨51019120319325137110567511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34012746879550091407045007 51019120319325137110567511)
  ·
    refine ⟨76528680478987705665851267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51019120319325137110567511 76528680478987705665851267)
    ·
      refine ⟨114793020718481558498776901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76528680478987705665851267 114793020718481558498776901)
      ·
        refine ⟨21523691384715292218520669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114793020718481558498776901 21523691384715292218520669)
        ·
          refine ⟨8071384269268234581945251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21523691384715292218520669 8071384269268234581945251)
          ·
            refine ⟨12107076403902351872917877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8071384269268234581945251 12107076403902351872917877)
            ·
              refine ⟨1135038412865845488086051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12107076403902351872917877 1135038412865845488086051)
              ·
                refine ⟨1702557619298768232129077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135038412865845488086051 1702557619298768232129077)
                ·
                  refine ⟨159614776809259521762101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702557619298768232129077 159614776809259521762101)
                  ·
                    rfl

theorem cell22_1398819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 5].length) (baseStart_1398819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398819 prefixEnd_1398819 := by exact prefixLift 1398819
  have htrace : WordTrace (prefixWord ++ tailWord_1398819) baseStart_1398819 baseEnd_1398819 := by
    simpa [prefixWord, tailWord_1398819, baseEnd_1398819] using wordTrace_append hprefix tailTrace_1398819
  have hstable : (prefixWord ++ tailWord_1398819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398819).length < 2 ^ (prefixWord ++ tailWord_1398819).sum := by decide
  have hdescent : baseEnd_1398819 < baseStart_1398819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398840 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_1398840 : Nat := 118140960795 + 1398840 * 2 ^ 59
def prefixEnd_1398840 : Nat := 4983230072969 + 3 ^ 40 * 1398840 * 2
def baseEnd_1398840 : Nat := 478851519156941510511239

theorem tailTrace_1398840 : CollatzResearch.WordTrace tailWord_1398840 prefixEnd_1398840 478851519156941510511239 := by
  unfold tailWord_1398840
  simp only [CollatzResearch.WordTrace]
  refine ⟨25509943126124528848540987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34013257501499371798054649 25509943126124528848540987)
  ·
    refine ⟨38264914689186793272811481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25509943126124528848540987 38264914689186793272811481)
    ·
      refine ⟨28698686016890094954608611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38264914689186793272811481 28698686016890094954608611)
      ·
        refine ⟨43048029025335142431912917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28698686016890094954608611 43048029025335142431912917)
        ·
          refine ⟨1008938180281292400747959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43048029025335142431912917 1008938180281292400747959)
          ·
            refine ⟨1513407270421938601121939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008938180281292400747959 1513407270421938601121939)
            ·
              refine ⟨2270110905632907901682909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513407270421938601121939 2270110905632907901682909)
              ·
                refine ⟨851291589612340463131091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2270110905632907901682909 851291589612340463131091)
                ·
                  refine ⟨1276937384418510694696637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851291589612340463131091 1276937384418510694696637)
                  ·
                    refine ⟨478851519156941510511239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1276937384418510694696637 478851519156941510511239)
                    ·
                      rfl

theorem cell22_1398840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_1398840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398840 prefixEnd_1398840 := by exact prefixLift 1398840
  have htrace : WordTrace (prefixWord ++ tailWord_1398840) baseStart_1398840 baseEnd_1398840 := by
    simpa [prefixWord, tailWord_1398840, baseEnd_1398840] using wordTrace_append hprefix tailTrace_1398840
  have hstable : (prefixWord ++ tailWord_1398840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398840).length < 2 ^ (prefixWord ++ tailWord_1398840).sum := by decide
  have hdescent : baseEnd_1398840 < baseStart_1398840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398870 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1398870 : Nat := 118140960795 + 1398870 * 2 ^ 59
def prefixEnd_1398870 : Nat := 4983230072969 + 3 ^ 40 * 1398870 * 2
def baseEnd_1398870 : Nat := 159620596256677144087049

theorem tailTrace_1398870 : CollatzResearch.WordTrace tailWord_1398870 prefixEnd_1398870 159620596256677144087049 := by
  unfold tailWord_1398870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188811277633773301292129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34013986961426915213782709 3188811277633773301292129)
  ·
    refine ⟨2391608458225329975969097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3188811277633773301292129 2391608458225329975969097)
    ·
      refine ⟨1793706343668997481976823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2391608458225329975969097 1793706343668997481976823)
      ·
        refine ⟨2690559515503496222965235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793706343668997481976823 2690559515503496222965235)
        ·
          refine ⟨4035839273255244334447853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690559515503496222965235 4035839273255244334447853)
          ·
            refine ⟨1513439727470716625417945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4035839273255244334447853 1513439727470716625417945)
            ·
              refine ⟨1135079795603037469063459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513439727470716625417945 1135079795603037469063459)
              ·
                refine ⟨1702619693404556203595189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135079795603037469063459 1702619693404556203595189)
                ·
                  refine ⟨159620596256677144087049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702619693404556203595189 159620596256677144087049)
                  ·
                    rfl

theorem cell22_1398870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1398870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398870 prefixEnd_1398870 := by exact prefixLift 1398870
  have htrace : WordTrace (prefixWord ++ tailWord_1398870) baseStart_1398870 baseEnd_1398870 := by
    simpa [prefixWord, tailWord_1398870, baseEnd_1398870] using wordTrace_append hprefix tailTrace_1398870
  have hstable : (prefixWord ++ tailWord_1398870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398870).length < 2 ^ (prefixWord ++ tailWord_1398870).sum := by decide
  have hdescent : baseEnd_1398870 < baseStart_1398870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398892 : List Nat := [2, 2, 1, 1, 3, 3, 2, 8]
def baseStart_1398892 : Nat := 118140960795 + 1398892 * 2 ^ 59
def prefixEnd_1398892 : Nat := 4983230072969 + 3 ^ 40 * 1398892 * 2
def baseEnd_1398892 : Nat := 53207702202181189801231

theorem tailTrace_1398892 : CollatzResearch.WordTrace tailWord_1398892 prefixEnd_1398892 53207702202181189801231 := by
  unfold tailWord_1398892
  simp only [CollatzResearch.WordTrace]
  refine ⟨25510891424030335288987465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34014521898707113718649953 25510891424030335288987465)
  ·
    refine ⟨19133168568022751466740599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25510891424030335288987465 19133168568022751466740599)
    ·
      refine ⟨28699752852034127200110899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19133168568022751466740599 28699752852034127200110899)
      ·
        refine ⟨43049629278051190800166349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28699752852034127200110899 43049629278051190800166349)
        ·
          refine ⟨16143610979269196550062381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43049629278051190800166349 16143610979269196550062381)
          ·
            refine ⟨6053854117225948706273393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16143610979269196550062381 6053854117225948706273393)
            ·
              refine ⟨4540390587919461529705045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6053854117225948706273393 4540390587919461529705045)
              ·
                refine ⟨53207702202181189801231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4540390587919461529705045 53207702202181189801231)
                ·
                  rfl

theorem cell22_1398892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_1398892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398892 prefixEnd_1398892 := by exact prefixLift 1398892
  have htrace : WordTrace (prefixWord ++ tailWord_1398892) baseStart_1398892 baseEnd_1398892 := by
    simpa [prefixWord, tailWord_1398892, baseEnd_1398892] using wordTrace_append hprefix tailTrace_1398892
  have hstable : (prefixWord ++ tailWord_1398892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398892).length < 2 ^ (prefixWord ++ tailWord_1398892).sum := by decide
  have hdescent : baseEnd_1398892 < baseStart_1398892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398913 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1398913 : Nat := 118140960795 + 1398913 * 2 ^ 59
def prefixEnd_1398913 : Nat := 4983230072969 + 3 ^ 40 * 1398913 * 2
def baseEnd_1398913 : Nat := 478876508548793653436015

theorem tailTrace_1398913 : CollatzResearch.WordTrace tailWord_1398913 prefixEnd_1398913 478876508548793653436015 := by
  unfold tailWord_1398913
  simp only [CollatzResearch.WordTrace]
  refine ⟨51022548780984591164489393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34015032520656394109659595 51022548780984591164489393)
  ·
    refine ⟨38266911585738443373367045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51022548780984591164489393 38266911585738443373367045)
    ·
      refine ⟨7175045922325958132506321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38266911585738443373367045 7175045922325958132506321)
      ·
        refine ⟨5381284441744468599379741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7175045922325958132506321 5381284441744468599379741)
        ·
          refine ⟨2017981665654175724767403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5381284441744468599379741 2017981665654175724767403)
          ·
            refine ⟨3026972498481263587151105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017981665654175724767403 3026972498481263587151105)
            ·
              refine ⟨2270229373860947690363329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026972498481263587151105 2270229373860947690363329)
              ·
                refine ⟨1702672030395710767772497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270229373860947690363329 1702672030395710767772497)
                ·
                  refine ⟨1277004022796783075829373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702672030395710767772497 1277004022796783075829373)
                  ·
                    refine ⟨478876508548793653436015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277004022796783075829373 478876508548793653436015)
                    ·
                      rfl

theorem cell22_1398913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1398913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398913 prefixEnd_1398913 := by exact prefixLift 1398913
  have htrace : WordTrace (prefixWord ++ tailWord_1398913) baseStart_1398913 baseEnd_1398913 := by
    simpa [prefixWord, tailWord_1398913, baseEnd_1398913] using wordTrace_append hprefix tailTrace_1398913
  have hstable : (prefixWord ++ tailWord_1398913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398913).length < 2 ^ (prefixWord ++ tailWord_1398913).sum := by decide
  have hdescent : baseEnd_1398913 < baseStart_1398913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398926 : List Nat := [4, 1, 1, 3, 3, 2, 1, 7]
def baseStart_1398926 : Nat := 118140960795 + 1398926 * 2 ^ 59
def prefixEnd_1398926 : Nat := 4983230072969 + 3 ^ 40 * 1398926 * 2
def baseEnd_1398926 : Nat := 53208995412718439206775

theorem tailTrace_1398926 : CollatzResearch.WordTrace tailWord_1398926 prefixEnd_1398926 53208995412718439206775 := by
  unfold tailWord_1398926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377877866242186798089079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34015348619958329589808421 6377877866242186798089079)
  ·
    refine ⟨9566816799363280197133619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6377877866242186798089079 9566816799363280197133619)
    ·
      refine ⟨14350225199044920295700429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9566816799363280197133619 14350225199044920295700429)
      ·
        refine ⟨5381334449641845110887661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14350225199044920295700429 5381334449641845110887661)
        ·
          refine ⟨2018000418615691916582873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5381334449641845110887661 2018000418615691916582873)
          ·
            refine ⟨1513500313961768937437155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018000418615691916582873 1513500313961768937437155)
            ·
              refine ⟨2270250470942653406155733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513500313961768937437155 2270250470942653406155733)
              ·
                refine ⟨53208995412718439206775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2270250470942653406155733 53208995412718439206775)
                ·
                  rfl

theorem cell22_1398926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_1398926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398926 prefixEnd_1398926 := by exact prefixLift 1398926
  have htrace : WordTrace (prefixWord ++ tailWord_1398926) baseStart_1398926 baseEnd_1398926 := by
    simpa [prefixWord, tailWord_1398926, baseEnd_1398926] using wordTrace_append hprefix tailTrace_1398926
  have hstable : (prefixWord ++ tailWord_1398926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398926).length < 2 ^ (prefixWord ++ tailWord_1398926).sum := by decide
  have hdescent : baseEnd_1398926 < baseStart_1398926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398941 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1398941 : Nat := 118140960795 + 1398941 * 2 ^ 59
def prefixEnd_1398941 : Nat := 4983230072969 + 3 ^ 40 * 1398941 * 2
def baseEnd_1398941 : Nat := 478886093521010913735929

theorem tailTrace_1398941 : CollatzResearch.WordTrace tailWord_1398941 prefixEnd_1398941 478886093521010913735929 := by
  unfold tailWord_1398941
  simp only [CollatzResearch.WordTrace]
  refine ⟨51023570024883151946508677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34015713349922101297672451 51023570024883151946508677)
  ·
    refine ⟨9566919379665590989970377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51023570024883151946508677 9566919379665590989970377)
    ·
      refine ⟨7175189534749193242477783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9566919379665590989970377 7175189534749193242477783)
      ·
        refine ⟨10762784302123789863716675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175189534749193242477783 10762784302123789863716675)
        ·
          refine ⟨16144176453185684795575013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762784302123789863716675 16144176453185684795575013)
          ·
            refine ⟨3027033084972315899170315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16144176453185684795575013 3027033084972315899170315)
            ·
              refine ⟨4540549627458473848755473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027033084972315899170315 4540549627458473848755473)
              ·
                refine ⟨3405412220593855386566605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540549627458473848755473 3405412220593855386566605)
                ·
                  refine ⟨1277029582722695769962477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3405412220593855386566605 1277029582722695769962477)
                  ·
                    refine ⟨478886093521010913735929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277029582722695769962477 478886093521010913735929)
                    ·
                      rfl

theorem cell22_1398941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1398941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398941 prefixEnd_1398941 := by exact prefixLift 1398941
  have htrace : WordTrace (prefixWord ++ tailWord_1398941) baseStart_1398941 baseEnd_1398941 := by
    simpa [prefixWord, tailWord_1398941, baseEnd_1398941] using wordTrace_append hprefix tailTrace_1398941
  have hstable : (prefixWord ++ tailWord_1398941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398941).length < 2 ^ (prefixWord ++ tailWord_1398941).sum := by decide
  have hdescent : baseEnd_1398941 < baseStart_1398941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398964 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1398964 : Nat := 118140960795 + 1398964 * 2 ^ 59
def prefixEnd_1398964 : Nat := 4983230072969 + 3 ^ 40 * 1398964 * 2
def baseEnd_1398964 : Nat := 478893966891046520410859

theorem tailTrace_1398964 : CollatzResearch.WordTrace tailWord_1398964 prefixEnd_1398964 478893966891046520410859 := by
  unfold tailWord_1398964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25512204451899913437297973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34016272602533217916397297 25512204451899913437297973)
  ·
    refine ⟨2391769167365616884746685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25512204451899913437297973 2391769167365616884746685)
    ·
      refine ⟨896913437762106331780007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2391769167365616884746685 896913437762106331780007)
      ·
        refine ⟨1345370156643159497670011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896913437762106331780007 1345370156643159497670011)
        ·
          refine ⟨2018055234964739246505017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345370156643159497670011 2018055234964739246505017)
          ·
            refine ⟨1513541426223554434878763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018055234964739246505017 1513541426223554434878763)
            ·
              refine ⟨2270312139335331652318145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513541426223554434878763 2270312139335331652318145)
              ·
                refine ⟨1702734104501498739238609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270312139335331652318145 1702734104501498739238609)
                ·
                  refine ⟨1277050578376124054428957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702734104501498739238609 1277050578376124054428957)
                  ·
                    refine ⟨478893966891046520410859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277050578376124054428957 478893966891046520410859)
                    ·
                      rfl

theorem cell22_1398964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1398964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1398964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1398964 prefixEnd_1398964 := by exact prefixLift 1398964
  have htrace : WordTrace (prefixWord ++ tailWord_1398964) baseStart_1398964 baseEnd_1398964 := by
    simpa [prefixWord, tailWord_1398964, baseEnd_1398964] using wordTrace_append hprefix tailTrace_1398964
  have hstable : (prefixWord ++ tailWord_1398964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398964).length < 2 ^ (prefixWord ++ tailWord_1398964).sum := by decide
  have hdescent : baseEnd_1398964 < baseStart_1398964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399048 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1399048 : Nat := 118140960795 + 1399048 * 2 ^ 59
def prefixEnd_1399048 : Nat := 4983230072969 + 3 ^ 40 * 1399048 * 2
def baseEnd_1399048 : Nat := 478922721807698301310601

theorem tailTrace_1399048 : CollatzResearch.WordTrace tailWord_1399048 prefixEnd_1399048 478922721807698301310601 := by
  unfold tailWord_1399048
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513736317747754610326899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34018315090330339480435865 25513736317747754610326899)
  ·
    refine ⟨38270604476621631915490349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25513736317747754610326899 38270604476621631915490349)
    ·
      refine ⟨14351476678733111968308881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38270604476621631915490349 14351476678733111968308881)
      ·
        refine ⟨10763607509049833976231661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14351476678733111968308881 10763607509049833976231661)
        ·
          refine ⟨4036352815893687741086873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10763607509049833976231661 4036352815893687741086873)
          ·
            refine ⟨3027264611920265805815155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4036352815893687741086873 3027264611920265805815155)
            ·
              refine ⟨4540896917880398708722733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027264611920265805815155 4540896917880398708722733)
              ·
                refine ⟨1702836344205149515771025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4540896917880398708722733 1702836344205149515771025)
                ·
                  refine ⟨1277127258153862136828269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1702836344205149515771025 1277127258153862136828269)
                  ·
                    refine ⟨478922721807698301310601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277127258153862136828269 478922721807698301310601)
                    ·
                      rfl

theorem cell22_1399048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1399048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399048 prefixEnd_1399048 := by exact prefixLift 1399048
  have htrace : WordTrace (prefixWord ++ tailWord_1399048) baseStart_1399048 baseEnd_1399048 := by
    simpa [prefixWord, tailWord_1399048, baseEnd_1399048] using wordTrace_append hprefix tailTrace_1399048
  have hstable : (prefixWord ++ tailWord_1399048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399048).length < 2 ^ (prefixWord ++ tailWord_1399048).sum := by decide
  have hdescent : baseEnd_1399048 < baseStart_1399048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399217 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_1399217 : Nat := 118140960795 + 1399217 * 2 ^ 59
def prefixEnd_1399217 : Nat := 4983230072969 + 3 ^ 40 * 1399217 * 2
def baseEnd_1399217 : Nat := 478980573961438193835083

theorem tailTrace_1399217 : CollatzResearch.WordTrace tailWord_1399217 prefixEnd_1399217 478980573961438193835083 := by
  unfold tailWord_1399217
  simp only [CollatzResearch.WordTrace]
  refine ⟨51033636571883251083555905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34022424381255500722370603 51033636571883251083555905)
  ·
    refine ⟨38275227428912438312666929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51033636571883251083555905 38275227428912438312666929)
    ·
      refine ⟨28706420571684328734500197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38275227428912438312666929 28706420571684328734500197)
      ·
        refine ⟨5382453857190811637718787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28706420571684328734500197 5382453857190811637718787)
        ·
          refine ⟨8073680785786217456578181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382453857190811637718787 8073680785786217456578181)
          ·
            refine ⟨1513815147334915773108409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8073680785786217456578181 1513815147334915773108409)
            ·
              refine ⟨1135361360501186829831307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513815147334915773108409 1135361360501186829831307)
              ·
                refine ⟨1703042040751780244746961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135361360501186829831307 1703042040751780244746961)
                ·
                  refine ⟨1277281530563835183560221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1703042040751780244746961 1277281530563835183560221)
                  ·
                    refine ⟨478980573961438193835083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277281530563835183560221 478980573961438193835083)
                    ·
                      rfl

theorem cell22_1399217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_1399217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399217 prefixEnd_1399217 := by exact prefixLift 1399217
  have htrace : WordTrace (prefixWord ++ tailWord_1399217) baseStart_1399217 baseEnd_1399217 := by
    simpa [prefixWord, tailWord_1399217, baseEnd_1399217] using wordTrace_append hprefix tailTrace_1399217
  have hstable : (prefixWord ++ tailWord_1399217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399217).length < 2 ^ (prefixWord ++ tailWord_1399217).sum := by decide
  have hdescent : baseEnd_1399217 < baseStart_1399217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399256 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1399256 : Nat := 118140960795 + 1399256 * 2 ^ 59
def prefixEnd_1399256 : Nat := 4983230072969 + 3 ^ 40 * 1399256 * 2
def baseEnd_1399256 : Nat := 478993924458455092109963

theorem tailTrace_1399256 : CollatzResearch.WordTrace tailWord_1399256 prefixEnd_1399256 478993924458455092109963 := by
  unfold tailWord_1399256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25517529509370980372112811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34023372679161307162817081 25517529509370980372112811)
  ·
    refine ⟨38276294264056470558169217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25517529509370980372112811 38276294264056470558169217)
    ·
      refine ⟨28707220698042352918626913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38276294264056470558169217 28707220698042352918626913)
      ·
        refine ⟨21530415523531764688970185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28707220698042352918626913 21530415523531764688970185)
        ·
          refine ⟨16147811642648823516727639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21530415523531764688970185 16147811642648823516727639)
          ·
            refine ⟨24221717463973235275091459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16147811642648823516727639 24221717463973235275091459)
            ·
              refine ⟨36332576195959852912637189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24221717463973235275091459 36332576195959852912637189)
              ·
                refine ⟨6812358036742472421119473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36332576195959852912637189 6812358036742472421119473)
                ·
                  refine ⟨5109268527556854315839605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6812358036742472421119473 5109268527556854315839605)
                  ·
                    refine ⟨478993924458455092109963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5109268527556854315839605 478993924458455092109963)
                    ·
                      rfl

theorem cell22_1399256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1399256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399256 prefixEnd_1399256 := by exact prefixLift 1399256
  have htrace : WordTrace (prefixWord ++ tailWord_1399256) baseStart_1399256 baseEnd_1399256 := by
    simpa [prefixWord, tailWord_1399256, baseEnd_1399256] using wordTrace_append hprefix tailTrace_1399256
  have hstable : (prefixWord ++ tailWord_1399256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399256).length < 2 ^ (prefixWord ++ tailWord_1399256).sum := by decide
  have hdescent : baseEnd_1399256 < baseStart_1399256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399258 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_1399258 : Nat := 118140960795 + 1399258 * 2 ^ 59
def prefixEnd_1399258 : Nat := 4983230072969 + 3 ^ 40 * 1399258 * 2
def baseEnd_1399258 : Nat := 159664869699775917853319

theorem tailTrace_1399258 : CollatzResearch.WordTrace tailWord_1399258 prefixEnd_1399258 159664869699775917853319 := by
  unfold tailWord_1399258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12758782991183678771449607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34023421309823143390532285 12758782991183678771449607)
  ·
    refine ⟨19138174486775518157174411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12758782991183678771449607 19138174486775518157174411)
    ·
      refine ⟨28707261730163277235761617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19138174486775518157174411 28707261730163277235761617)
      ·
        refine ⟨21530446297622457926821213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28707261730163277235761617 21530446297622457926821213)
        ·
          refine ⟨8073917361608421722557955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21530446297622457926821213 8073917361608421722557955)
          ·
            refine ⟨12110876042412632583836933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073917361608421722557955 12110876042412632583836933)
            ·
              refine ⟨2270789257952368609469425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12110876042412632583836933 2270789257952368609469425)
              ·
                refine ⟨1703091943464276457102069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270789257952368609469425 1703091943464276457102069)
                ·
                  refine ⟨159664869699775917853319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1703091943464276457102069 159664869699775917853319)
                  ·
                    rfl

theorem cell22_1399258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_1399258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399258 prefixEnd_1399258 := by exact prefixLift 1399258
  have htrace : WordTrace (prefixWord ++ tailWord_1399258) baseStart_1399258 baseEnd_1399258 := by
    simpa [prefixWord, tailWord_1399258, baseEnd_1399258] using wordTrace_append hprefix tailTrace_1399258
  have hstable : (prefixWord ++ tailWord_1399258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399258).length < 2 ^ (prefixWord ++ tailWord_1399258).sum := by decide
  have hdescent : baseEnd_1399258 < baseStart_1399258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399288 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1399288 : Nat := 118140960795 + 1399288 * 2 ^ 59
def prefixEnd_1399288 : Nat := 4983230072969 + 3 ^ 40 * 1399288 * 2
def baseEnd_1399288 : Nat := 479004878712417675309865

theorem tailTrace_1399288 : CollatzResearch.WordTrace tailWord_1399288 prefixEnd_1399288 479004878712417675309865 := by
  unfold tailWord_1399288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518113077313015104695259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34024150769750686806260345 25518113077313015104695259)
  ·
    refine ⟨38277169615969522657042889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25518113077313015104695259 38277169615969522657042889)
    ·
      refine ⟨28707877211977141992782167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38277169615969522657042889 28707877211977141992782167)
      ·
        refine ⟨43061815817965712989173251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28707877211977141992782167 43061815817965712989173251)
        ·
          refine ⟨64592723726948569483759877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43061815817965712989173251 64592723726948569483759877)
          ·
            refine ⟨12111135698802856778204977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64592723726948569483759877 12111135698802856778204977)
            ·
              refine ⟨9083351774102142583653733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12111135698802856778204977 9083351774102142583653733)
              ·
                refine ⟨1703128457644151734435075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9083351774102142583653733 1703128457644151734435075)
                ·
                  refine ⟨2554692686466227601652613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703128457644151734435075 2554692686466227601652613)
                  ·
                    refine ⟨479004878712417675309865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2554692686466227601652613 479004878712417675309865)
                    ·
                      rfl

theorem cell22_1399288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1399288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399288 prefixEnd_1399288 := by exact prefixLift 1399288
  have htrace : WordTrace (prefixWord ++ tailWord_1399288) baseStart_1399288 baseEnd_1399288 := by
    simpa [prefixWord, tailWord_1399288, baseEnd_1399288] using wordTrace_append hprefix tailTrace_1399288
  have hstable : (prefixWord ++ tailWord_1399288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399288).length < 2 ^ (prefixWord ++ tailWord_1399288).sum := by decide
  have hdescent : baseEnd_1399288 < baseStart_1399288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399309 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1399309 : Nat := 118140960795 + 1399309 * 2 ^ 59
def prefixEnd_1399309 : Nat := 4983230072969 + 3 ^ 40 * 1399309 * 2
def baseEnd_1399309 : Nat := 159670689147193540178267

theorem tailTrace_1399309 : CollatzResearch.WordTrace tailWord_1399309 prefixEnd_1399309 159670689147193540178267 := by
  unfold tailWord_1399309
  simp only [CollatzResearch.WordTrace]
  refine ⟨51036992087549950795904981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34024661391699967197269987 51036992087549950795904981)
  ·
    refine ⟨1196179502051951971779023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51036992087549950795904981 1196179502051951971779023)
    ·
      refine ⟨1794269253077927957668535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196179502051951971779023 1794269253077927957668535)
      ·
        refine ⟨2691403879616891936502803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794269253077927957668535 2691403879616891936502803)
        ·
          refine ⟨4037105819425337904754205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691403879616891936502803 4037105819425337904754205)
          ·
            refine ⟨1513914682284501714282827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4037105819425337904754205 1513914682284501714282827)
            ·
              refine ⟨2270872023426752571424241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513914682284501714282827 2270872023426752571424241)
              ·
                refine ⟨1703154017570064428568181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270872023426752571424241 1703154017570064428568181)
                ·
                  refine ⟨159670689147193540178267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1703154017570064428568181 159670689147193540178267)
                  ·
                    rfl

theorem cell22_1399309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1399309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399309 prefixEnd_1399309 := by exact prefixLift 1399309
  have htrace : WordTrace (prefixWord ++ tailWord_1399309) baseStart_1399309 baseEnd_1399309 := by
    simpa [prefixWord, tailWord_1399309, baseEnd_1399309] using wordTrace_append hprefix tailTrace_1399309
  have hstable : (prefixWord ++ tailWord_1399309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399309).length < 2 ^ (prefixWord ++ tailWord_1399309).sum := by decide
  have hdescent : baseEnd_1399309 < baseStart_1399309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399320 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_1399320 : Nat := 118140960795 + 1399320 * 2 ^ 59
def prefixEnd_1399320 : Nat := 4983230072969 + 3 ^ 40 * 1399320 * 2
def baseEnd_1399320 : Nat := 159671944322126752836589

theorem tailTrace_1399320 : CollatzResearch.WordTrace tailWord_1399320 prefixEnd_1399320 159671944322126752836589 := by
  unfold tailWord_1399320
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518696645255049837277707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34024928860340066449703609 25518696645255049837277707)
  ·
    refine ⟨38278044967882574755916561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25518696645255049837277707 38278044967882574755916561)
    ·
      refine ⟨28708533725911931066937421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38278044967882574755916561 28708533725911931066937421)
      ·
        refine ⟨10765700147216974150101533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28708533725911931066937421 10765700147216974150101533)
        ·
          refine ⟨4037137555206365306288075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10765700147216974150101533 4037137555206365306288075)
          ·
            refine ⟨6055706332809547959432113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037137555206365306288075 6055706332809547959432113)
            ·
              refine ⟨4541779749607160969574085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055706332809547959432113 4541779749607160969574085)
              ·
                refine ⟨851583703051342681795141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4541779749607160969574085 851583703051342681795141)
                ·
                  refine ⟨159671944322126752836589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851583703051342681795141 159671944322126752836589)
                  ·
                    rfl

theorem cell22_1399320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_1399320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399320 prefixEnd_1399320 := by exact prefixLift 1399320
  have htrace : WordTrace (prefixWord ++ tailWord_1399320) baseStart_1399320 baseEnd_1399320 := by
    simpa [prefixWord, tailWord_1399320, baseEnd_1399320] using wordTrace_append hprefix tailTrace_1399320
  have hstable : (prefixWord ++ tailWord_1399320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399320).length < 2 ^ (prefixWord ++ tailWord_1399320).sum := by decide
  have hdescent : baseEnd_1399320 < baseStart_1399320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399350 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1399350 : Nat := 118140960795 + 1399350 * 2 ^ 59
def prefixEnd_1399350 : Nat := 4983230072969 + 3 ^ 40 * 1399350 * 2
def baseEnd_1399350 : Nat := 479026102579470180259675

theorem tailTrace_1399350 : CollatzResearch.WordTrace tailWord_1399350 prefixEnd_1399350 479026102579470180259675 := by
  unfold tailWord_1399350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189905467525088424884219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34025658320267609865431669 3189905467525088424884219)
  ·
    refine ⟨4784858201287632637326329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3189905467525088424884219 4784858201287632637326329)
    ·
      refine ⟨3588643650965724477994747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4784858201287632637326329 3588643650965724477994747)
      ·
        refine ⟨5382965476448586716992121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588643650965724477994747 5382965476448586716992121)
        ·
          refine ⟨4037224107336440037744091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382965476448586716992121 4037224107336440037744091)
          ·
            refine ⟨6055836161004660056616137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037224107336440037744091 6055836161004660056616137)
            ·
              refine ⟨4541877120753495042462103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055836161004660056616137 4541877120753495042462103)
              ·
                refine ⟨6812815681130242563693155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541877120753495042462103 6812815681130242563693155)
                ·
                  refine ⟨10219223521695363845539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6812815681130242563693155 10219223521695363845539733)
                  ·
                    refine ⟨479026102579470180259675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10219223521695363845539733 479026102579470180259675)
                    ·
                      rfl

theorem cell22_1399350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1399350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399350 prefixEnd_1399350 := by exact prefixLift 1399350
  have htrace : WordTrace (prefixWord ++ tailWord_1399350) baseStart_1399350 baseEnd_1399350 := by
    simpa [prefixWord, tailWord_1399350, baseEnd_1399350] using wordTrace_append hprefix tailTrace_1399350
  have hstable : (prefixWord ++ tailWord_1399350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399350).length < 2 ^ (prefixWord ++ tailWord_1399350).sum := by decide
  have hdescent : baseEnd_1399350 < baseStart_1399350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399363 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 5, 3]
def baseStart_1399363 : Nat := 118140960795 + 1399363 * 2 ^ 59
def prefixEnd_1399363 : Nat := 4983230072969 + 3 ^ 40 * 1399363 * 2
def baseEnd_1399363 : Nat := 479030552745142479684635

theorem tailTrace_1399363 : CollatzResearch.WordTrace tailWord_1399363 prefixEnd_1399363 479030552745142479684635 := by
  unfold tailWord_1399363
  simp only [CollatzResearch.WordTrace]
  refine ⟨51038961629354318018370743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34025974419569545345580495 51038961629354318018370743)
  ·
    refine ⟨76558442444031477027556115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51038961629354318018370743 76558442444031477027556115)
    ·
      refine ⟨114837663666047215541334173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76558442444031477027556115 114837663666047215541334173)
      ·
        refine ⟨43064123874767705828000315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114837663666047215541334173 43064123874767705828000315)
        ·
          refine ⟨64596185812151558742000473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43064123874767705828000315 64596185812151558742000473)
          ·
            refine ⟨48447139359113669056500355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64596185812151558742000473 48447139359113669056500355)
            ·
              refine ⟨72670709038670503584750533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48447139359113669056500355 72670709038670503584750533)
              ·
                refine ⟨13625757944750719422140725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72670709038670503584750533 13625757944750719422140725)
                ·
                  refine ⟨1277414807320379945825693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13625757944750719422140725 1277414807320379945825693)
                  ·
                    refine ⟨479030552745142479684635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277414807320379945825693 479030552745142479684635)
                    ·
                      rfl

theorem cell22_1399363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].length) (baseStart_1399363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399363 prefixEnd_1399363 := by exact prefixLift 1399363
  have htrace : WordTrace (prefixWord ++ tailWord_1399363) baseStart_1399363 baseEnd_1399363 := by
    simpa [prefixWord, tailWord_1399363, baseEnd_1399363] using wordTrace_append hprefix tailTrace_1399363
  have hstable : (prefixWord ++ tailWord_1399363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399363).length < 2 ^ (prefixWord ++ tailWord_1399363).sum := by decide
  have hdescent : baseEnd_1399363 < baseStart_1399363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399378 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1399378 : Nat := 118140960795 + 1399378 * 2 ^ 59
def prefixEnd_1399378 : Nat := 4983230072969 + 3 ^ 40 * 1399378 * 2
def baseEnd_1399378 : Nat := 479035687551687440559589

theorem tailTrace_1399378 : CollatzResearch.WordTrace tailWord_1399378 prefixEnd_1399378 479035687551687440559589 := by
  unfold tailWord_1399378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759877181074993895041697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34026339149533317053444525 12759877181074993895041697)
  ·
    refine ⟨9569907885806245421281273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12759877181074993895041697 9569907885806245421281273)
    ·
      refine ⟨7177430914354684065960955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9569907885806245421281273 7177430914354684065960955)
      ·
        refine ⟨10766146371532026098941433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7177430914354684065960955 10766146371532026098941433)
        ·
          refine ⟨8074609778649019574206075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10766146371532026098941433 8074609778649019574206075)
          ·
            refine ⟨12111914667973529361309113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074609778649019574206075 12111914667973529361309113)
            ·
              refine ⟨9083936000980147020981835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12111914667973529361309113 9083936000980147020981835)
              ·
                refine ⟨13625904001470220531472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9083936000980147020981835 13625904001470220531472753)
                ·
                  refine ⟨10219428001102665398604565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13625904001470220531472753 10219428001102665398604565)
                  ·
                    refine ⟨479035687551687440559589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10219428001102665398604565 479035687551687440559589)
                    ·
                      rfl

theorem cell22_1399378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1399378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399378 prefixEnd_1399378 := by exact prefixLift 1399378
  have htrace : WordTrace (prefixWord ++ tailWord_1399378) baseStart_1399378 baseEnd_1399378 := by
    simpa [prefixWord, tailWord_1399378, baseEnd_1399378] using wordTrace_append hprefix tailTrace_1399378
  have hstable : (prefixWord ++ tailWord_1399378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399378).length < 2 ^ (prefixWord ++ tailWord_1399378).sum := by decide
  have hdescent : baseEnd_1399378 < baseStart_1399378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399487 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 2, 3]
def baseStart_1399487 : Nat := 118140960795 + 1399487 * 2 ^ 59
def prefixEnd_1399487 : Nat := 4983230072969 + 3 ^ 40 * 1399487 * 2
def baseEnd_1399487 : Nat := 479073000479247489584255

theorem tailTrace_1399487 : CollatzResearch.WordTrace tailWord_1399487 prefixEnd_1399487 479073000479247489584255 := by
  unfold tailWord_1399487
  simp only [CollatzResearch.WordTrace]
  refine ⟨51043484280905087195884715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34028989520603391463923143 51043484280905087195884715)
  ·
    refine ⟨76565226421357630793827073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51043484280905087195884715 76565226421357630793827073)
    ·
      refine ⟨57423919816018223095370305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76565226421357630793827073 57423919816018223095370305)
      ·
        refine ⟨43067939862013667321527729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57423919816018223095370305 43067939862013667321527729)
        ·
          refine ⟨32300954896510250491145797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43067939862013667321527729 32300954896510250491145797)
          ·
            refine ⟨6056429043095671967089837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32300954896510250491145797 6056429043095671967089837)
            ·
              refine ⟨2271160891160876987658689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6056429043095671967089837 2271160891160876987658689)
              ·
                refine ⟨1703370668370657740744017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271160891160876987658689 1703370668370657740744017)
                ·
                  refine ⟨1277528001277993305558013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1703370668370657740744017 1277528001277993305558013)
                  ·
                    refine ⟨479073000479247489584255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277528001277993305558013 479073000479247489584255)
                    ·
                      rfl

theorem cell22_1399487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_1399487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399487 prefixEnd_1399487 := by exact prefixLift 1399487
  have htrace : WordTrace (prefixWord ++ tailWord_1399487) baseStart_1399487 baseEnd_1399487 := by
    simpa [prefixWord, tailWord_1399487, baseEnd_1399487] using wordTrace_append hprefix tailTrace_1399487
  have hstable : (prefixWord ++ tailWord_1399487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399487).length < 2 ^ (prefixWord ++ tailWord_1399487).sum := by decide
  have hdescent : baseEnd_1399487 < baseStart_1399487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399489 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 6]
def baseStart_1399489 : Nat := 118140960795 + 1399489 * 2 ^ 59
def prefixEnd_1399489 : Nat := 4983230072969 + 3 ^ 40 * 1399489 * 2
def baseEnd_1399489 : Nat := 159691228373373383678083

theorem tailTrace_1399489 : CollatzResearch.WordTrace tailWord_1399489 prefixEnd_1399489 159691228373373383678083 := by
  unfold tailWord_1399489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51043557226897841537457521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34029038151265227691638347 51043557226897841537457521)
  ·
    refine ⟨38282667920173381153093141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51043557226897841537457521 38282667920173381153093141)
    ·
      refine ⟨1794500058758127241551241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38282667920173381153093141 1794500058758127241551241)
      ·
        refine ⟨1345875044068595431163431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794500058758127241551241 1345875044068595431163431)
        ·
          refine ⟨2018812566102893146745147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345875044068595431163431 2018812566102893146745147)
          ·
            refine ⟨3028218849154339720117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018812566102893146745147 3028218849154339720117721)
            ·
              refine ⟨2271164136865754790088291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028218849154339720117721 2271164136865754790088291)
              ·
                refine ⟨3406746205298632185132437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271164136865754790088291 3406746205298632185132437)
                ·
                  refine ⟨159691228373373383678083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3406746205298632185132437 159691228373373383678083)
                  ·
                    rfl

theorem cell22_1399489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_1399489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399489 prefixEnd_1399489 := by exact prefixLift 1399489
  have htrace : WordTrace (prefixWord ++ tailWord_1399489) baseStart_1399489 baseEnd_1399489 := by
    simpa [prefixWord, tailWord_1399489, baseEnd_1399489] using wordTrace_append hprefix tailTrace_1399489
  have hstable : (prefixWord ++ tailWord_1399489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399489).length < 2 ^ (prefixWord ++ tailWord_1399489).sum := by decide
  have hdescent : baseEnd_1399489 < baseStart_1399489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399607 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 4]
def baseStart_1399607 : Nat := 118140960795 + 1399607 * 2 ^ 59
def prefixEnd_1399607 : Nat := 4983230072969 + 3 ^ 40 * 1399607 * 2
def baseEnd_1399607 : Nat := 159704692977202392194629

theorem tailTrace_1399607 : CollatzResearch.WordTrace tailWord_1399607 prefixEnd_1399607 159704692977202392194629 := by
  unfold tailWord_1399607
  simp only [CollatzResearch.WordTrace]
  refine ⟨51047861040470347690253075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34031907360313565126835383 51047861040470347690253075)
  ·
    refine ⟨76571791560705521535379613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51047861040470347690253075 76571791560705521535379613)
    ·
      refine ⟨28714421835264570575767355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76571791560705521535379613 28714421835264570575767355)
      ·
        refine ⟨43071632752896855863651033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28714421835264570575767355 43071632752896855863651033)
        ·
          refine ⟨32303724564672641897738275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43071632752896855863651033 32303724564672641897738275)
          ·
            refine ⟨48455586847008962846607413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32303724564672641897738275 48455586847008962846607413)
            ·
              refine ⟨4542711266907090266869445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48455586847008962846607413 4542711266907090266869445)
              ·
                refine ⟨851758362545079425038021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4542711266907090266869445 851758362545079425038021)
                ·
                  refine ⟨159704692977202392194629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851758362545079425038021 159704692977202392194629)
                  ·
                    rfl

theorem cell22_1399607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 4].length) (baseStart_1399607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399607 prefixEnd_1399607 := by exact prefixLift 1399607
  have htrace : WordTrace (prefixWord ++ tailWord_1399607) baseStart_1399607 baseEnd_1399607 := by
    simpa [prefixWord, tailWord_1399607, baseEnd_1399607] using wordTrace_append hprefix tailTrace_1399607
  have hstable : (prefixWord ++ tailWord_1399607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399607).length < 2 ^ (prefixWord ++ tailWord_1399607).sum := by decide
  have hdescent : baseEnd_1399607 < baseStart_1399607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399656 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1399656 : Nat := 118140960795 + 1399656 * 2 ^ 59
def prefixEnd_1399656 : Nat := 4983230072969 + 3 ^ 40 * 1399656 * 2
def baseEnd_1399656 : Nat := 479130852632987382108737

theorem tailTrace_1399656 : CollatzResearch.WordTrace tailWord_1399656 prefixEnd_1399656 479130852632987382108737 := by
  unfold tailWord_1399656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25524824108646414529393411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34033098811528552705857881 25524824108646414529393411)
  ·
    refine ⟨38287236162969621794090117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25524824108646414529393411 38287236162969621794090117)
    ·
      refine ⟨7178856780556804086391897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38287236162969621794090117 7178856780556804086391897)
      ·
        refine ⟨5384142585417603064793923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178856780556804086391897 5384142585417603064793923)
        ·
          refine ⟨8076213878126404597190885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384142585417603064793923 8076213878126404597190885)
          ·
            refine ⟨1514290102148700861973291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8076213878126404597190885 1514290102148700861973291)
            ·
              refine ⟨2271435153223051292959937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514290102148700861973291 2271435153223051292959937)
              ·
                refine ⟨1703576364917288469719953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271435153223051292959937 1703576364917288469719953)
                ·
                  refine ⟨1277682273687966352289965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1703576364917288469719953 1277682273687966352289965)
                  ·
                    refine ⟨479130852632987382108737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277682273687966352289965 479130852632987382108737)
                    ·
                      rfl

theorem cell22_1399656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1399656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399656 prefixEnd_1399656 := by exact prefixLift 1399656
  have htrace : WordTrace (prefixWord ++ tailWord_1399656) baseStart_1399656 baseEnd_1399656 := by
    simpa [prefixWord, tailWord_1399656, baseEnd_1399656] using wordTrace_append hprefix tailTrace_1399656
  have hstable : (prefixWord ++ tailWord_1399656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399656).length < 2 ^ (prefixWord ++ tailWord_1399656).sum := by decide
  have hdescent : baseEnd_1399656 < baseStart_1399656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399667 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 3, 3]
def baseStart_1399667 : Nat := 118140960795 + 1399667 * 2 ^ 59
def prefixEnd_1399667 : Nat := 4983230072969 + 3 ^ 40 * 1399667 * 2
def baseEnd_1399667 : Nat := 479134618157787020083703

theorem tailTrace_1399667 : CollatzResearch.WordTrace tailWord_1399667 prefixEnd_1399667 479134618157787020083703 := by
  unfold tailWord_1399667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51050049420252977937437255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34033366280168651958291503 51050049420252977937437255)
  ·
    refine ⟨76575074130379466906155883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51050049420252977937437255 76575074130379466906155883)
    ·
      refine ⟨114862611195569200359233825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76575074130379466906155883 114862611195569200359233825)
      ·
        refine ⟨86146958396676900269425369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114862611195569200359233825 86146958396676900269425369)
        ·
          refine ⟨64610218797507675202069027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86146958396676900269425369 64610218797507675202069027)
          ·
            refine ⟨96915328196261512803103541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64610218797507675202069027 96915328196261512803103541)
            ·
              refine ⟨9085812018399516825290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96915328196261512803103541 9085812018399516825290957)
              ·
                refine ⟨3407179506899818809484109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085812018399516825290957 3407179506899818809484109)
                ·
                  refine ⟨1277692315087432053556541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3407179506899818809484109 1277692315087432053556541)
                  ·
                    refine ⟨479134618157787020083703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277692315087432053556541 479134618157787020083703)
                    ·
                      rfl

theorem cell22_1399667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 3].length) (baseStart_1399667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399667 prefixEnd_1399667 := by exact prefixLift 1399667
  have htrace : WordTrace (prefixWord ++ tailWord_1399667) baseStart_1399667 baseEnd_1399667 := by
    simpa [prefixWord, tailWord_1399667, baseEnd_1399667] using wordTrace_append hprefix tailTrace_1399667
  have hstable : (prefixWord ++ tailWord_1399667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399667).length < 2 ^ (prefixWord ++ tailWord_1399667).sum := by decide
  have hdescent : baseEnd_1399667 < baseStart_1399667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399701 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_1399701 : Nat := 118140960795 + 1399701 * 2 ^ 59
def prefixEnd_1399701 : Nat := 4983230072969 + 3 ^ 40 * 1399701 * 2
def baseEnd_1399701 : Nat := 479146257052622264733599

theorem tailTrace_1399701 : CollatzResearch.WordTrace tailWord_1399701 prefixEnd_1399701 479146257052622264733599 := by
  unfold tailWord_1399701
  simp only [CollatzResearch.WordTrace]
  refine ⟨51051289502129801744174957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34034193001419867829449971 51051289502129801744174957)
  ·
    refine ⟨19144233563298675654065609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51051289502129801744174957 19144233563298675654065609)
    ·
      refine ⟨14358175172474006740549207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19144233563298675654065609 14358175172474006740549207)
      ·
        refine ⟨21537262758711010110823811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14358175172474006740549207 21537262758711010110823811)
        ·
          refine ⟨32305894138066515166235717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21537262758711010110823811 32305894138066515166235717)
          ·
            refine ⟨6057355150887471593669197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32305894138066515166235717 6057355150887471593669197)
            ·
              refine ⟨2271508181582801847625949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6057355150887471593669197 2271508181582801847625949)
              ·
                refine ⟨851815568093550692859731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271508181582801847625949 851815568093550692859731)
                ·
                  refine ⟨1277723352140326039289597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851815568093550692859731 1277723352140326039289597)
                  ·
                    refine ⟨479146257052622264733599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277723352140326039289597 479146257052622264733599)
                    ·
                      rfl

theorem cell22_1399701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_1399701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399701 prefixEnd_1399701 := by exact prefixLift 1399701
  have htrace : WordTrace (prefixWord ++ tailWord_1399701) baseStart_1399701 baseEnd_1399701 := by
    simpa [prefixWord, tailWord_1399701, baseEnd_1399701] using wordTrace_append hprefix tailTrace_1399701
  have hstable : (prefixWord ++ tailWord_1399701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399701).length < 2 ^ (prefixWord ++ tailWord_1399701).sum := by decide
  have hdescent : baseEnd_1399701 < baseStart_1399701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399742 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1399742 : Nat := 118140960795 + 1399742 * 2 ^ 59
def prefixEnd_1399742 : Nat := 4983230072969 + 3 ^ 40 * 1399742 * 2
def baseEnd_1399742 : Nat := 159720097396837274819491

theorem tailTrace_1399742 : CollatzResearch.WordTrace tailWord_1399742 prefixEnd_1399742 159720097396837274819491 := by
  unfold tailWord_1399742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381598111872658218302185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34035189929987510497611653 6381598111872658218302185)
  ·
    refine ⟨4786198583904493663726639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6381598111872658218302185 4786198583904493663726639)
    ·
      refine ⟨7179297875856740495589959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786198583904493663726639 7179297875856740495589959)
      ·
        refine ⟨10768946813785110743384939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179297875856740495589959 10768946813785110743384939)
        ·
          refine ⟨16153420220677666115077409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10768946813785110743384939 16153420220677666115077409)
          ·
            refine ⟨12115065165508249586308057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16153420220677666115077409 12115065165508249586308057)
            ·
              refine ⟨9086298874131187189731043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12115065165508249586308057 9086298874131187189731043)
              ·
                refine ⟨13629448311196780784596565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9086298874131187189731043 13629448311196780784596565)
                ·
                  refine ⟨159720097396837274819491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13629448311196780784596565 159720097396837274819491)
                  ·
                    rfl

theorem cell22_1399742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1399742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399742 prefixEnd_1399742 := by exact prefixLift 1399742
  have htrace : WordTrace (prefixWord ++ tailWord_1399742) baseStart_1399742 baseEnd_1399742 := by
    simpa [prefixWord, tailWord_1399742, baseEnd_1399742] using wordTrace_append hprefix tailTrace_1399742
  have hstable : (prefixWord ++ tailWord_1399742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399742).length < 2 ^ (prefixWord ++ tailWord_1399742).sum := by decide
  have hdescent : baseEnd_1399742 < baseStart_1399742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399744 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_1399744 : Nat := 118140960795 + 1399744 * 2 ^ 59
def prefixEnd_1399744 : Nat := 4983230072969 + 3 ^ 40 * 1399744 * 2
def baseEnd_1399744 : Nat := 479160976831384485908467

theorem tailTrace_1399744 : CollatzResearch.WordTrace tailWord_1399744 prefixEnd_1399744 479160976831384485908467 := by
  unfold tailWord_1399744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25526428920487010043995143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34035238560649346725326857 25526428920487010043995143)
  ·
    refine ⟨38289643380730515065992715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25526428920487010043995143 38289643380730515065992715)
    ·
      refine ⟨57434465071095772598989073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38289643380730515065992715 57434465071095772598989073)
      ·
        refine ⟨43075848803321829449241805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57434465071095772598989073 43075848803321829449241805)
        ·
          refine ⟨16153443301245686043465677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43075848803321829449241805 16153443301245686043465677)
          ·
            refine ⟨6057541237967132266299629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16153443301245686043465677 6057541237967132266299629)
            ·
              refine ⟨2271577964237674599862361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6057541237967132266299629 2271577964237674599862361)
              ·
                refine ⟨1703683473178255949896771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271577964237674599862361 1703683473178255949896771)
                ·
                  refine ⟨2555525209767383924845157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703683473178255949896771 2555525209767383924845157)
                  ·
                    refine ⟨479160976831384485908467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2555525209767383924845157 479160976831384485908467)
                    ·
                      rfl

theorem cell22_1399744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_1399744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399744 prefixEnd_1399744 := by exact prefixLift 1399744
  have htrace : WordTrace (prefixWord ++ tailWord_1399744) baseStart_1399744 baseEnd_1399744 := by
    simpa [prefixWord, tailWord_1399744, baseEnd_1399744] using wordTrace_append hprefix tailTrace_1399744
  have hstable : (prefixWord ++ tailWord_1399744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399744).length < 2 ^ (prefixWord ++ tailWord_1399744).sum := by decide
  have hdescent : baseEnd_1399744 < baseStart_1399744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399804 : List Nat := [2, 2, 2, 1, 2, 4, 3, 6]
def baseStart_1399804 : Nat := 118140960795 + 1399804 * 2 ^ 59
def prefixEnd_1399804 : Nat := 4983230072969 + 3 ^ 40 * 1399804 * 2
def baseEnd_1399804 : Nat := 53242390673062703267587

theorem tailTrace_1399804 : CollatzResearch.WordTrace tailWord_1399804 prefixEnd_1399804 53242390673062703267587 := by
  unfold tailWord_1399804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527523110378325167587233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34036697480504433556782977 25527523110378325167587233)
  ·
    refine ⟨19145642332783743875690425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25527523110378325167587233 19145642332783743875690425)
    ·
      refine ⟨14359231749587807906767819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19145642332783743875690425 14359231749587807906767819)
      ·
        refine ⟨21538847624381711860151729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14359231749587807906767819 21538847624381711860151729)
        ·
          refine ⟨16154135718286283895113797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21538847624381711860151729 16154135718286283895113797)
          ·
            refine ⟨3028900447178678230333837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16154135718286283895113797 3028900447178678230333837)
            ·
              refine ⟨1135837667692004336375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3028900447178678230333837 1135837667692004336375189)
              ·
                refine ⟨53242390673062703267587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1135837667692004336375189 53242390673062703267587)
                ·
                  rfl

theorem cell22_1399804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_1399804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399804 prefixEnd_1399804 := by exact prefixLift 1399804
  have htrace : WordTrace (prefixWord ++ tailWord_1399804) baseStart_1399804 baseEnd_1399804 := by
    simpa [prefixWord, tailWord_1399804, baseEnd_1399804] using wordTrace_append hprefix tailTrace_1399804
  have hstable : (prefixWord ++ tailWord_1399804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399804).length < 2 ^ (prefixWord ++ tailWord_1399804).sum := by decide
  have hdescent : baseEnd_1399804 < baseStart_1399804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399806 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1399806 : Nat := 118140960795 + 1399806 * 2 ^ 59
def prefixEnd_1399806 : Nat := 4983230072969 + 3 ^ 40 * 1399806 * 2
def baseEnd_1399806 : Nat := 479182200698436990858277

theorem tailTrace_1399806 : CollatzResearch.WordTrace tailWord_1399806 prefixEnd_1399806 479182200698436990858277 := by
  unfold tailWord_1399806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381889895843675584593409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34036746111166269784498181 6381889895843675584593409)
  ·
    refine ⟨4786417421882756688445057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6381889895843675584593409 4786417421882756688445057)
    ·
      refine ⟨3589813066412067516333793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4786417421882756688445057 3589813066412067516333793)
      ·
        refine ⟨2692359799809050637250345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3589813066412067516333793 2692359799809050637250345)
        ·
          refine ⟨2019269849856787977937759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692359799809050637250345 2019269849856787977937759)
          ·
            refine ⟨3028904774785181966906639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019269849856787977937759 3028904774785181966906639)
            ·
              refine ⟨4543357162177772950359959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028904774785181966906639 4543357162177772950359959)
              ·
                refine ⟨6815035743266659425539939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543357162177772950359959 6815035743266659425539939)
                ·
                  refine ⟨10222553614899989138309909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815035743266659425539939 10222553614899989138309909)
                  ·
                    refine ⟨479182200698436990858277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10222553614899989138309909 479182200698436990858277)
                    ·
                      rfl

theorem cell22_1399806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1399806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399806 prefixEnd_1399806 := by exact prefixLift 1399806
  have htrace : WordTrace (prefixWord ++ tailWord_1399806) baseStart_1399806 baseEnd_1399806 := by
    simpa [prefixWord, tailWord_1399806, baseEnd_1399806] using wordTrace_append hprefix tailTrace_1399806
  have hstable : (prefixWord ++ tailWord_1399806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399806).length < 2 ^ (prefixWord ++ tailWord_1399806).sum := by decide
  have hdescent : baseEnd_1399806 < baseStart_1399806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399810 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1399810 : Nat := 118140960795 + 1399810 * 2 ^ 59
def prefixEnd_1399810 : Nat := 4983230072969 + 3 ^ 40 * 1399810 * 2
def baseEnd_1399810 : Nat := 159727856660060771252755

theorem tailTrace_1399810 : CollatzResearch.WordTrace tailWord_1399810 prefixEnd_1399810 159727856660060771252755 := by
  unfold tailWord_1399810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763816264683728339973221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34036843372489942239928589 12763816264683728339973221)
  ·
    refine ⟨2393215549628199063744979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12763816264683728339973221 2393215549628199063744979)
    ·
      refine ⟨3589823324442298595617469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393215549628199063744979 3589823324442298595617469)
      ·
        refine ⟨1346183746665861973356551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3589823324442298595617469 1346183746665861973356551)
        ·
          refine ⟨2019275619998792960034827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346183746665861973356551 2019275619998792960034827)
          ·
            refine ⟨3028913429998189440052241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019275619998792960034827 3028913429998189440052241)
            ·
              refine ⟨2271685072498642080039181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3028913429998189440052241 2271685072498642080039181)
              ·
                refine ⟨851881902186990780014693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271685072498642080039181 851881902186990780014693)
                ·
                  refine ⟨159727856660060771252755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851881902186990780014693 159727856660060771252755)
                  ·
                    rfl

theorem cell22_1399810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1399810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399810 prefixEnd_1399810 := by exact prefixLift 1399810
  have htrace : WordTrace (prefixWord ++ tailWord_1399810) baseStart_1399810 baseEnd_1399810 := by
    simpa [prefixWord, tailWord_1399810, baseEnd_1399810] using wordTrace_append hprefix tailTrace_1399810
  have hstable : (prefixWord ++ tailWord_1399810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399810).length < 2 ^ (prefixWord ++ tailWord_1399810).sum := by decide
  have hdescent : baseEnd_1399810 < baseStart_1399810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399870 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1399870 : Nat := 118140960795 + 1399870 * 2 ^ 59
def prefixEnd_1399870 : Nat := 4983230072969 + 3 ^ 40 * 1399870 * 2
def baseEnd_1399870 : Nat := 479204109206362157258081

theorem tailTrace_1399870 : CollatzResearch.WordTrace tailWord_1399870 prefixEnd_1399870 479204109206362157258081 := by
  unfold tailWord_1399870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382181679814692950884633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34038302292345029071384709 6382181679814692950884633)
  ·
    refine ⟨4786636259861019713163475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382181679814692950884633 4786636259861019713163475)
    ·
      refine ⟨7179954389791529569745213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786636259861019713163475 7179954389791529569745213)
      ·
        refine ⟨2692482896171823588654455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7179954389791529569745213 2692482896171823588654455)
        ·
          refine ⟨4038724344257735382981683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692482896171823588654455 4038724344257735382981683)
          ·
            refine ⟨6058086516386603074472525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038724344257735382981683 6058086516386603074472525)
            ·
              refine ⟨2271782443644976152927197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6058086516386603074472525 2271782443644976152927197)
              ·
                refine ⟨851918416366866057347699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271782443644976152927197 851918416366866057347699)
                ·
                  refine ⟨1277877624550299086021549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851918416366866057347699 1277877624550299086021549)
                  ·
                    refine ⟨479204109206362157258081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1277877624550299086021549 479204109206362157258081)
                    ·
                      rfl

theorem cell22_1399870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1399870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399870 prefixEnd_1399870 := by exact prefixLift 1399870
  have htrace : WordTrace (prefixWord ++ tailWord_1399870) baseStart_1399870 baseEnd_1399870 := by
    simpa [prefixWord, tailWord_1399870, baseEnd_1399870] using wordTrace_append hprefix tailTrace_1399870
  have hstable : (prefixWord ++ tailWord_1399870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399870).length < 2 ^ (prefixWord ++ tailWord_1399870).sum := by decide
  have hdescent : baseEnd_1399870 < baseStart_1399870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399877 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 8]
def baseStart_1399877 : Nat := 118140960795 + 1399877 * 2 ^ 59
def prefixEnd_1399877 : Nat := 4983230072969 + 3 ^ 40 * 1399877 * 2
def baseEnd_1399877 : Nat := 159735501816472157444353

theorem tailTrace_1399877 : CollatzResearch.WordTrace tailWord_1399877 prefixEnd_1399877 159735501816472157444353 := by
  unfold tailWord_1399877
  simp only [CollatzResearch.WordTrace]
  refine ⟨51057708749492183802581885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34038472499661455868387923 51057708749492183802581885)
  ·
    refine ⟨19146640781059568925968207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51057708749492183802581885 19146640781059568925968207)
    ·
      refine ⟨28719961171589353388952311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19146640781059568925968207 28719961171589353388952311)
      ·
        refine ⟨43079941757384030083428467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28719961171589353388952311 43079941757384030083428467)
        ·
          refine ⟨64619912636076045125142701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43079941757384030083428467 64619912636076045125142701)
          ·
            refine ⟨24232467238528516921928513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64619912636076045125142701 24232467238528516921928513)
            ·
              refine ⟨18174350428896387691446385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24232467238528516921928513 18174350428896387691446385)
              ·
                refine ⟨13630762821672290768584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18174350428896387691446385 13630762821672290768584789)
                ·
                  refine ⟨159735501816472157444353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13630762821672290768584789 159735501816472157444353)
                  ·
                    rfl

theorem cell22_1399877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_1399877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399877 prefixEnd_1399877 := by exact prefixLift 1399877
  have htrace : WordTrace (prefixWord ++ tailWord_1399877) baseStart_1399877 baseEnd_1399877 := by
    simpa [prefixWord, tailWord_1399877, baseEnd_1399877] using wordTrace_append hprefix tailTrace_1399877
  have hstable : (prefixWord ++ tailWord_1399877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399877).length < 2 ^ (prefixWord ++ tailWord_1399877).sum := by decide
  have hdescent : baseEnd_1399877 < baseStart_1399877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399909 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1399909 : Nat := 118140960795 + 1399909 * 2 ^ 59
def prefixEnd_1399909 : Nat := 4983230072969 + 3 ^ 40 * 1399909 * 2
def baseEnd_1399909 : Nat := 479217459703379055532961

theorem tailTrace_1399909 : CollatzResearch.WordTrace tailWord_1399909 prefixEnd_1399909 479217459703379055532961 := by
  unfold tailWord_1399909
  simp only [CollatzResearch.WordTrace]
  refine ⟨51058875885376253267746781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34039250590250835511831187 51058875885376253267746781)
  ·
    refine ⟨19147078457016094975405043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51058875885376253267746781 19147078457016094975405043)
    ·
      refine ⟨28720617685524142463107565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19147078457016094975405043 28720617685524142463107565)
      ·
        refine ⟨10770231632071553423665337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28720617685524142463107565 10770231632071553423665337)
        ·
          refine ⟨8077673724053665067749003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10770231632071553423665337 8077673724053665067749003)
          ·
            refine ⟨12116510586080497601623505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077673724053665067749003 12116510586080497601623505)
            ·
              refine ⟨9087382939560373201217629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12116510586080497601623505 9087382939560373201217629)
              ·
                refine ⟨3407768602335139950456611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9087382939560373201217629 3407768602335139950456611)
                ·
                  refine ⟨5111652903502709925684917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407768602335139950456611 5111652903502709925684917)
                  ·
                    refine ⟨479217459703379055532961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5111652903502709925684917 479217459703379055532961)
                    ·
                      rfl

theorem cell22_1399909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1399909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399909 prefixEnd_1399909 := by exact prefixLift 1399909
  have htrace : WordTrace (prefixWord ++ tailWord_1399909) baseStart_1399909 baseEnd_1399909 := by
    simpa [prefixWord, tailWord_1399909, baseEnd_1399909] using wordTrace_append hprefix tailTrace_1399909
  have hstable : (prefixWord ++ tailWord_1399909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399909).length < 2 ^ (prefixWord ++ tailWord_1399909).sum := by decide
  have hdescent : baseEnd_1399909 < baseStart_1399909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399926 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1399926 : Nat := 118140960795 + 1399926 * 2 ^ 59
def prefixEnd_1399926 : Nat := 4983230072969 + 3 ^ 40 * 1399926 * 2
def baseEnd_1399926 : Nat := 479223279150796677857909

theorem tailTrace_1399926 : CollatzResearch.WordTrace tailWord_1399926 prefixEnd_1399926 479223279150796677857909 := by
  unfold tailWord_1399926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191218495394666573194727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34039663950876443447410421 3191218495394666573194727)
  ·
    refine ⟨4786827743091999859792091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3191218495394666573194727 4786827743091999859792091)
    ·
      refine ⟨7180241614637999789688137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786827743091999859792091 7180241614637999789688137)
      ·
        refine ⟨5385181210978499842266103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180241614637999789688137 5385181210978499842266103)
        ·
          refine ⟨8077771816467749763399155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385181210978499842266103 8077771816467749763399155)
          ·
            refine ⟨12116657724701624645098733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077771816467749763399155 12116657724701624645098733)
            ·
              refine ⟨4543746646763109241912025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12116657724701624645098733 4543746646763109241912025)
              ·
                refine ⟨3407809985072331931434019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543746646763109241912025 3407809985072331931434019)
                ·
                  refine ⟨5111714977608497897151029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407809985072331931434019 5111714977608497897151029)
                  ·
                    refine ⟨479223279150796677857909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5111714977608497897151029 479223279150796677857909)
                    ·
                      rfl

theorem cell22_1399926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1399926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399926 prefixEnd_1399926 := by exact prefixLift 1399926
  have htrace : WordTrace (prefixWord ++ tailWord_1399926) baseStart_1399926 baseEnd_1399926 := by
    simpa [prefixWord, tailWord_1399926, baseEnd_1399926] using wordTrace_append hprefix tailTrace_1399926
  have hstable : (prefixWord ++ tailWord_1399926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399926).length < 2 ^ (prefixWord ++ tailWord_1399926).sum := by decide
  have hdescent : baseEnd_1399926 < baseStart_1399926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399969 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1399969 : Nat := 118140960795 + 1399969 * 2 ^ 59
def prefixEnd_1399969 : Nat := 4983230072969 + 3 ^ 40 * 1399969 * 2
def baseEnd_1399969 : Nat := 479237998929558899032777

theorem tailTrace_1399969 : CollatzResearch.WordTrace tailWord_1399969 prefixEnd_1399969 479237998929558899032777 := by
  unfold tailWord_1399969
  simp only [CollatzResearch.WordTrace]
  refine ⟨51061064265158883514930961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34040709510105922343287307 51061064265158883514930961)
  ·
    refine ⟨38295798198869162636198221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51061064265158883514930961 38295798198869162636198221)
    ·
      refine ⟨14360924324575935988574333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38295798198869162636198221 14360924324575935988574333)
      ·
        refine ⟨5385346621715975995715375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14360924324575935988574333 5385346621715975995715375)
        ·
          refine ⟨8078019932573963993573063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385346621715975995715375 8078019932573963993573063)
          ·
            refine ⟨12117029898860945990359595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8078019932573963993573063 12117029898860945990359595)
            ·
              refine ⟨18175544848291418985539393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12117029898860945990359595 18175544848291418985539393)
              ·
                refine ⟨13631658636218564239154545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18175544848291418985539393 13631658636218564239154545)
                ·
                  refine ⟨10223743977163923179365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13631658636218564239154545 10223743977163923179365909)
                  ·
                    refine ⟨479237998929558899032777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10223743977163923179365909 479237998929558899032777)
                    ·
                      rfl

theorem cell22_1399969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1399969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399969 prefixEnd_1399969 := by exact prefixLift 1399969
  have htrace : WordTrace (prefixWord ++ tailWord_1399969) baseStart_1399969 baseEnd_1399969 := by
    simpa [prefixWord, tailWord_1399969, baseEnd_1399969] using wordTrace_append hprefix tailTrace_1399969
  have hstable : (prefixWord ++ tailWord_1399969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399969).length < 2 ^ (prefixWord ++ tailWord_1399969).sum := by decide
  have hdescent : baseEnd_1399969 < baseStart_1399969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399999 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_1399999 : Nat := 118140960795 + 1399999 * 2 ^ 59
def prefixEnd_1399999 : Nat := 4983230072969 + 3 ^ 40 * 1399999 * 2
def baseEnd_1399999 : Nat := 479248268542648820782685

theorem tailTrace_1399999 : CollatzResearch.WordTrace tailWord_1399999 prefixEnd_1399999 479248268542648820782685 := by
  unfold tailWord_1399999
  simp only [CollatzResearch.WordTrace]
  refine ⟨51062158455050198638523051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34041438970033465759015367 51062158455050198638523051)
  ·
    refine ⟨76593237682575297957784577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51062158455050198638523051 76593237682575297957784577)
    ·
      refine ⟨57444928261931473468338433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76593237682575297957784577 57444928261931473468338433)
      ·
        refine ⟨43083696196448605101253825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57444928261931473468338433 43083696196448605101253825)
        ·
          refine ⟨32312772147336453825940369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43083696196448605101253825 32312772147336453825940369)
          ·
            refine ⟨24234579110502340369455277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32312772147336453825940369 24234579110502340369455277)
            ·
              refine ⟨9087967166438377638545729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24234579110502340369455277 9087967166438377638545729)
              ·
                refine ⟨6815975374828783228909297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9087967166438377638545729 6815975374828783228909297)
                ·
                  refine ⟨5111981531121587421681973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6815975374828783228909297 5111981531121587421681973)
                  ·
                    refine ⟨479248268542648820782685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5111981531121587421681973 479248268542648820782685)
                    ·
                      rfl

theorem cell22_1399999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_1399999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1399999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1399999 prefixEnd_1399999 := by exact prefixLift 1399999
  have htrace : WordTrace (prefixWord ++ tailWord_1399999) baseStart_1399999 baseEnd_1399999 := by
    simpa [prefixWord, tailWord_1399999, baseEnd_1399999] using wordTrace_append hprefix tailTrace_1399999
  have hstable : (prefixWord ++ tailWord_1399999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399999).length < 2 ^ (prefixWord ++ tailWord_1399999).sum := by decide
  have hdescent : baseEnd_1399999 < baseStart_1399999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400018 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1400018 : Nat := 118140960795 + 1400018 * 2 ^ 59
def prefixEnd_1400018 : Nat := 4983230072969 + 3 ^ 40 * 1400018 * 2
def baseEnd_1400018 : Nat := 159751590876979701519209

theorem tailTrace_1400018 : CollatzResearch.WordTrace tailWord_1400018 prefixEnd_1400018 159751590876979701519209 := by
  unfold tailWord_1400018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765712860495341220866177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34041900961320909922309805 12765712860495341220866177)
  ·
    refine ⟨9574284645371505915649633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12765712860495341220866177 9574284645371505915649633)
    ·
      refine ⟨7180713484028629436737225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574284645371505915649633 7180713484028629436737225)
      ·
        refine ⟨5385535113021472077552919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180713484028629436737225 5385535113021472077552919)
        ·
          refine ⟨8078302669532208116329379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385535113021472077552919 8078302669532208116329379)
          ·
            refine ⟨12117454004298312174494069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8078302669532208116329379 12117454004298312174494069)
            ·
              refine ⟨1136011312902966766358819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12117454004298312174494069 1136011312902966766358819)
              ·
                refine ⟨1704016969354450149538229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136011312902966766358819 1704016969354450149538229)
                ·
                  refine ⟨159751590876979701519209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1704016969354450149538229 159751590876979701519209)
                  ·
                    rfl

theorem cell22_1400018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1400018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400018 prefixEnd_1400018 := by exact prefixLift 1400018
  have htrace : WordTrace (prefixWord ++ tailWord_1400018) baseStart_1400018 baseEnd_1400018 := by
    simpa [prefixWord, tailWord_1400018, baseEnd_1400018] using wordTrace_append hprefix tailTrace_1400018
  have hstable : (prefixWord ++ tailWord_1400018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400018).length < 2 ^ (prefixWord ++ tailWord_1400018).sum := by decide
  have hdescent : baseEnd_1400018 < baseStart_1400018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400031 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 1, 4]
def baseStart_1400031 : Nat := 118140960795 + 1400031 * 2 ^ 59
def prefixEnd_1400031 : Nat := 4983230072969 + 3 ^ 40 * 1400031 * 2
def baseEnd_1400031 : Nat := 479259222796611403982587

theorem tailTrace_1400031 : CollatzResearch.WordTrace tailWord_1400031 prefixEnd_1400031 479259222796611403982587 := by
  unfold tailWord_1400031
  simp only [CollatzResearch.WordTrace]
  refine ⟨51063325590934268103687947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34042217060622845402458631 51063325590934268103687947)
  ·
    refine ⟨76594988386401402155531921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51063325590934268103687947 76594988386401402155531921)
    ·
      refine ⟨57446241289801051616648941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76594988386401402155531921 57446241289801051616648941)
      ·
        refine ⟨21542340483675394356243353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57446241289801051616648941 21542340483675394356243353)
        ·
          refine ⟨16156755362756545767182515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21542340483675394356243353 16156755362756545767182515)
          ·
            refine ⟨24235133044134818650773773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16156755362756545767182515 24235133044134818650773773)
            ·
              refine ⟨9088174891550556994040165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24235133044134818650773773 9088174891550556994040165)
              ·
                refine ⟨1704032792165729436382531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9088174891550556994040165 1704032792165729436382531)
                ·
                  refine ⟨2556049188248594154573797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704032792165729436382531 2556049188248594154573797)
                  ·
                    refine ⟨479259222796611403982587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556049188248594154573797 479259222796611403982587)
                    ·
                      rfl

theorem cell22_1400031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_1400031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400031 prefixEnd_1400031 := by exact prefixLift 1400031
  have htrace : WordTrace (prefixWord ++ tailWord_1400031) baseStart_1400031 baseEnd_1400031 := by
    simpa [prefixWord, tailWord_1400031, baseEnd_1400031] using wordTrace_append hprefix tailTrace_1400031
  have hstable : (prefixWord ++ tailWord_1400031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400031).length < 2 ^ (prefixWord ++ tailWord_1400031).sum := by decide
  have hdescent : baseEnd_1400031 < baseStart_1400031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400039 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1400039 : Nat := 118140960795 + 1400039 * 2 ^ 59
def prefixEnd_1400039 : Nat := 4983230072969 + 3 ^ 40 * 1400039 * 2
def baseEnd_1400039 : Nat := 479261961360102049782563

theorem tailTrace_1400039 : CollatzResearch.WordTrace tailWord_1400039 prefixEnd_1400039 479261961360102049782563 := by
  unfold tailWord_1400039
  simp only [CollatzResearch.WordTrace]
  refine ⟨51063617374905285469979171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34042411583270190313319447 51063617374905285469979171)
  ·
    refine ⟨76595426062357928204968757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51063617374905285469979171 76595426062357928204968757)
    ·
      refine ⟨7180821193346055769215821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76595426062357928204968757 7180821193346055769215821)
      ·
        refine ⟨2692807947504770913455933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7180821193346055769215821 2692807947504770913455933)
        ·
          refine ⟨1009802980314289092545975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2692807947504770913455933 1009802980314289092545975)
          ·
            refine ⟨1514704470471433638818963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009802980314289092545975 1514704470471433638818963)
            ·
              refine ⟨2272056705707150458228445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514704470471433638818963 2272056705707150458228445)
              ·
                refine ⟨852021264640181421835667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272056705707150458228445 852021264640181421835667)
                ·
                  refine ⟨1278031896960272132753501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852021264640181421835667 1278031896960272132753501)
                  ·
                    refine ⟨479261961360102049782563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278031896960272132753501 479261961360102049782563)
                    ·
                      rfl

theorem cell22_1400039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1400039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400039 prefixEnd_1400039 := by exact prefixLift 1400039
  have htrace : WordTrace (prefixWord ++ tailWord_1400039) baseStart_1400039 baseEnd_1400039 := by
    simpa [prefixWord, tailWord_1400039, baseEnd_1400039] using wordTrace_append hprefix tailTrace_1400039
  have hstable : (prefixWord ++ tailWord_1400039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400039).length < 2 ^ (prefixWord ++ tailWord_1400039).sum := by decide
  have hdescent : baseEnd_1400039 < baseStart_1400039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400093 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1400093 : Nat := 118140960795 + 1400093 * 2 ^ 59
def prefixEnd_1400093 : Nat := 4983230072969 + 3 ^ 40 * 1400093 * 2
def baseEnd_1400093 : Nat := 479280446663663908932397

theorem tailTrace_1400093 : CollatzResearch.WordTrace tailWord_1400093 prefixEnd_1400093 479280446663663908932397 := by
  unfold tailWord_1400093
  simp only [CollatzResearch.WordTrace]
  refine ⟨51065586916709652692444933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34043724611139768461629955 51065586916709652692444933)
  ·
    refine ⟨9574797546883059879833425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51065586916709652692444933 9574797546883059879833425)
    ·
      refine ⟨7181098160162294909875069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574797546883059879833425 7181098160162294909875069)
      ·
        refine ⟨2692911810060860591203151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7181098160162294909875069 2692911810060860591203151)
        ·
          refine ⟨4039367715091290886804727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692911810060860591203151 4039367715091290886804727)
          ·
            refine ⟨6059051572636936330207091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039367715091290886804727 6059051572636936330207091)
            ·
              refine ⟨9088577358955404495310637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059051572636936330207091 9088577358955404495310637)
              ·
                refine ⟨3408216509608276685741489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9088577358955404495310637 3408216509608276685741489)
                ·
                  refine ⟨2556162382206207514306117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408216509608276685741489 2556162382206207514306117)
                  ·
                    refine ⟨479280446663663908932397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556162382206207514306117 479280446663663908932397)
                    ·
                      rfl

theorem cell22_1400093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1400093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400093 prefixEnd_1400093 := by exact prefixLift 1400093
  have htrace : WordTrace (prefixWord ++ tailWord_1400093) baseStart_1400093 baseEnd_1400093 := by
    simpa [prefixWord, tailWord_1400093, baseEnd_1400093] using wordTrace_append hprefix tailTrace_1400093
  have hstable : (prefixWord ++ tailWord_1400093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400093).length < 2 ^ (prefixWord ++ tailWord_1400093).sum := by decide
  have hdescent : baseEnd_1400093 < baseStart_1400093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400125 : List Nat := [1, 4, 1, 5, 1, 2, 1, 7]
def baseStart_1400125 : Nat := 118140960795 + 1400125 * 2 ^ 59
def prefixEnd_1400125 : Nat := 4983230072969 + 3 ^ 40 * 1400125 * 2
def baseEnd_1400125 : Nat := 53254600101958499125811

theorem tailTrace_1400125 : CollatzResearch.WordTrace tailWord_1400125 prefixEnd_1400125 53254600101958499125811 := by
  unfold tailWord_1400125
  simp only [CollatzResearch.WordTrace]
  refine ⟨51066754052593722157609829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34044502701729148105073219 51066754052593722157609829)
  ·
    refine ⟨9575016384861322904551843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51066754052593722157609829 9575016384861322904551843)
    ·
      refine ⟨14362524577291984356827765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575016384861322904551843 14362524577291984356827765)
      ·
        refine ⟨1346486679121123533452603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14362524577291984356827765 1346486679121123533452603)
        ·
          refine ⟨2019730018681685300178905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346486679121123533452603 2019730018681685300178905)
          ·
            refine ⟨1514797514011263975134179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019730018681685300178905 1514797514011263975134179)
            ·
              refine ⟨2272196271016895962701269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514797514011263975134179 2272196271016895962701269)
              ·
                refine ⟨53254600101958499125811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2272196271016895962701269 53254600101958499125811)
                ·
                  rfl

theorem cell22_1400125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 7].length) (baseStart_1400125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400125 prefixEnd_1400125 := by exact prefixLift 1400125
  have htrace : WordTrace (prefixWord ++ tailWord_1400125) baseStart_1400125 baseEnd_1400125 := by
    simpa [prefixWord, tailWord_1400125, baseEnd_1400125] using wordTrace_append hprefix tailTrace_1400125
  have hstable : (prefixWord ++ tailWord_1400125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400125).length < 2 ^ (prefixWord ++ tailWord_1400125).sum := by decide
  have hdescent : baseEnd_1400125 < baseStart_1400125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400200 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1400200 : Nat := 118140960795 + 1400200 * 2 ^ 59
def prefixEnd_1400200 : Nat := 4983230072969 + 3 ^ 40 * 1400200 * 2
def baseEnd_1400200 : Nat := 479317074950351296507069

theorem tailTrace_1400200 : CollatzResearch.WordTrace tailWord_1400200 prefixEnd_1400200 479317074950351296507069 := by
  unfold tailWord_1400200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534744763661004983295027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34046326351548006644393369 25534744763661004983295027)
  ·
    refine ⟨38302117145491507474942541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25534744763661004983295027 38302117145491507474942541)
    ·
      refine ⟨14363293929559315303103453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38302117145491507474942541 14363293929559315303103453)
      ·
        refine ⟨5386235223584743238663795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14363293929559315303103453 5386235223584743238663795)
        ·
          refine ⟨8079352835377114857995693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386235223584743238663795 8079352835377114857995693)
          ·
            refine ⟨3029757313266418071748385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8079352835377114857995693 3029757313266418071748385)
            ·
              refine ⟨2272317984949813553811289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029757313266418071748385 2272317984949813553811289)
              ·
                refine ⟨1704238488712360165358467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272317984949813553811289 1704238488712360165358467)
                ·
                  refine ⟨2556357733068540248037701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704238488712360165358467 2556357733068540248037701)
                  ·
                    refine ⟨479317074950351296507069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556357733068540248037701 479317074950351296507069)
                    ·
                      rfl

theorem cell22_1400200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1400200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400200 prefixEnd_1400200 := by exact prefixLift 1400200
  have htrace : WordTrace (prefixWord ++ tailWord_1400200) baseStart_1400200 baseEnd_1400200 := by
    simpa [prefixWord, tailWord_1400200, baseEnd_1400200] using wordTrace_append hprefix tailTrace_1400200
  have hstable : (prefixWord ++ tailWord_1400200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400200).length < 2 ^ (prefixWord ++ tailWord_1400200).sum := by decide
  have hdescent : baseEnd_1400200 < baseStart_1400200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_1400211 : Nat := 118140960795 + 1400211 * 2 ^ 59
def prefixEnd_1400211 : Nat := 4983230072969 + 3 ^ 40 * 1400211 * 2
def baseEnd_1400211 : Nat := 479320840475150934482035

theorem tailTrace_1400211 : CollatzResearch.WordTrace tailWord_1400211 prefixEnd_1400211 479320840475150934482035 := by
  unfold tailWord_1400211
  simp only [CollatzResearch.WordTrace]
  refine ⟨51069890730282158845240487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34046593820188105896826991 51069890730282158845240487)
  ·
    refine ⟨76604836095423238267860731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51069890730282158845240487 76604836095423238267860731)
    ·
      refine ⟨114907254143134857401791097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76604836095423238267860731 114907254143134857401791097)
      ·
        refine ⟨86180440607351143051343323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114907254143134857401791097 86180440607351143051343323)
        ·
          refine ⟨129270660911026714577014985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86180440607351143051343323 129270660911026714577014985)
          ·
            refine ⟨96952995683270035932761239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129270660911026714577014985 96952995683270035932761239)
            ·
              refine ⟨145429493524905053899141859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96952995683270035932761239 145429493524905053899141859)
              ·
                refine ⟨218144240287357580848712789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145429493524905053899141859 218144240287357580848712789)
                ·
                  refine ⟨2556377815867471650570853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 218144240287357580848712789 2556377815867471650570853)
                  ·
                    refine ⟨479320840475150934482035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2556377815867471650570853 479320840475150934482035)
                    ·
                      rfl

theorem cell22_1400211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_1400211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400211 prefixEnd_1400211 := by exact prefixLift 1400211
  have htrace : WordTrace (prefixWord ++ tailWord_1400211) baseStart_1400211 baseEnd_1400211 := by
    simpa [prefixWord, tailWord_1400211, baseEnd_1400211] using wordTrace_append hprefix tailTrace_1400211
  have hstable : (prefixWord ++ tailWord_1400211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400211).length < 2 ^ (prefixWord ++ tailWord_1400211).sum := by decide
  have hdescent : baseEnd_1400211 < baseStart_1400211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400213 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1400213 : Nat := 118140960795 + 1400213 * 2 ^ 59
def prefixEnd_1400213 : Nat := 4983230072969 + 3 ^ 40 * 1400213 * 2
def baseEnd_1400213 : Nat := 479321525116023595932029

theorem tailTrace_1400213 : CollatzResearch.WordTrace tailWord_1400213 prefixEnd_1400213 479321525116023595932029 := by
  unfold tailWord_1400213
  simp only [CollatzResearch.WordTrace]
  refine ⟨51069963676274913186813293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34046642450849942124542195 51069963676274913186813293)
  ·
    refine ⟨19151236378603092445054985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51069963676274913186813293 19151236378603092445054985)
    ·
      refine ⟨14363427283952319333791239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19151236378603092445054985 14363427283952319333791239)
      ·
        refine ⟨21545140925928479000686859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363427283952319333791239 21545140925928479000686859)
        ·
          refine ⟨32317711388892718501030289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21545140925928479000686859 32317711388892718501030289)
          ·
            refine ⟨24238283541669538875772717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32317711388892718501030289 24238283541669538875772717)
            ·
              refine ⟨9089356328126077078414769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24238283541669538875772717 9089356328126077078414769)
              ·
                refine ⟨6817017246094557808811077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9089356328126077078414769 6817017246094557808811077)
                ·
                  refine ⟨1278190733642729589152077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6817017246094557808811077 1278190733642729589152077)
                  ·
                    refine ⟨479321525116023595932029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278190733642729589152077 479321525116023595932029)
                    ·
                      rfl

theorem cell22_1400213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1400213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400213 prefixEnd_1400213 := by exact prefixLift 1400213
  have htrace : WordTrace (prefixWord ++ tailWord_1400213) baseStart_1400213 baseEnd_1400213 := by
    simpa [prefixWord, tailWord_1400213, baseEnd_1400213] using wordTrace_append hprefix tailTrace_1400213
  have hstable : (prefixWord ++ tailWord_1400213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400213).length < 2 ^ (prefixWord ++ tailWord_1400213).sum := by decide
  have hdescent : baseEnd_1400213 < baseStart_1400213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400232 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_1400232 : Nat := 118140960795 + 1400232 * 2 ^ 59
def prefixEnd_1400232 : Nat := 4983230072969 + 3 ^ 40 * 1400232 * 2
def baseEnd_1400232 : Nat := 159776009734771293235657

theorem tailTrace_1400232 : CollatzResearch.WordTrace tailWord_1400232 prefixEnd_1400232 159776009734771293235657 := by
  unfold tailWord_1400232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535328331603039715877475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34047104442137386287836633 25535328331603039715877475)
  ·
    refine ⟨38302992497404559573816213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25535328331603039715877475 38302992497404559573816213)
    ·
      refine ⟨1795452773315838730022635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38302992497404559573816213 1795452773315838730022635)
      ·
        refine ⟨2693179159973758095033953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795452773315838730022635 2693179159973758095033953)
        ·
          refine ⟨2019884369980318571275465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693179159973758095033953 2019884369980318571275465)
          ·
            refine ⟨1514913277485238928456599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019884369980318571275465 1514913277485238928456599)
            ·
              refine ⟨2272369916227858392684899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514913277485238928456599 2272369916227858392684899)
              ·
                refine ⟨3408554874341787589027349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272369916227858392684899 3408554874341787589027349)
                ·
                  refine ⟨159776009734771293235657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3408554874341787589027349 159776009734771293235657)
                  ·
                    rfl

theorem cell22_1400232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_1400232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400232 prefixEnd_1400232 := by exact prefixLift 1400232
  have htrace : WordTrace (prefixWord ++ tailWord_1400232) baseStart_1400232 baseEnd_1400232 := by
    simpa [prefixWord, tailWord_1400232, baseEnd_1400232] using wordTrace_append hprefix tailTrace_1400232
  have hstable : (prefixWord ++ tailWord_1400232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400232).length < 2 ^ (prefixWord ++ tailWord_1400232).sum := by decide
  have hdescent : baseEnd_1400232 < baseStart_1400232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400271 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 9]
def baseStart_1400271 : Nat := 118140960795 + 1400271 * 2 ^ 59
def prefixEnd_1400271 : Nat := 4983230072969 + 3 ^ 40 * 1400271 * 2
def baseEnd_1400271 : Nat := 159780459900443592660617

theorem tailTrace_1400271 : CollatzResearch.WordTrace tailWord_1400271 prefixEnd_1400271 159780459900443592660617 := by
  unfold tailWord_1400271
  simp only [CollatzResearch.WordTrace]
  refine ⟨51072079110064789092424667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34048052740043192728283111 51072079110064789092424667)
  ·
    refine ⟨76608118665097183638637001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51072079110064789092424667 76608118665097183638637001)
    ·
      refine ⟨57456088998822887728977751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76608118665097183638637001 57456088998822887728977751)
      ·
        refine ⟨86184133498234331593466627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57456088998822887728977751 86184133498234331593466627)
        ·
          refine ⟨129276200247351497390199941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86184133498234331593466627 129276200247351497390199941)
          ·
            refine ⟨24239287546378405760662489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129276200247351497390199941 24239287546378405760662489)
            ·
              refine ⟨18179465659783804320496867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24239287546378405760662489 18179465659783804320496867)
              ·
                refine ⟨27269198489675706480745301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18179465659783804320496867 27269198489675706480745301)
                ·
                  refine ⟨159780459900443592660617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27269198489675706480745301 159780459900443592660617)
                  ·
                    rfl

theorem cell22_1400271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_1400271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400271 prefixEnd_1400271 := by exact prefixLift 1400271
  have htrace : WordTrace (prefixWord ++ tailWord_1400271) baseStart_1400271 baseEnd_1400271 := by
    simpa [prefixWord, tailWord_1400271, baseEnd_1400271] using wordTrace_append hprefix tailTrace_1400271
  have hstable : (prefixWord ++ tailWord_1400271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400271).length < 2 ^ (prefixWord ++ tailWord_1400271).sum := by decide
  have hdescent : baseEnd_1400271 < baseStart_1400271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400378 : List Nat := [3, 1, 1, 1, 3, 2, 3, 8]
def baseStart_1400378 : Nat := 118140960795 + 1400378 * 2 ^ 59
def prefixEnd_1400378 : Nat := 4983230072969 + 3 ^ 40 * 1400378 * 2
def baseEnd_1400378 : Nat := 53264223109779796172947

theorem tailTrace_1400378 : CollatzResearch.WordTrace tailWord_1400378 prefixEnd_1400378 53264223109779796172947 := by
  unfold tailWord_1400378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768995430169286591642447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34050654480451430911046525 12768995430169286591642447)
  ·
    refine ⟨19153493145253929887463671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12768995430169286591642447 19153493145253929887463671)
    ·
      refine ⟨28730239717880894831195507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19153493145253929887463671 28730239717880894831195507)
      ·
        refine ⟨43095359576821342246793261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28730239717880894831195507 43095359576821342246793261)
        ·
          refine ⟨16160759841308003342547473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43095359576821342246793261 16160759841308003342547473)
          ·
            refine ⟨12120569880981002506910605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16160759841308003342547473 12120569880981002506910605)
            ·
              refine ⟨4545213705367875940091477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12120569880981002506910605 4545213705367875940091477)
              ·
                refine ⟨53264223109779796172947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4545213705367875940091477 53264223109779796172947)
                ·
                  rfl

theorem cell22_1400378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_1400378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400378 prefixEnd_1400378 := by exact prefixLift 1400378
  have htrace : WordTrace (prefixWord ++ tailWord_1400378) baseStart_1400378 baseEnd_1400378 := by
    simpa [prefixWord, tailWord_1400378, baseEnd_1400378] using wordTrace_append hprefix tailTrace_1400378
  have hstable : (prefixWord ++ tailWord_1400378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400378).length < 2 ^ (prefixWord ++ tailWord_1400378).sum := by decide
  have hdescent : baseEnd_1400378 < baseStart_1400378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400408 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1400408 : Nat := 118140960795 + 1400408 * 2 ^ 59
def prefixEnd_1400408 : Nat := 4983230072969 + 3 ^ 40 * 1400408 * 2
def baseEnd_1400408 : Nat := 479388277601108087306431

theorem tailTrace_1400408 : CollatzResearch.WordTrace tailWord_1400408 prefixEnd_1400408 479388277601108087306431 := by
  unfold tailWord_1400408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25538537955284230745080939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34051383940378974326774585 25538537955284230745080939)
  ·
    refine ⟨38307806932926346117621409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25538537955284230745080939 38307806932926346117621409)
    ·
      refine ⟨28730855199694759588216057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38307806932926346117621409 28730855199694759588216057)
      ·
        refine ⟨21548141399771069691162043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28730855199694759588216057 21548141399771069691162043)
        ·
          refine ⟨32322212099656604536743065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21548141399771069691162043 32322212099656604536743065)
          ·
            refine ⟨24241659074742453402557299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32322212099656604536743065 24241659074742453402557299)
            ·
              refine ⟨36362488612113680103835949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24241659074742453402557299 36362488612113680103835949)
              ·
                refine ⟨13635933229542630038938481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36362488612113680103835949 13635933229542630038938481)
                ·
                  refine ⟨10226949922156972529203861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13635933229542630038938481 10226949922156972529203861)
                  ·
                    refine ⟨479388277601108087306431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10226949922156972529203861 479388277601108087306431)
                    ·
                      rfl

theorem cell22_1400408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1400408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400408 prefixEnd_1400408 := by exact prefixLift 1400408
  have htrace : WordTrace (prefixWord ++ tailWord_1400408) baseStart_1400408 baseEnd_1400408 := by
    simpa [prefixWord, tailWord_1400408, baseEnd_1400408] using wordTrace_append hprefix tailTrace_1400408
  have hstable : (prefixWord ++ tailWord_1400408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400408).length < 2 ^ (prefixWord ++ tailWord_1400408).sum := by decide
  have hdescent : baseEnd_1400408 < baseStart_1400408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400532 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1400532 : Nat := 118140960795 + 1400532 * 2 ^ 59
def prefixEnd_1400532 : Nat := 4983230072969 + 3 ^ 40 * 1400532 * 2
def baseEnd_1400532 : Nat := 479430725335213097206051

theorem tailTrace_1400532 : CollatzResearch.WordTrace tailWord_1400532 prefixEnd_1400532 479430725335213097206051 := by
  unfold tailWord_1400532
  simp only [CollatzResearch.WordTrace]
  refine ⟨25540799281059615333837925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34054399041412820445117233 25540799281059615333837925)
  ·
    refine ⟨4788899865198677875094611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25540799281059615333837925 4788899865198677875094611)
    ·
      refine ⟨7183349797798016812641917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788899865198677875094611 7183349797798016812641917)
      ·
        refine ⟨2693756174174256304740719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7183349797798016812641917 2693756174174256304740719)
        ·
          refine ⟨4040634261261384457111079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693756174174256304740719 4040634261261384457111079)
          ·
            refine ⟨6060951391892076685666619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040634261261384457111079 6060951391892076685666619)
            ·
              refine ⟨9091427087838115028499929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060951391892076685666619 9091427087838115028499929)
              ·
                refine ⟨6818570315878586271374947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9091427087838115028499929 6818570315878586271374947)
                ·
                  refine ⟨10227855473817879407062421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818570315878586271374947 10227855473817879407062421)
                  ·
                    refine ⟨479430725335213097206051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10227855473817879407062421 479430725335213097206051)
                    ·
                      rfl

theorem cell22_1400532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1400532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400532 prefixEnd_1400532 := by exact prefixLift 1400532
  have htrace : WordTrace (prefixWord ++ tailWord_1400532) baseStart_1400532 baseEnd_1400532 := by
    simpa [prefixWord, tailWord_1400532, baseEnd_1400532] using wordTrace_append hprefix tailTrace_1400532
  have hstable : (prefixWord ++ tailWord_1400532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400532).length < 2 ^ (prefixWord ++ tailWord_1400532).sum := by decide
  have hdescent : baseEnd_1400532 < baseStart_1400532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400547 : List Nat := [1, 1, 1, 7, 2, 1, 1, 8]
def baseStart_1400547 : Nat := 118140960795 + 1400547 * 2 ^ 59
def prefixEnd_1400547 : Nat := 4983230072969 + 3 ^ 40 * 1400547 * 2
def baseEnd_1400547 : Nat := 53270651126862006453445

theorem tailTrace_1400547 : CollatzResearch.WordTrace tailWord_1400547 prefixEnd_1400547 53270651126862006453445 := by
  unfold tailWord_1400547
  simp only [CollatzResearch.WordTrace]
  refine ⟨51082145657064888229471895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34054763771376592152981263 51082145657064888229471895)
  ·
    refine ⟨76623218485597332344207843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51082145657064888229471895 76623218485597332344207843)
    ·
      refine ⟨114934827728395998516311765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76623218485597332344207843 114934827728395998516311765)
      ·
        refine ⟨2693785024884281215226057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114934827728395998516311765 2693785024884281215226057)
        ·
          refine ⟨2020338768663210911419543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693785024884281215226057 2020338768663210911419543)
          ·
            refine ⟨3030508152994816367129315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020338768663210911419543 3030508152994816367129315)
            ·
              refine ⟨4545762229492224550693973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030508152994816367129315 4545762229492224550693973)
              ·
                refine ⟨53270651126862006453445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4545762229492224550693973 53270651126862006453445)
                ·
                  rfl

theorem cell22_1400547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 8].length) (baseStart_1400547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400547 prefixEnd_1400547 := by exact prefixLift 1400547
  have htrace : WordTrace (prefixWord ++ tailWord_1400547) baseStart_1400547 baseEnd_1400547 := by
    simpa [prefixWord, tailWord_1400547, baseEnd_1400547] using wordTrace_append hprefix tailTrace_1400547
  have hstable : (prefixWord ++ tailWord_1400547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400547).length < 2 ^ (prefixWord ++ tailWord_1400547).sum := by decide
  have hdescent : baseEnd_1400547 < baseStart_1400547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400564 : List Nat := [2, 6, 1, 1, 1, 1, 10]
def baseStart_1400564 : Nat := 118140960795 + 1400564 * 2 ^ 59
def prefixEnd_1400564 : Nat := 4983230072969 + 3 ^ 40 * 1400564 * 2
def baseEnd_1400564 : Nat := 17757099244043543718739

theorem tailTrace_1400564 : CollatzResearch.WordTrace tailWord_1400564 prefixEnd_1400564 17757099244043543718739 := by
  unfold tailWord_1400564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25541382849001650066420373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34055177132002200088560497 25541382849001650066420373)
  ·
    refine ⟨1197252321046952346863455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25541382849001650066420373 1197252321046952346863455)
    ·
      refine ⟨1795878481570428520295183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197252321046952346863455 1795878481570428520295183)
      ·
        refine ⟨2693817722355642780442775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795878481570428520295183 2693817722355642780442775)
        ·
          refine ⟨4040726583533464170664163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693817722355642780442775 4040726583533464170664163)
          ·
            refine ⟨6061089875300196255996245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040726583533464170664163 6061089875300196255996245)
            ·
              refine ⟨17757099244043543718739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6061089875300196255996245 17757099244043543718739)
              ·
                rfl

theorem cell22_1400564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 10].length) (baseStart_1400564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400564 prefixEnd_1400564 := by exact prefixLift 1400564
  have htrace : WordTrace (prefixWord ++ tailWord_1400564) baseStart_1400564 baseEnd_1400564 := by
    simpa [prefixWord, tailWord_1400564, baseEnd_1400564] using wordTrace_append hprefix tailTrace_1400564
  have hstable : (prefixWord ++ tailWord_1400564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400564).length < 2 ^ (prefixWord ++ tailWord_1400564).sum := by decide
  have hdescent : baseEnd_1400564 < baseStart_1400564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400575 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 7]
def baseStart_1400575 : Nat := 118140960795 + 1400575 * 2 ^ 59
def prefixEnd_1400575 : Nat := 4983230072969 + 3 ^ 40 * 1400575 * 2
def baseEnd_1400575 : Nat := 159815148371325106126973

theorem tailTrace_1400575 : CollatzResearch.WordTrace tailWord_1400575 prefixEnd_1400575 159815148371325106126973 := by
  unfold tailWord_1400575
  simp only [CollatzResearch.WordTrace]
  refine ⟨51083166900963449011491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34055444600642299340994119 51083166900963449011491179)
  ·
    refine ⟨76624750351445173517236769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51083166900963449011491179 76624750351445173517236769)
    ·
      refine ⟨57468562763583880137927577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76624750351445173517236769 57468562763583880137927577)
      ·
        refine ⟨43101422072687910103445683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57468562763583880137927577 43101422072687910103445683)
        ·
          refine ⟨64652133109031865155168525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43101422072687910103445683 64652133109031865155168525)
          ·
            refine ⟨24244549915886949433188197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64652133109031865155168525 24244549915886949433188197)
            ·
              refine ⟨4545853109228803018722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24244549915886949433188197 4545853109228803018722787)
              ·
                refine ⟨6818779663843204528084181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4545853109228803018722787 6818779663843204528084181)
                ·
                  refine ⟨159815148371325106126973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6818779663843204528084181 159815148371325106126973)
                  ·
                    rfl

theorem cell22_1400575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_1400575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400575 prefixEnd_1400575 := by exact prefixLift 1400575
  have htrace : WordTrace (prefixWord ++ tailWord_1400575) baseStart_1400575 baseEnd_1400575 := by
    simpa [prefixWord, tailWord_1400575, baseEnd_1400575] using wordTrace_append hprefix tailTrace_1400575
  have hstable : (prefixWord ++ tailWord_1400575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400575).length < 2 ^ (prefixWord ++ tailWord_1400575).sum := by decide
  have hdescent : baseEnd_1400575 < baseStart_1400575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400579 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 1, 3]
def baseStart_1400579 : Nat := 118140960795 + 1400579 * 2 ^ 59
def prefixEnd_1400579 : Nat := 4983230072969 + 3 ^ 40 * 1400579 * 2
def baseEnd_1400579 : Nat := 479446814395720641280907

theorem tailTrace_1400579 : CollatzResearch.WordTrace tailWord_1400579 prefixEnd_1400579 479446814395720641280907 := by
  unfold tailWord_1400579
  simp only [CollatzResearch.WordTrace]
  refine ⟨51083312792948957694636791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34055541861965971796424527 51083312792948957694636791)
  ·
    refine ⟨76624969189423436541955187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51083312792948957694636791 76624969189423436541955187)
    ·
      refine ⟨114937453784135154812932781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76624969189423436541955187 114937453784135154812932781)
      ·
        refine ⟨43101545169050683054849793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114937453784135154812932781 43101545169050683054849793)
        ·
          refine ⟨32326158876788012291137345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43101545169050683054849793 32326158876788012291137345)
          ·
            refine ⟨24244619157591009218353009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32326158876788012291137345 24244619157591009218353009)
            ·
              refine ⟨18183464368193256913764757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24244619157591009218353009 18183464368193256913764757)
              ·
                refine ⟨852349892259058917832723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18183464368193256913764757 852349892259058917832723)
                ·
                  refine ⟨1278524838388588376749085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852349892259058917832723 1278524838388588376749085)
                  ·
                    refine ⟨479446814395720641280907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278524838388588376749085 479446814395720641280907)
                    ·
                      rfl

theorem cell22_1400579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 3].length) (baseStart_1400579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400579 prefixEnd_1400579 := by exact prefixLift 1400579
  have htrace : WordTrace (prefixWord ++ tailWord_1400579) baseStart_1400579 baseEnd_1400579 := by
    simpa [prefixWord, tailWord_1400579, baseEnd_1400579] using wordTrace_append hprefix tailTrace_1400579
  have hstable : (prefixWord ++ tailWord_1400579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400579).length < 2 ^ (prefixWord ++ tailWord_1400579).sum := by decide
  have hdescent : baseEnd_1400579 < baseStart_1400579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400630 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1400630 : Nat := 118140960795 + 1400630 * 2 ^ 59
def prefixEnd_1400630 : Nat := 4983230072969 + 3 ^ 40 * 1400630 * 2
def baseEnd_1400630 : Nat := 479464272737973508255751

theorem tailTrace_1400630 : CollatzResearch.WordTrace tailWord_1400630 prefixEnd_1400630 479464272737973508255751 := by
  unfold tailWord_1400630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192823307235262087796459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34056781943842795603162229 3192823307235262087796459)
  ·
    refine ⟨4789234960852893131694689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192823307235262087796459 4789234960852893131694689)
    ·
      refine ⟨3591926220639669848771017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789234960852893131694689 3591926220639669848771017)
      ·
        refine ⟨2693944665479752386578263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3591926220639669848771017 2693944665479752386578263)
        ·
          refine ⟨4040916998219628579867395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693944665479752386578263 4040916998219628579867395)
          ·
            refine ⟨6061375497329442869801093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040916998219628579867395 6061375497329442869801093)
            ·
              refine ⟨1136507905749270538087705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6061375497329442869801093 1136507905749270538087705)
              ·
                refine ⟨852380929311952903565779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136507905749270538087705 852380929311952903565779)
                ·
                  refine ⟨1278571393967929355348669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852380929311952903565779 1278571393967929355348669)
                  ·
                    refine ⟨479464272737973508255751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278571393967929355348669 479464272737973508255751)
                    ·
                      rfl

theorem cell22_1400630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1400630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400630 prefixEnd_1400630 := by exact prefixLift 1400630
  have htrace : WordTrace (prefixWord ++ tailWord_1400630) baseStart_1400630 baseEnd_1400630 := by
    simpa [prefixWord, tailWord_1400630, baseEnd_1400630] using wordTrace_append hprefix tailTrace_1400630
  have hstable : (prefixWord ++ tailWord_1400630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400630).length < 2 ^ (prefixWord ++ tailWord_1400630).sum := by decide
  have hdescent : baseEnd_1400630 < baseStart_1400630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400686 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1400686 : Nat := 118140960795 + 1400686 * 2 ^ 59
def prefixEnd_1400686 : Nat := 4983230072969 + 3 ^ 40 * 1400686 * 2
def baseEnd_1400686 : Nat := 479483442682408028855579

theorem tailTrace_1400686 : CollatzResearch.WordTrace tailWord_1400686 prefixEnd_1400686 479483442682408028855579 := by
  unfold tailWord_1400686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385901925445164371097739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34058143602374209979187941 6385901925445164371097739)
  ·
    refine ⟨9578852888167746556646609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6385901925445164371097739 9578852888167746556646609)
    ·
      refine ⟨7184139666125809917484957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9578852888167746556646609 7184139666125809917484957)
      ·
        refine ⟨2694052374797178719056859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7184139666125809917484957 2694052374797178719056859)
        ·
          refine ⟨4041078562195768078585289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694052374797178719056859 4041078562195768078585289)
          ·
            refine ⟨3030808921646826058938967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041078562195768078585289 3030808921646826058938967)
            ·
              refine ⟨4546213382470239088408451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030808921646826058938967 4546213382470239088408451)
              ·
                refine ⟨6819320073705358632612677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546213382470239088408451 6819320073705358632612677)
                ·
                  refine ⟨1278622513819754743614877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6819320073705358632612677 1278622513819754743614877)
                  ·
                    refine ⟨479483442682408028855579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278622513819754743614877 479483442682408028855579)
                    ·
                      rfl

theorem cell22_1400686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1400686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400686 prefixEnd_1400686 := by exact prefixLift 1400686
  have htrace : WordTrace (prefixWord ++ tailWord_1400686) baseStart_1400686 baseEnd_1400686 := by
    simpa [prefixWord, tailWord_1400686, baseEnd_1400686] using wordTrace_append hprefix tailTrace_1400686
  have hstable : (prefixWord ++ tailWord_1400686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400686).length < 2 ^ (prefixWord ++ tailWord_1400686).sum := by decide
  have hdescent : baseEnd_1400686 < baseStart_1400686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400727 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 7]
def baseStart_1400727 : Nat := 118140960795 + 1400727 * 2 ^ 59
def prefixEnd_1400727 : Nat := 4983230072969 + 3 ^ 40 * 1400727 * 2
def baseEnd_1400727 : Nat := 159832492606765862860151

theorem tailTrace_1400727 : CollatzResearch.WordTrace tailWord_1400727 prefixEnd_1400727 159832492606765862860151 := by
  unfold tailWord_1400727
  simp only [CollatzResearch.WordTrace]
  refine ⟨51088710796412778971024435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34059140530941852647349623 51088710796412778971024435)
  ·
    refine ⟨76633066194619168456536653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51088710796412778971024435 76633066194619168456536653)
    ·
      refine ⟨28737399822982188171201245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76633066194619168456536653 28737399822982188171201245)
      ·
        refine ⟨10776524933618320564200467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28737399822982188171201245 10776524933618320564200467)
        ·
          refine ⟨16164787400427480846300701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10776524933618320564200467 16164787400427480846300701)
          ·
            refine ⟨6061795275160305317362763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16164787400427480846300701 6061795275160305317362763)
            ·
              refine ⟨9092692912740457976044145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6061795275160305317362763 9092692912740457976044145)
              ·
                refine ⟨6819519684555343482033109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9092692912740457976044145 6819519684555343482033109)
                ·
                  refine ⟨159832492606765862860151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6819519684555343482033109 159832492606765862860151)
                  ·
                    rfl

theorem cell22_1400727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_1400727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400727 prefixEnd_1400727 := by exact prefixLift 1400727
  have htrace : WordTrace (prefixWord ++ tailWord_1400727) baseStart_1400727 baseEnd_1400727 := by
    simpa [prefixWord, tailWord_1400727, baseEnd_1400727] using wordTrace_append hprefix tailTrace_1400727
  have hstable : (prefixWord ++ tailWord_1400727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400727).length < 2 ^ (prefixWord ++ tailWord_1400727).sum := by decide
  have hdescent : baseEnd_1400727 < baseStart_1400727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400791 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 1, 4]
def baseStart_1400791 : Nat := 118140960795 + 1400791 * 2 ^ 59
def prefixEnd_1400791 : Nat := 4983230072969 + 3 ^ 40 * 1400791 * 2
def baseEnd_1400791 : Nat := 479519386328222754980257

theorem tailTrace_1400791 : CollatzResearch.WordTrace tailWord_1400791 prefixEnd_1400791 479519386328222754980257 := by
  unfold tailWord_1400791
  simp only [CollatzResearch.WordTrace]
  refine ⟨51091045068180917901354227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34060696712120611934236151 51091045068180917901354227)
  ·
    refine ⟨76636567602271376852031341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51091045068180917901354227 76636567602271376852031341)
    ·
      refine ⟨28738712850851766319511753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76636567602271376852031341 28738712850851766319511753)
      ·
        refine ⟨21554034638138824739633815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28738712850851766319511753 21554034638138824739633815)
        ·
          refine ⟨32331051957208237109450723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21554034638138824739633815 32331051957208237109450723)
          ·
            refine ⟨48496577935812355664176085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32331051957208237109450723 48496577935812355664176085)
            ·
              refine ⟨1136638545370602085879127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48496577935812355664176085 1136638545370602085879127)
              ·
                refine ⟨1704957818055903128818691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136638545370602085879127 1704957818055903128818691)
                ·
                  refine ⟨2557436727083854693228037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704957818055903128818691 2557436727083854693228037)
                  ·
                    refine ⟨479519386328222754980257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557436727083854693228037 479519386328222754980257)
                    ·
                      rfl

theorem cell22_1400791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_1400791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400791 prefixEnd_1400791 := by exact prefixLift 1400791
  have htrace : WordTrace (prefixWord ++ tailWord_1400791) baseStart_1400791 baseEnd_1400791 := by
    simpa [prefixWord, tailWord_1400791, baseEnd_1400791] using wordTrace_append hprefix tailTrace_1400791
  have hstable : (prefixWord ++ tailWord_1400791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400791).length < 2 ^ (prefixWord ++ tailWord_1400791).sum := by decide
  have hdescent : baseEnd_1400791 < baseStart_1400791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400832 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_1400832 : Nat := 118140960795 + 1400832 * 2 ^ 59
def prefixEnd_1400832 : Nat := 4983230072969 + 3 ^ 40 * 1400832 * 2
def baseEnd_1400832 : Nat := 479533421466112314705131

theorem tailTrace_1400832 : CollatzResearch.WordTrace tailWord_1400832 prefixEnd_1400832 479533421466112314705131 := by
  unfold tailWord_1400832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546270230516190951798375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34061693640688254602397833 25546270230516190951798375)
  ·
    refine ⟨38319405345774286427697563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25546270230516190951798375 38319405345774286427697563)
    ·
      refine ⟨57479108018661429641546345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38319405345774286427697563 57479108018661429641546345)
      ·
        refine ⟨43109331013996072231159759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57479108018661429641546345 43109331013996072231159759)
        ·
          refine ⟨64663996520994108346739639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43109331013996072231159759 64663996520994108346739639)
          ·
            refine ⟨96995994781491162520109459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64663996520994108346739639 96995994781491162520109459)
            ·
              refine ⟨145493992172236743780164189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96995994781491162520109459 145493992172236743780164189)
              ·
                refine ⟨54560247064588778917561571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145493992172236743780164189 54560247064588778917561571)
                ·
                  refine ⟨81840370596883168376342357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54560247064588778917561571 81840370596883168376342357)
                  ·
                    refine ⟨479533421466112314705131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81840370596883168376342357 479533421466112314705131)
                    ·
                      rfl

theorem cell22_1400832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_1400832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400832 prefixEnd_1400832 := by exact prefixLift 1400832
  have htrace : WordTrace (prefixWord ++ tailWord_1400832) baseStart_1400832 baseEnd_1400832 := by
    simpa [prefixWord, tailWord_1400832, baseEnd_1400832] using wordTrace_append hprefix tailTrace_1400832
  have hstable : (prefixWord ++ tailWord_1400832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400832).length < 2 ^ (prefixWord ++ tailWord_1400832).sum := by decide
  have hdescent : baseEnd_1400832 < baseStart_1400832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400855 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 2, 3]
def baseStart_1400855 : Nat := 118140960795 + 1400855 * 2 ^ 59
def prefixEnd_1400855 : Nat := 4983230072969 + 3 ^ 40 * 1400855 * 2
def baseEnd_1400855 : Nat := 479541294836147921380061

theorem tailTrace_1400855 : CollatzResearch.WordTrace tailWord_1400855 prefixEnd_1400855 479541294836147921380061 := by
  unfold tailWord_1400855
  simp only [CollatzResearch.WordTrace]
  refine ⟨51093379339949056831684019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34062252893299371221122679 51093379339949056831684019)
  ·
    refine ⟨76640069009923585247526029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51093379339949056831684019 76640069009923585247526029)
    ·
      refine ⟨28740025878721344467822261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76640069009923585247526029 28740025878721344467822261)
      ·
        refine ⟨2694377426130126043858337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28740025878721344467822261 2694377426130126043858337)
        ·
          refine ⟨2020783069597594532893753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694377426130126043858337 2020783069597594532893753)
          ·
            refine ⟨1515587302198195899670315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020783069597594532893753 1515587302198195899670315)
            ·
              refine ⟨2273380953297293849505473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515587302198195899670315 2273380953297293849505473)
              ·
                refine ⟨1705035714972970387129105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273380953297293849505473 1705035714972970387129105)
                ·
                  refine ⟨1278776786229727790346829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705035714972970387129105 1278776786229727790346829)
                  ·
                    refine ⟨479541294836147921380061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278776786229727790346829 479541294836147921380061)
                    ·
                      rfl

theorem cell22_1400855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_1400855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400855 prefixEnd_1400855 := by exact prefixLift 1400855
  have htrace : WordTrace (prefixWord ++ tailWord_1400855) baseStart_1400855 baseEnd_1400855 := by
    simpa [prefixWord, tailWord_1400855, baseEnd_1400855] using wordTrace_append hprefix tailTrace_1400855
  have hstable : (prefixWord ++ tailWord_1400855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400855).length < 2 ^ (prefixWord ++ tailWord_1400855).sum := by decide
  have hdescent : baseEnd_1400855 < baseStart_1400855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400872 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1400872 : Nat := 118140960795 + 1400872 * 2 ^ 59
def prefixEnd_1400872 : Nat := 4983230072969 + 3 ^ 40 * 1400872 * 2
def baseEnd_1400872 : Nat := 479547114283565543705009

theorem tailTrace_1400872 : CollatzResearch.WordTrace tailWord_1400872 prefixEnd_1400872 479547114283565543705009 := by
  unfold tailWord_1400872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546999690443734367526435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34062666253924979156701913 25546999690443734367526435)
  ·
    refine ⟨38320499535665601551289653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25546999690443734367526435 38320499535665601551289653)
    ·
      refine ⟨3592546831468650145433405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38320499535665601551289653 3592546831468650145433405)
      ·
        refine ⟨1347205061800743804537527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3592546831468650145433405 1347205061800743804537527)
        ·
          refine ⟨2020807592701115706806291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347205061800743804537527 2020807592701115706806291)
          ·
            refine ⟨3031211389051673560209437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020807592701115706806291 3031211389051673560209437)
            ·
              refine ⟨1136704270894377585078539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031211389051673560209437 1136704270894377585078539)
              ·
                refine ⟨1705056406341566377617809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136704270894377585078539 1705056406341566377617809)
                ·
                  refine ⟨1278792304756174783213357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705056406341566377617809 1278792304756174783213357)
                  ·
                    refine ⟨479547114283565543705009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278792304756174783213357 479547114283565543705009)
                    ·
                      rfl

theorem cell22_1400872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1400872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400872 prefixEnd_1400872 := by exact prefixLift 1400872
  have htrace : WordTrace (prefixWord ++ tailWord_1400872) baseStart_1400872 baseEnd_1400872 := by
    simpa [prefixWord, tailWord_1400872, baseEnd_1400872] using wordTrace_append hprefix tailTrace_1400872
  have hstable : (prefixWord ++ tailWord_1400872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400872).length < 2 ^ (prefixWord ++ tailWord_1400872).sum := by decide
  have hdescent : baseEnd_1400872 < baseStart_1400872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400943 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 1, 4]
def baseStart_1400943 : Nat := 118140960795 + 1400943 * 2 ^ 59
def prefixEnd_1400943 : Nat := 4983230072969 + 3 ^ 40 * 1400943 * 2
def baseEnd_1400943 : Nat := 479571419034545025179791

theorem tailTrace_1400943 : CollatzResearch.WordTrace tailWord_1400943 prefixEnd_1400943 479571419034545025179791 := by
  unfold tailWord_1400943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51096588963630247860887483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34064392642420165240591655 51096588963630247860887483)
  ·
    refine ⟨76644883445445371791331225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51096588963630247860887483 76644883445445371791331225)
    ·
      refine ⟨57483662584084028843498419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76644883445445371791331225 57483662584084028843498419)
      ·
        refine ⟨86225493876126043265247629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57483662584084028843498419 86225493876126043265247629)
        ·
          refine ⟨32334560203547266224467861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86225493876126043265247629 32334560203547266224467861)
          ·
            refine ⟨1515682509541278104271931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32334560203547266224467861 1515682509541278104271931)
            ·
              refine ⟨2273523764311917156407897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515682509541278104271931 2273523764311917156407897)
              ·
                refine ⟨1705142823233937867305923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273523764311917156407897 1705142823233937867305923)
                ·
                  refine ⟨2557714234850906800958885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705142823233937867305923 2557714234850906800958885)
                  ·
                    refine ⟨479571419034545025179791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557714234850906800958885 479571419034545025179791)
                    ·
                      rfl

theorem cell22_1400943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_1400943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400943 prefixEnd_1400943 := by exact prefixLift 1400943
  have htrace : WordTrace (prefixWord ++ tailWord_1400943) baseStart_1400943 baseEnd_1400943 := by
    simpa [prefixWord, tailWord_1400943, baseEnd_1400943] using wordTrace_append hprefix tailTrace_1400943
  have hstable : (prefixWord ++ tailWord_1400943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400943).length < 2 ^ (prefixWord ++ tailWord_1400943).sum := by decide
  have hdescent : baseEnd_1400943 < baseStart_1400943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400956 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_1400956 : Nat := 118140960795 + 1400956 * 2 ^ 59
def prefixEnd_1400956 : Nat := 4983230072969 + 3 ^ 40 * 1400956 * 2
def baseEnd_1400956 : Nat := 479575869200217324604751

theorem tailTrace_1400956 : CollatzResearch.WordTrace tailWord_1400956 prefixEnd_1400956 479575869200217324604751 := by
  unfold tailWord_1400956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25548531556291575540555361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34064708741722100720740481 25548531556291575540555361)
  ·
    refine ⟨19161398667218681655416521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25548531556291575540555361 19161398667218681655416521)
    ·
      refine ⟨14371049000414011241562391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19161398667218681655416521 14371049000414011241562391)
      ·
        refine ⟨21556573500621016862343587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371049000414011241562391 21556573500621016862343587)
        ·
          refine ⟨32334860250931525293515381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21556573500621016862343587 32334860250931525293515381)
          ·
            refine ⟨3031393148524830496267067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32334860250931525293515381 3031393148524830496267067)
            ·
              refine ⟨4547089722787245744400601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031393148524830496267067 4547089722787245744400601)
              ·
                refine ⟨3410317292090434308300451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547089722787245744400601 3410317292090434308300451)
                ·
                  refine ⟨5115475938135651462450677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410317292090434308300451 5115475938135651462450677)
                  ·
                    refine ⟨479575869200217324604751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5115475938135651462450677 479575869200217324604751)
                    ·
                      rfl

theorem cell22_1400956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_1400956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400956 prefixEnd_1400956 := by exact prefixLift 1400956
  have htrace : WordTrace (prefixWord ++ tailWord_1400956) baseStart_1400956 baseEnd_1400956 := by
    simpa [prefixWord, tailWord_1400956, baseEnd_1400956] using wordTrace_append hprefix tailTrace_1400956
  have hstable : (prefixWord ++ tailWord_1400956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400956).length < 2 ^ (prefixWord ++ tailWord_1400956).sum := by decide
  have hdescent : baseEnd_1400956 < baseStart_1400956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400990 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1400990 : Nat := 118140960795 + 1400990 * 2 ^ 59
def prefixEnd_1400990 : Nat := 4983230072969 + 3 ^ 40 * 1400990 * 2
def baseEnd_1400990 : Nat := 479587508095052569254647

theorem tailTrace_1400990 : CollatzResearch.WordTrace tailWord_1400990 prefixEnd_1400990 479587508095052569254647 := by
  unfold tailWord_1400990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387287899307496860981053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34065535462973316591898949 6387287899307496860981053)
  ·
    refine ⟨2395232962240311322867895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6387287899307496860981053 2395232962240311322867895)
    ·
      refine ⟨3592849443360466984301843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395232962240311322867895 3592849443360466984301843)
      ·
        refine ⟨5389274165040700476452765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592849443360466984301843 5389274165040700476452765)
        ·
          refine ⟨2020977811890262678669787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5389274165040700476452765 2020977811890262678669787)
          ·
            refine ⟨3031466717835394018004681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020977811890262678669787 3031466717835394018004681)
            ·
              refine ⟨2273600038376545513503511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3031466717835394018004681 2273600038376545513503511)
              ·
                refine ⟨3410400057564818270255267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273600038376545513503511 3410400057564818270255267)
                ·
                  refine ⟨5115600086347227405382901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410400057564818270255267 5115600086347227405382901)
                  ·
                    refine ⟨479587508095052569254647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5115600086347227405382901 479587508095052569254647)
                    ·
                      rfl

theorem cell22_1400990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1400990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1400990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1400990 prefixEnd_1400990 := by exact prefixLift 1400990
  have htrace : WordTrace (prefixWord ++ tailWord_1400990) baseStart_1400990 baseEnd_1400990 := by
    simpa [prefixWord, tailWord_1400990, baseEnd_1400990] using wordTrace_append hprefix tailTrace_1400990
  have hstable : (prefixWord ++ tailWord_1400990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400990).length < 2 ^ (prefixWord ++ tailWord_1400990).sum := by decide
  have hdescent : baseEnd_1400990 < baseStart_1400990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401005 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1401005 : Nat := 118140960795 + 1401005 * 2 ^ 59
def prefixEnd_1401005 : Nat := 4983230072969 + 3 ^ 40 * 1401005 * 2
def baseEnd_1401005 : Nat := 479592642901597530129601

theorem tailTrace_1401005 : CollatzResearch.WordTrace tailWord_1401005 prefixEnd_1401005 479592642901597530129601 := by
  unfold tailWord_1401005
  simp only [CollatzResearch.WordTrace]
  refine ⟨51098850289405632449644469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34065900192937088299762979 51098850289405632449644469)
  ·
    refine ⟨4790517214631778042154169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51098850289405632449644469 4790517214631778042154169)
    ·
      refine ⟨3592887910973833531615627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4790517214631778042154169 3592887910973833531615627)
      ·
        refine ⟨5389331866460750297423441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592887910973833531615627 5389331866460750297423441)
        ·
          refine ⟨4041998899845562723067581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5389331866460750297423441 4041998899845562723067581)
          ·
            refine ⟨1515749587442086021150343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4041998899845562723067581 1515749587442086021150343)
            ·
              refine ⟨2273624381163129031725515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515749587442086021150343 2273624381163129031725515)
              ·
                refine ⟨3410436571744693547588273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273624381163129031725515 3410436571744693547588273)
                ·
                  refine ⟨2557827428808520160691205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410436571744693547588273 2557827428808520160691205)
                  ·
                    refine ⟨479592642901597530129601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2557827428808520160691205 479592642901597530129601)
                    ·
                      rfl

theorem cell22_1401005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1401005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401005 prefixEnd_1401005 := by exact prefixLift 1401005
  have htrace : WordTrace (prefixWord ++ tailWord_1401005) baseStart_1401005 baseEnd_1401005 := by
    simpa [prefixWord, tailWord_1401005, baseEnd_1401005] using wordTrace_append hprefix tailTrace_1401005
  have hstable : (prefixWord ++ tailWord_1401005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401005).length < 2 ^ (prefixWord ++ tailWord_1401005).sum := by decide
  have hdescent : baseEnd_1401005 < baseStart_1401005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401069 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1401069 : Nat := 118140960795 + 1401069 * 2 ^ 59
def prefixEnd_1401069 : Nat := 4983230072969 + 3 ^ 40 * 1401069 * 2
def baseEnd_1401069 : Nat := 479614551409522696529405

theorem tailTrace_1401069 : CollatzResearch.WordTrace tailWord_1401069 prefixEnd_1401069 479614551409522696529405 := by
  unfold tailWord_1401069
  simp only [CollatzResearch.WordTrace]
  refine ⟨51101184561173771379974261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34067456374115847586649507 51101184561173771379974261)
  ·
    refine ⟨4790736052610041066872587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51101184561173771379974261 4790736052610041066872587)
    ·
      refine ⟨7186104078915061600308881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790736052610041066872587 7186104078915061600308881)
      ·
        refine ⟨5389578059186296200231661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7186104078915061600308881 5389578059186296200231661)
        ·
          refine ⟨2021091772194861075086873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5389578059186296200231661 2021091772194861075086873)
          ·
            refine ⟨1515818829146145806315155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021091772194861075086873 1515818829146145806315155)
            ·
              refine ⟨2273728243719218709472733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515818829146145806315155 2273728243719218709472733)
              ·
                refine ⟨852648091394707016052275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273728243719218709472733 852648091394707016052275)
                ·
                  refine ⟨1278972137092060524078413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852648091394707016052275 1278972137092060524078413)
                  ·
                    refine ⟨479614551409522696529405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1278972137092060524078413 479614551409522696529405)
                    ·
                      rfl

theorem cell22_1401069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1401069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401069 prefixEnd_1401069 := by exact prefixLift 1401069
  have htrace : WordTrace (prefixWord ++ tailWord_1401069) baseStart_1401069 baseEnd_1401069 := by
    simpa [prefixWord, tailWord_1401069, baseEnd_1401069] using wordTrace_append hprefix tailTrace_1401069
  have hstable : (prefixWord ++ tailWord_1401069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401069).length < 2 ^ (prefixWord ++ tailWord_1401069).sum := by decide
  have hdescent : baseEnd_1401069 < baseStart_1401069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401121 : List Nat := [1, 2, 3, 2, 1, 1, 4, 8]
def baseStart_1401121 : Nat := 118140960795 + 1401121 * 2 ^ 59
def prefixEnd_1401121 : Nat := 4983230072969 + 3 ^ 40 * 1401121 * 2
def baseEnd_1401121 : Nat := 53292483563579099358805

theorem tailTrace_1401121 : CollatzResearch.WordTrace tailWord_1401121 prefixEnd_1401121 53292483563579099358805 := by
  unfold tailWord_1401121
  simp only [CollatzResearch.WordTrace]
  refine ⟨51103081156985384260867217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34068720771323589507244811 51103081156985384260867217)
  ·
    refine ⟨38327310867739038195650413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51103081156985384260867217 38327310867739038195650413)
    ·
      refine ⟨14372741575402139323368905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38327310867739038195650413 14372741575402139323368905)
      ·
        refine ⟨10779556181551604492526679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14372741575402139323368905 10779556181551604492526679)
        ·
          refine ⟨16169334272327406738790019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10779556181551604492526679 16169334272327406738790019)
          ·
            refine ⟨24254001408491110108185029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16169334272327406738790019 24254001408491110108185029)
            ·
              refine ⟨4547625264092083145284693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24254001408491110108185029 4547625264092083145284693)
              ·
                refine ⟨53292483563579099358805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4547625264092083145284693 53292483563579099358805)
                ·
                  rfl

theorem cell22_1401121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 8].length) (baseStart_1401121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401121 prefixEnd_1401121 := by exact prefixLift 1401121
  have htrace : WordTrace (prefixWord ++ tailWord_1401121) baseStart_1401121 baseEnd_1401121 := by
    simpa [prefixWord, tailWord_1401121, baseEnd_1401121] using wordTrace_append hprefix tailTrace_1401121
  have hstable : (prefixWord ++ tailWord_1401121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401121).length < 2 ^ (prefixWord ++ tailWord_1401121).sum := by decide
  have hdescent : baseEnd_1401121 < baseStart_1401121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401123 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_1401123 : Nat := 118140960795 + 1401123 * 2 ^ 59
def prefixEnd_1401123 : Nat := 4983230072969 + 3 ^ 40 * 1401123 * 2
def baseEnd_1401123 : Nat := 479633036713084555679239

theorem tailTrace_1401123 : CollatzResearch.WordTrace tailWord_1401123 prefixEnd_1401123 479633036713084555679239 := by
  unfold tailWord_1401123
  simp only [CollatzResearch.WordTrace]
  refine ⟨51103154102978138602440023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34068769401985425734960015 51103154102978138602440023)
  ·
    refine ⟨76654731154467207903660035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51103154102978138602440023 76654731154467207903660035)
    ·
      refine ⟨114982096731700811855490053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76654731154467207903660035 114982096731700811855490053)
      ·
        refine ⟨21559143137193902222904385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114982096731700811855490053 21559143137193902222904385)
        ·
          refine ⟨16169357352895426667178289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21559143137193902222904385 16169357352895426667178289)
          ·
            refine ⟨12127018014671570000383717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16169357352895426667178289 12127018014671570000383717)
            ·
              refine ⟨2273815877750919375071947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12127018014671570000383717 2273815877750919375071947)
              ·
                refine ⟨3410723816626379062607921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273815877750919375071947 3410723816626379062607921)
                ·
                  refine ⟨2558042862469784296955941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410723816626379062607921 2558042862469784296955941)
                  ·
                    refine ⟨479633036713084555679239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558042862469784296955941 479633036713084555679239)
                    ·
                      rfl

theorem cell22_1401123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_1401123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401123 prefixEnd_1401123 := by exact prefixLift 1401123
  have htrace : WordTrace (prefixWord ++ tailWord_1401123) baseStart_1401123 baseEnd_1401123 := by
    simpa [prefixWord, tailWord_1401123, baseEnd_1401123] using wordTrace_append hprefix tailTrace_1401123
  have hstable : (prefixWord ++ tailWord_1401123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401123).length < 2 ^ (prefixWord ++ tailWord_1401123).sum := by decide
  have hdescent : baseEnd_1401123 < baseStart_1401123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401138 : List Nat := [3, 2, 1, 1, 6, 9]
def baseStart_1401138 : Nat := 118140960795 + 1401138 * 2 ^ 59
def prefixEnd_1401138 : Nat := 4983230072969 + 3 ^ 40 * 1401138 * 2
def baseEnd_1401138 : Nat := 5921458907649747117953

theorem tailTrace_1401138 : CollatzResearch.WordTrace tailWord_1401138 prefixEnd_1401138 5921458907649747117953 := by
  unfold tailWord_1401138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775925299480949041059017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34069134131949197442824045 12775925299480949041059017)
  ·
    refine ⟨9581943974610711780794263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12775925299480949041059017 9581943974610711780794263)
    ·
      refine ⟨14372915961916067671191395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581943974610711780794263 14372915961916067671191395)
      ·
        refine ⟨21559373942874101506787093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372915961916067671191395 21559373942874101506787093)
        ·
          refine ⟨1010595653572223508130645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21559373942874101506787093 1010595653572223508130645)
          ·
            refine ⟨5921458907649747117953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1010595653572223508130645 5921458907649747117953)
            ·
              rfl

theorem cell22_1401138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 9].length) (baseStart_1401138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401138 prefixEnd_1401138 := by exact prefixLift 1401138
  have htrace : WordTrace (prefixWord ++ tailWord_1401138) baseStart_1401138 baseEnd_1401138 := by
    simpa [prefixWord, tailWord_1401138, baseEnd_1401138] using wordTrace_append hprefix tailTrace_1401138
  have hstable : (prefixWord ++ tailWord_1401138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401138).length < 2 ^ (prefixWord ++ tailWord_1401138).sum := by decide
  have hdescent : baseEnd_1401138 < baseStart_1401138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401140 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1401140 : Nat := 118140960795 + 1401140 * 2 ^ 59
def prefixEnd_1401140 : Nat := 4983230072969 + 3 ^ 40 * 1401140 * 2
def baseEnd_1401140 : Nat := 479638856160502178004187

theorem tailTrace_1401140 : CollatzResearch.WordTrace tailWord_1401140 prefixEnd_1401140 479638856160502178004187 := by
  unfold tailWord_1401140
  simp only [CollatzResearch.WordTrace]
  refine ⟨25551887071958275252904437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34069182762611033670539249 25551887071958275252904437)
  ·
    refine ⟨2395489412996088304959791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25551887071958275252904437 2395489412996088304959791)
    ·
      refine ⟨3593234119494132457439687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395489412996088304959791 3593234119494132457439687)
      ·
        refine ⟨5389851179241198686159531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593234119494132457439687 5389851179241198686159531)
        ·
          refine ⟨8084776768861798029239297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389851179241198686159531 8084776768861798029239297)
          ·
            refine ⟨6063582576646348521929473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8084776768861798029239297 6063582576646348521929473)
            ·
              refine ⟨4547686932484761391447105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6063582576646348521929473 4547686932484761391447105)
              ·
                refine ⟨3410765199363571043585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547686932484761391447105 3410765199363571043585329)
                ·
                  refine ⟨2558073899522678282688997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3410765199363571043585329 2558073899522678282688997)
                  ·
                    refine ⟨479638856160502178004187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558073899522678282688997 479638856160502178004187)
                    ·
                      rfl

theorem cell22_1401140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1401140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401140 prefixEnd_1401140 := by exact prefixLift 1401140
  have htrace : WordTrace (prefixWord ++ tailWord_1401140) baseStart_1401140 baseEnd_1401140 := by
    simpa [prefixWord, tailWord_1401140, baseEnd_1401140] using wordTrace_append hprefix tailTrace_1401140
  have hstable : (prefixWord ++ tailWord_1401140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401140).length < 2 ^ (prefixWord ++ tailWord_1401140).sum := by decide
  have hdescent : baseEnd_1401140 < baseStart_1401140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401151 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_1401151 : Nat := 118140960795 + 1401151 * 2 ^ 59
def prefixEnd_1401151 : Nat := 4983230072969 + 3 ^ 40 * 1401151 * 2
def baseEnd_1401151 : Nat := 479642621685301815979153

theorem tailTrace_1401151 : CollatzResearch.WordTrace tailWord_1401151 prefixEnd_1401151 479642621685301815979153 := by
  unfold tailWord_1401151
  simp only [CollatzResearch.WordTrace]
  refine ⟨51104175346876699384459307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34069450231251132922972871 51104175346876699384459307)
  ·
    refine ⟨76656263020315049076688961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51104175346876699384459307 76656263020315049076688961)
    ·
      refine ⟨57492197265236286807516721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76656263020315049076688961 57492197265236286807516721)
      ·
        refine ⟨43119147948927215105637541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57492197265236286807516721 43119147948927215105637541)
        ·
          refine ⟨8084840240423852832307039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43119147948927215105637541 8084840240423852832307039)
          ·
            refine ⟨12127260360635779248460559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8084840240423852832307039 12127260360635779248460559)
            ·
              refine ⟨18190890540953668872690839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12127260360635779248460559 18190890540953668872690839)
              ·
                refine ⟨27286335811430503309036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18190890540953668872690839 27286335811430503309036259)
                ·
                  refine ⟨40929503717145754963554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27286335811430503309036259 40929503717145754963554389)
                  ·
                    refine ⟨479642621685301815979153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40929503717145754963554389 479642621685301815979153)
                    ·
                      rfl

theorem cell22_1401151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_1401151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401151 prefixEnd_1401151 := by exact prefixLift 1401151
  have htrace : WordTrace (prefixWord ++ tailWord_1401151) baseStart_1401151 baseEnd_1401151 := by
    simpa [prefixWord, tailWord_1401151, baseEnd_1401151] using wordTrace_append hprefix tailTrace_1401151
  have hstable : (prefixWord ++ tailWord_1401151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401151).length < 2 ^ (prefixWord ++ tailWord_1401151).sum := by decide
  have hdescent : baseEnd_1401151 < baseStart_1401151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401187 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 1, 3]
def baseStart_1401187 : Nat := 118140960795 + 1401187 * 2 ^ 59
def prefixEnd_1401187 : Nat := 4983230072969 + 3 ^ 40 * 1401187 * 2
def baseEnd_1401187 : Nat := 479654945221009722079043

theorem tailTrace_1401187 : CollatzResearch.WordTrace tailWord_1401187 prefixEnd_1401187 479654945221009722079043 := by
  unfold tailWord_1401187
  simp only [CollatzResearch.WordTrace]
  refine ⟨51105488374746277532769815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34070325583164185021846543 51105488374746277532769815)
  ·
    refine ⟨76658232562119416299154723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51105488374746277532769815 76658232562119416299154723)
    ·
      refine ⟨114987348843179124448732085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76658232562119416299154723 114987348843179124448732085)
      ·
        refine ⟨10780063954048042917068633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114987348843179124448732085 10780063954048042917068633)
        ·
          refine ⟨8085047965536032187801475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780063954048042917068633 8085047965536032187801475)
          ·
            refine ⟨12127571948304048281702213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085047965536032187801475 12127571948304048281702213)
            ·
              refine ⟨2273919740307009052819165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12127571948304048281702213 2273919740307009052819165)
              ·
                refine ⟨852719902615128394807187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273919740307009052819165 852719902615128394807187)
                ·
                  refine ⟨1279079853922692592210781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852719902615128394807187 1279079853922692592210781)
                  ·
                    refine ⟨479654945221009722079043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279079853922692592210781 479654945221009722079043)
                    ·
                      rfl

theorem cell22_1401187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 3].length) (baseStart_1401187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401187 prefixEnd_1401187 := by exact prefixLift 1401187
  have htrace : WordTrace (prefixWord ++ tailWord_1401187) baseStart_1401187 baseEnd_1401187 := by
    simpa [prefixWord, tailWord_1401187, baseEnd_1401187] using wordTrace_append hprefix tailTrace_1401187
  have hstable : (prefixWord ++ tailWord_1401187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401187).length < 2 ^ (prefixWord ++ tailWord_1401187).sum := by decide
  have hdescent : baseEnd_1401187 < baseStart_1401187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401200 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_1401200 : Nat := 118140960795 + 1401200 * 2 ^ 59
def prefixEnd_1401200 : Nat := 4983230072969 + 3 ^ 40 * 1401200 * 2
def baseEnd_1401200 : Nat := 159886465128894007168001

theorem tailTrace_1401200 : CollatzResearch.WordTrace tailWord_1401200 prefixEnd_1401200 159886465128894007168001 := by
  unfold tailWord_1401200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552981261849590376496527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34070641682466120501995369 25552981261849590376496527)
  ·
    refine ⟨38329471892774385564744791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25552981261849590376496527 38329471892774385564744791)
    ·
      refine ⟨57494207839161578347117187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38329471892774385564744791 57494207839161578347117187)
      ·
        refine ⟨86241311758742367520675781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57494207839161578347117187 86241311758742367520675781)
        ·
          refine ⟨16170245954764193910126709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86241311758742367520675781 16170245954764193910126709)
          ·
            refine ⟨1515960558259143179074379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16170245954764193910126709 1515960558259143179074379)
            ·
              refine ⟨2273940837388714768611569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515960558259143179074379 2273940837388714768611569)
              ·
                refine ⟨1705455628041536076458677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273940837388714768611569 1705455628041536076458677)
                ·
                  refine ⟨159886465128894007168001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705455628041536076458677 159886465128894007168001)
                  ·
                    rfl

theorem cell22_1401200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_1401200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401200 prefixEnd_1401200 := by exact prefixLift 1401200
  have htrace : WordTrace (prefixWord ++ tailWord_1401200) baseStart_1401200 baseEnd_1401200 := by
    simpa [prefixWord, tailWord_1401200, baseEnd_1401200] using wordTrace_append hprefix tailTrace_1401200
  have hstable : (prefixWord ++ tailWord_1401200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401200).length < 2 ^ (prefixWord ++ tailWord_1401200).sum := by decide
  have hdescent : baseEnd_1401200 < baseStart_1401200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401217 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 5]
def baseStart_1401217 : Nat := 118140960795 + 1401217 * 2 ^ 59
def prefixEnd_1401217 : Nat := 4983230072969 + 3 ^ 40 * 1401217 * 2
def baseEnd_1401217 : Nat := 159888404944699881276317

theorem tailTrace_1401217 : CollatzResearch.WordTrace tailWord_1401217 prefixEnd_1401217 159888404944699881276317 := by
  unfold tailWord_1401217
  simp only [CollatzResearch.WordTrace]
  refine ⟨51106582564637592656361905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34071055043091728437574603 51106582564637592656361905)
  ·
    refine ⟨38329936923478194492271429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51106582564637592656361905 38329936923478194492271429)
    ·
      refine ⟨7186863173152161467300893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38329936923478194492271429 7186863173152161467300893)
      ·
        refine ⟨2695073689932060550237835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7186863173152161467300893 2695073689932060550237835)
        ·
          refine ⟨4042610534898090825356753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695073689932060550237835 4042610534898090825356753)
          ·
            refine ⟨3031957901173568119017565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042610534898090825356753 3031957901173568119017565)
            ·
              refine ⟨1136984212940088044631587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031957901173568119017565 1136984212940088044631587)
              ·
                refine ⟨1705476319410132066947381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136984212940088044631587 1705476319410132066947381)
                ·
                  refine ⟨159888404944699881276317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705476319410132066947381 159888404944699881276317)
                  ·
                    rfl

theorem cell22_1401217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_1401217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401217 prefixEnd_1401217 := by exact prefixLift 1401217
  have htrace : WordTrace (prefixWord ++ tailWord_1401217) baseStart_1401217 baseEnd_1401217 := by
    simpa [prefixWord, tailWord_1401217, baseEnd_1401217] using wordTrace_append hprefix tailTrace_1401217
  have hstable : (prefixWord ++ tailWord_1401217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401217).length < 2 ^ (prefixWord ++ tailWord_1401217).sum := by decide
  have hdescent : baseEnd_1401217 < baseStart_1401217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401228 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1401228 : Nat := 118140960795 + 1401228 * 2 ^ 59
def prefixEnd_1401228 : Nat := 4983230072969 + 3 ^ 40 * 1401228 * 2
def baseEnd_1401228 : Nat := 159889660119633093934639

theorem tailTrace_1401228 : CollatzResearch.WordTrace tailWord_1401228 prefixEnd_1401228 159889660119633093934639 := by
  unfold tailWord_1401228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25553491883798870767506169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34071322511731827690008225 25553491883798870767506169)
  ·
    refine ⟨19165118912849153075629627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25553491883798870767506169 19165118912849153075629627)
    ·
      refine ⟨28747678369273729613444441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19165118912849153075629627 28747678369273729613444441)
      ·
        refine ⟨21560758776955297210083331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28747678369273729613444441 21560758776955297210083331)
        ·
          refine ⟨32341138165432945815124997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560758776955297210083331 32341138165432945815124997)
          ·
            refine ⟨6063963406018677340335937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32341138165432945815124997 6063963406018677340335937)
            ·
              refine ⟨4547972554514008005251953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6063963406018677340335937 4547972554514008005251953)
              ·
                refine ⟨3410979415885506003938965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547972554514008005251953 3410979415885506003938965)
                ·
                  refine ⟨159889660119633093934639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3410979415885506003938965 159889660119633093934639)
                  ·
                    rfl

theorem cell22_1401228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1401228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401228 prefixEnd_1401228 := by exact prefixLift 1401228
  have htrace : WordTrace (prefixWord ++ tailWord_1401228) baseStart_1401228 baseEnd_1401228 := by
    simpa [prefixWord, tailWord_1401228, baseEnd_1401228] using wordTrace_append hprefix tailTrace_1401228
  have hstable : (prefixWord ++ tailWord_1401228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401228).length < 2 ^ (prefixWord ++ tailWord_1401228).sum := by decide
  have hdescent : baseEnd_1401228 < baseStart_1401228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401260 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_1401260 : Nat := 118140960795 + 1401260 * 2 ^ 59
def prefixEnd_1401260 : Nat := 4983230072969 + 3 ^ 40 * 1401260 * 2
def baseEnd_1401260 : Nat := 479679934612861865003819

theorem tailTrace_1401260 : CollatzResearch.WordTrace tailWord_1401260 prefixEnd_1401260 479679934612861865003819 := by
  unfold tailWord_1401260
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554075451740905500088617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34072100602321207333451489 25554075451740905500088617)
  ·
    refine ⟨19165556588805679125066463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25554075451740905500088617 19165556588805679125066463)
    ·
      refine ⟨28748334883208518687599695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19165556588805679125066463 28748334883208518687599695)
      ·
        refine ⟨43122502324812778031399543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748334883208518687599695 43122502324812778031399543)
        ·
          refine ⟨64683753487219167047099315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43122502324812778031399543 64683753487219167047099315)
          ·
            refine ⟨97025630230828750570648973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64683753487219167047099315 97025630230828750570648973)
            ·
              refine ⟨36384611336560781463993365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97025630230828750570648973 36384611336560781463993365)
              ·
                refine ⟨1705528656401286631124689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36384611336560781463993365 1705528656401286631124689)
                ·
                  refine ⟨1279146492300964973343517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705528656401286631124689 1279146492300964973343517)
                  ·
                    refine ⟨479679934612861865003819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279146492300964973343517 479679934612861865003819)
                    ·
                      rfl

theorem cell22_1401260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_1401260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401260 prefixEnd_1401260 := by exact prefixLift 1401260
  have htrace : WordTrace (prefixWord ++ tailWord_1401260) baseStart_1401260 baseEnd_1401260 := by
    simpa [prefixWord, tailWord_1401260, baseEnd_1401260] using wordTrace_append hprefix tailTrace_1401260
  have hstable : (prefixWord ++ tailWord_1401260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401260).length < 2 ^ (prefixWord ++ tailWord_1401260).sum := by decide
  have hdescent : baseEnd_1401260 < baseStart_1401260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401268 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1401268 : Nat := 118140960795 + 1401268 * 2 ^ 59
def prefixEnd_1401268 : Nat := 4983230072969 + 3 ^ 40 * 1401268 * 2
def baseEnd_1401268 : Nat := 159894224392117503601265

theorem tailTrace_1401268 : CollatzResearch.WordTrace tailWord_1401268 prefixEnd_1401268 159894224392117503601265 := by
  unfold tailWord_1401268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554221343726414183234229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34072295124968552244312305 25554221343726414183234229)
  ·
    refine ⟨2395708250974351329678209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25554221343726414183234229 2395708250974351329678209)
    ·
      refine ⟨1796781188230763497258657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2395708250974351329678209 1796781188230763497258657)
      ·
        refine ⟨1347585891173072622943993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1796781188230763497258657 1347585891173072622943993)
        ·
          refine ⟨1010689418379804467207995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347585891173072622943993 1010689418379804467207995)
          ·
            refine ⟨1516034127569706700811993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010689418379804467207995 1516034127569706700811993)
            ·
              refine ⟨1137025595677280025608995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516034127569706700811993 1137025595677280025608995)
              ·
                refine ⟨1705538393515920038413493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137025595677280025608995 1705538393515920038413493)
                ·
                  refine ⟨159894224392117503601265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705538393515920038413493 159894224392117503601265)
                  ·
                    rfl

theorem cell22_1401268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1401268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401268 prefixEnd_1401268 := by exact prefixLift 1401268
  have htrace : WordTrace (prefixWord ++ tailWord_1401268) baseStart_1401268 baseEnd_1401268 := by
    simpa [prefixWord, tailWord_1401268, baseEnd_1401268] using wordTrace_append hprefix tailTrace_1401268
  have hstable : (prefixWord ++ tailWord_1401268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401268).length < 2 ^ (prefixWord ++ tailWord_1401268).sum := by decide
  have hdescent : baseEnd_1401268 < baseStart_1401268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401273 : List Nat := [1, 2, 1, 4, 3, 1, 1, 9]
def baseStart_1401273 : Nat := 118140960795 + 1401273 * 2 ^ 59
def prefixEnd_1401273 : Nat := 4983230072969 + 3 ^ 40 * 1401273 * 2
def baseEnd_1401273 : Nat := 53298264975392684936531

theorem tailTrace_1401273 : CollatzResearch.WordTrace tailWord_1401273 prefixEnd_1401273 53298264975392684936531 := by
  unfold tailWord_1401273
  simp only [CollatzResearch.WordTrace]
  refine ⟨51108625052434714220400473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34072416701623142813600315 51108625052434714220400473)
  ·
    refine ⟨38331468789326035665300355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51108625052434714220400473 38331468789326035665300355)
    ·
      refine ⟨57497203183989053497950533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38331468789326035665300355 57497203183989053497950533)
      ·
        refine ⟨10780725596997947530865725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57497203183989053497950533 10780725596997947530865725)
        ·
          refine ⟨4042772098874230324074647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10780725596997947530865725 4042772098874230324074647)
          ·
            refine ⟨6064158148311345486111971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042772098874230324074647 6064158148311345486111971)
            ·
              refine ⟨9096237222467018229167957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064158148311345486111971 9096237222467018229167957)
              ·
                refine ⟨53298264975392684936531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9096237222467018229167957 53298264975392684936531)
                ·
                  rfl

theorem cell22_1401273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 9].length) (baseStart_1401273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401273 prefixEnd_1401273 := by exact prefixLift 1401273
  have htrace : WordTrace (prefixWord ++ tailWord_1401273) baseStart_1401273 baseEnd_1401273 := by
    simpa [prefixWord, tailWord_1401273, baseEnd_1401273] using wordTrace_append hprefix tailTrace_1401273
  have hstable : (prefixWord ++ tailWord_1401273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401273).length < 2 ^ (prefixWord ++ tailWord_1401273).sum := by decide
  have hdescent : baseEnd_1401273 < baseStart_1401273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401277 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1401277 : Nat := 118140960795 + 1401277 * 2 ^ 59
def prefixEnd_1401277 : Nat := 4983230072969 + 3 ^ 40 * 1401277 * 2
def baseEnd_1401277 : Nat := 479685754060279487328767

theorem tailTrace_1401277 : CollatzResearch.WordTrace tailWord_1401277 prefixEnd_1401277 479685754060279487328767 := by
  unfold tailWord_1401277
  simp only [CollatzResearch.WordTrace]
  refine ⟨51108770944420222903546085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34072513962946815269030723 51108770944420222903546085)
  ·
    refine ⟨9582894552078791794414891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51108770944420222903546085 9582894552078791794414891)
    ·
      refine ⟨14374341828118187691622337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582894552078791794414891 14374341828118187691622337)
      ·
        refine ⟨10780756371088640768716753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14374341828118187691622337 10780756371088640768716753)
        ·
          refine ⟨8085567278316480576537565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780756371088640768716753 8085567278316480576537565)
          ·
            refine ⟨3032087729368680216201587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8085567278316480576537565 3032087729368680216201587)
            ·
              refine ⟨4548131594053020324302381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032087729368680216201587 4548131594053020324302381)
              ·
                refine ⟨1705549347769882621613393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4548131594053020324302381 1705549347769882621613393)
                ·
                  refine ⟨1279162010827411966210045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705549347769882621613393 1279162010827411966210045)
                  ·
                    refine ⟨479685754060279487328767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279162010827411966210045 479685754060279487328767)
                    ·
                      rfl

theorem cell22_1401277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1401277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401277 prefixEnd_1401277 := by exact prefixLift 1401277
  have htrace : WordTrace (prefixWord ++ tailWord_1401277) baseStart_1401277 baseEnd_1401277 := by
    simpa [prefixWord, tailWord_1401277, baseEnd_1401277] using wordTrace_append hprefix tailTrace_1401277
  have hstable : (prefixWord ++ tailWord_1401277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401277).length < 2 ^ (prefixWord ++ tailWord_1401277).sum := by decide
  have hdescent : baseEnd_1401277 < baseStart_1401277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401292 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_1401292 : Nat := 118140960795 + 1401292 * 2 ^ 59
def prefixEnd_1401292 : Nat := 4983230072969 + 3 ^ 40 * 1401292 * 2
def baseEnd_1401292 : Nat := 479690888866824448203721

theorem tailTrace_1401292 : CollatzResearch.WordTrace tailWord_1401292 prefixEnd_1401292 479690888866824448203721 := by
  unfold tailWord_1401292
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554659019682940232671065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34072878692910586976894753 25554659019682940232671065)
  ·
    refine ⟨19165994264762205174503299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25554659019682940232671065 19165994264762205174503299)
    ·
      refine ⟨28748991397143307761754949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19165994264762205174503299 28748991397143307761754949)
      ·
        refine ⟨5390435886964370205329053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28748991397143307761754949 5390435886964370205329053)
        ·
          refine ⟨2021413457611638826998395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5390435886964370205329053 2021413457611638826998395)
          ·
            refine ⟨3032120186417458240497593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021413457611638826998395 3032120186417458240497593)
            ·
              refine ⟨2274090139813093680373195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032120186417458240497593 2274090139813093680373195)
              ·
                refine ⟨3411135209719640520559793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274090139813093680373195 3411135209719640520559793)
                ·
                  refine ⟨2558351407289730390419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411135209719640520559793 2558351407289730390419845)
                  ·
                    refine ⟨479690888866824448203721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558351407289730390419845 479690888866824448203721)
                    ·
                      rfl

theorem cell22_1401292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_1401292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401292 prefixEnd_1401292 := by exact prefixLift 1401292
  have htrace : WordTrace (prefixWord ++ tailWord_1401292) baseStart_1401292 baseEnd_1401292 := by
    simpa [prefixWord, tailWord_1401292, baseEnd_1401292] using wordTrace_append hprefix tailTrace_1401292
  have hstable : (prefixWord ++ tailWord_1401292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401292).length < 2 ^ (prefixWord ++ tailWord_1401292).sum := by decide
  have hdescent : baseEnd_1401292 < baseStart_1401292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401363 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 8]
def baseStart_1401363 : Nat := 118140960795 + 1401363 * 2 ^ 59
def prefixEnd_1401363 : Nat := 4983230072969 + 3 ^ 40 * 1401363 * 2
def baseEnd_1401363 : Nat := 159905064539267976559501

theorem tailTrace_1401363 : CollatzResearch.WordTrace tailWord_1401363 prefixEnd_1401363 159905064539267976559501 := by
  unfold tailWord_1401363
  simp only [CollatzResearch.WordTrace]
  refine ⟨51111907622108659591176743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34074605081405773060784495 51111907622108659591176743)
  ·
    refine ⟨76667861433162989386765115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51111907622108659591176743 76667861433162989386765115)
    ·
      refine ⟨115001792149744484080147673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76667861433162989386765115 115001792149744484080147673)
      ·
        refine ⟨86251344112308363060110755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115001792149744484080147673 86251344112308363060110755)
        ·
          refine ⟨129377016168462544590166133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86251344112308363060110755 129377016168462544590166133)
          ·
            refine ⟨12129095265793363555328075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129377016168462544590166133 12129095265793363555328075)
            ·
              refine ⟨18193642898690045332992113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12129095265793363555328075 18193642898690045332992113)
              ·
                refine ⟨13645232174017533999744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18193642898690045332992113 13645232174017533999744085)
                ·
                  refine ⟨159905064539267976559501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13645232174017533999744085 159905064539267976559501)
                  ·
                    rfl

theorem cell22_1401363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_1401363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401363 prefixEnd_1401363 := by exact prefixLift 1401363
  have htrace : WordTrace (prefixWord ++ tailWord_1401363) baseStart_1401363 baseEnd_1401363 := by
    simpa [prefixWord, tailWord_1401363, baseEnd_1401363] using wordTrace_append hprefix tailTrace_1401363
  have hstable : (prefixWord ++ tailWord_1401363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401363).length < 2 ^ (prefixWord ++ tailWord_1401363).sum := by decide
  have hdescent : baseEnd_1401363 < baseStart_1401363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401425 : List Nat := [1, 2, 2, 1, 3, 5, 8]
def baseStart_1401425 : Nat := 118140960795 + 1401425 * 2 ^ 59
def prefixEnd_1401425 : Nat := 4983230072969 + 3 ^ 40 * 1401425 * 2
def baseEnd_1401425 : Nat := 17768015462402090171419

theorem tailTrace_1401425 : CollatzResearch.WordTrace tailWord_1401425 prefixEnd_1401425 17768015462402090171419 := by
  unfold tailWord_1401425
  simp only [CollatzResearch.WordTrace]
  refine ⟨51114168947884044179933729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34076112631922696119955819 51114168947884044179933729)
  ·
    refine ⟨38335626710913033134950297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51114168947884044179933729 38335626710913033134950297)
    ·
      refine ⟨28751720033184774851212723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38335626710913033134950297 28751720033184774851212723)
      ·
        refine ⟨43127580049777162276819085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28751720033184774851212723 43127580049777162276819085)
        ·
          refine ⟨16172842518666435853807157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43127580049777162276819085 16172842518666435853807157)
          ·
            refine ⟨1516203986124978361294421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16172842518666435853807157 1516203986124978361294421)
            ·
              refine ⟨17768015462402090171419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1516203986124978361294421 17768015462402090171419)
              ·
                rfl

theorem cell22_1401425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 8].length) (baseStart_1401425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401425 prefixEnd_1401425 := by exact prefixLift 1401425
  have htrace : WordTrace (prefixWord ++ tailWord_1401425) baseStart_1401425 baseEnd_1401425 := by
    simpa [prefixWord, tailWord_1401425, baseEnd_1401425] using wordTrace_append hprefix tailTrace_1401425
  have hstable : (prefixWord ++ tailWord_1401425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401425).length < 2 ^ (prefixWord ++ tailWord_1401425).sum := by decide
  have hdescent : baseEnd_1401425 < baseStart_1401425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401534 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1401534 : Nat := 118140960795 + 1401534 * 2 ^ 59
def prefixEnd_1401534 : Nat := 4983230072969 + 3 ^ 40 * 1401534 * 2
def baseEnd_1401534 : Nat := 479773730412416483652979

theorem tailTrace_1401534 : CollatzResearch.WordTrace tailWord_1401534 prefixEnd_1401534 479773730412416483652979 := by
  unfold tailWord_1401534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389768063061144474456457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34078763002992770530434437 6389768063061144474456457)
  ·
    refine ⟨4792326047295858355842343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6389768063061144474456457 4792326047295858355842343)
    ·
      refine ⟨7188489070943787533763515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4792326047295858355842343 7188489070943787533763515)
      ·
        refine ⟨10782733606415681300645273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188489070943787533763515 10782733606415681300645273)
        ·
          refine ⟨8087050204811760975483955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10782733606415681300645273 8087050204811760975483955)
          ·
            refine ⟨12130575307217641463225933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087050204811760975483955 12130575307217641463225933)
            ·
              refine ⟨4548965740206615548709725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12130575307217641463225933 4548965740206615548709725)
              ·
                refine ⟨1705862152577480830766147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4548965740206615548709725 1705862152577480830766147)
                ·
                  refine ⟨2558793228866221246149221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705862152577480830766147 2558793228866221246149221)
                  ·
                    refine ⟨479773730412416483652979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558793228866221246149221 479773730412416483652979)
                    ·
                      rfl

theorem cell22_1401534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1401534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401534 prefixEnd_1401534 := by exact prefixLift 1401534
  have htrace : WordTrace (prefixWord ++ tailWord_1401534) baseStart_1401534 baseEnd_1401534 := by
    simpa [prefixWord, tailWord_1401534, baseEnd_1401534] using wordTrace_append hprefix tailTrace_1401534
  have hstable : (prefixWord ++ tailWord_1401534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401534).length < 2 ^ (prefixWord ++ tailWord_1401534).sum := by decide
  have hdescent : baseEnd_1401534 < baseStart_1401534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401577 : List Nat := [1, 2, 1, 1, 1, 2, 8, 6]
def baseStart_1401577 : Nat := 118140960795 + 1401577 * 2 ^ 59
def prefixEnd_1401577 : Nat := 4983230072969 + 3 ^ 40 * 1401577 * 2
def baseEnd_1401577 : Nat := 53309827799019856091983

theorem tailTrace_1401577 : CollatzResearch.WordTrace tailWord_1401577 prefixEnd_1401577 53309827799019856091983 := by
  unfold tailWord_1401577
  simp only [CollatzResearch.WordTrace]
  refine ⟨51119712843333374139466985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34079808562222249426311323 51119712843333374139466985)
  ·
    refine ⟨38339784632500030604600239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51119712843333374139466985 38339784632500030604600239)
    ·
      refine ⟨57509676948750045906900359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38339784632500030604600239 57509676948750045906900359)
      ·
        refine ⟨86264515423125068860350539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57509676948750045906900359 86264515423125068860350539)
        ·
          refine ⟨129396773134687603290525809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86264515423125068860350539 129396773134687603290525809)
          ·
            refine ⟨97047579851015702467894357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129396773134687603290525809 97047579851015702467894357)
            ·
              refine ⟨1137276326379090263295637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97047579851015702467894357 1137276326379090263295637)
              ·
                refine ⟨53309827799019856091983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1137276326379090263295637 53309827799019856091983)
                ·
                  rfl

theorem cell22_1401577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 6].length) (baseStart_1401577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401577 prefixEnd_1401577 := by exact prefixLift 1401577
  have htrace : WordTrace (prefixWord ++ tailWord_1401577) baseStart_1401577 baseEnd_1401577 := by
    simpa [prefixWord, tailWord_1401577, baseEnd_1401577] using wordTrace_append hprefix tailTrace_1401577
  have hstable : (prefixWord ++ tailWord_1401577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401577).length < 2 ^ (prefixWord ++ tailWord_1401577).sum := by decide
  have hdescent : baseEnd_1401577 < baseStart_1401577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401609 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_1401609 : Nat := 118140960795 + 1401609 * 2 ^ 59
def prefixEnd_1401609 : Nat := 4983230072969 + 3 ^ 40 * 1401609 * 2
def baseEnd_1401609 : Nat := 479799404445141288027749

theorem tailTrace_1401609 : CollatzResearch.WordTrace tailWord_1401609 prefixEnd_1401609 479799404445141288027749 := by
  unfold tailWord_1401609
  simp only [CollatzResearch.WordTrace]
  refine ⟨51120879979217443604631881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34080586652811629069754587 51120879979217443604631881)
  ·
    refine ⟨38340659984413082703473911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51120879979217443604631881 38340659984413082703473911)
    ·
      refine ⟨57510989976619624055210867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38340659984413082703473911 57510989976619624055210867)
      ·
        refine ⟨86266484964929436082816301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57510989976619624055210867 86266484964929436082816301)
        ·
          refine ⟨32349931861848538531056113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86266484964929436082816301 32349931861848538531056113)
          ·
            refine ⟨24262448896386403898292085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32349931861848538531056113 24262448896386403898292085)
            ·
              refine ⟨2274604584036225365464883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24262448896386403898292085 2274604584036225365464883)
              ·
                refine ⟨3411906876054338048197325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274604584036225365464883 3411906876054338048197325)
                ·
                  refine ⟨1279465078520376768073997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3411906876054338048197325 1279465078520376768073997)
                  ·
                    refine ⟨479799404445141288027749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1279465078520376768073997 479799404445141288027749)
                    ·
                      rfl

theorem cell22_1401609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_1401609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401609 prefixEnd_1401609 := by exact prefixLift 1401609
  have htrace : WordTrace (prefixWord ++ tailWord_1401609) baseStart_1401609 baseEnd_1401609 := by
    simpa [prefixWord, tailWord_1401609, baseEnd_1401609] using wordTrace_append hprefix tailTrace_1401609
  have hstable : (prefixWord ++ tailWord_1401609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401609).length < 2 ^ (prefixWord ++ tailWord_1401609).sum := by decide
  have hdescent : baseEnd_1401609 < baseStart_1401609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401667 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 6]
def baseStart_1401667 : Nat := 118140960795 + 1401667 * 2 ^ 59
def prefixEnd_1401667 : Nat := 4983230072969 + 3 ^ 40 * 1401667 * 2
def baseEnd_1401667 : Nat := 159939753010149490025857

theorem tailTrace_1401667 : CollatzResearch.WordTrace tailWord_1401667 prefixEnd_1401667 159939753010149490025857 := by
  unfold tailWord_1401667
  simp only [CollatzResearch.WordTrace]
  refine ⟨51122995413007319510243255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34081996942004879673495503 51122995413007319510243255)
  ·
    refine ⟨76684493119510979265364883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51122995413007319510243255 76684493119510979265364883)
    ·
      refine ⟨115026739679266468898047325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76684493119510979265364883 115026739679266468898047325)
      ·
        refine ⟨43135027379724925836767747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115026739679266468898047325 43135027379724925836767747)
        ·
          refine ⟨64702541069587388755151621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43135027379724925836767747 64702541069587388755151621)
          ·
            refine ⟨12131726450547635391590929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64702541069587388755151621 12131726450547635391590929)
            ·
              refine ⟨9098794837910726543693197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12131726450547635391590929 9098794837910726543693197)
              ·
                refine ⟨3412048064216522453884949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9098794837910726543693197 3412048064216522453884949)
                ·
                  refine ⟨159939753010149490025857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3412048064216522453884949 159939753010149490025857)
                  ·
                    rfl

theorem cell22_1401667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_1401667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401667 prefixEnd_1401667 := by exact prefixLift 1401667
  have htrace : WordTrace (prefixWord ++ tailWord_1401667) baseStart_1401667 baseEnd_1401667 := by
    simpa [prefixWord, tailWord_1401667, baseEnd_1401667] using wordTrace_append hprefix tailTrace_1401667
  have hstable : (prefixWord ++ tailWord_1401667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401667).length < 2 ^ (prefixWord ++ tailWord_1401667).sum := by decide
  have hdescent : baseEnd_1401667 < baseStart_1401667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401699 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_1401699 : Nat := 118140960795 + 1401699 * 2 ^ 59
def prefixEnd_1401699 : Nat := 4983230072969 + 3 ^ 40 * 1401699 * 2
def baseEnd_1401699 : Nat := 479830213284411053277473

theorem tailTrace_1401699 : CollatzResearch.WordTrace tailWord_1401699 prefixEnd_1401699 479830213284411053277473 := by
  unfold tailWord_1401699
  simp only [CollatzResearch.WordTrace]
  refine ⟨51124162548891388975408151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34082775032594259316938767 51124162548891388975408151)
  ·
    refine ⟨76686243823337083463112227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51124162548891388975408151 76686243823337083463112227)
    ·
      refine ⟨115029365735005625194668341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76686243823337083463112227 115029365735005625194668341)
      ·
        refine ⟨10784003037656777362000157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115029365735005625194668341 10784003037656777362000157)
        ·
          refine ⟨4044001139121291510750059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10784003037656777362000157 4044001139121291510750059)
          ·
            refine ⟨6066001708681937266125089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044001139121291510750059 6066001708681937266125089)
            ·
              refine ⟨4549501281511452949593817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066001708681937266125089 4549501281511452949593817)
              ·
                refine ⟨3412125961133589712195363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549501281511452949593817 3412125961133589712195363)
                ·
                  refine ⟨5118188941700384568293045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412125961133589712195363 5118188941700384568293045)
                  ·
                    refine ⟨479830213284411053277473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5118188941700384568293045 479830213284411053277473)
                    ·
                      rfl

theorem cell22_1401699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_1401699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401699 prefixEnd_1401699 := by exact prefixLift 1401699
  have htrace : WordTrace (prefixWord ++ tailWord_1401699) baseStart_1401699 baseEnd_1401699 := by
    simpa [prefixWord, tailWord_1401699, baseEnd_1401699] using wordTrace_append hprefix tailTrace_1401699
  have hstable : (prefixWord ++ tailWord_1401699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401699).length < 2 ^ (prefixWord ++ tailWord_1401699).sum := by decide
  have hdescent : baseEnd_1401699 < baseStart_1401699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401703 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1401703 : Nat := 118140960795 + 1401703 * 2 ^ 59
def prefixEnd_1401703 : Nat := 4983230072969 + 3 ^ 40 * 1401703 * 2
def baseEnd_1401703 : Nat := 479831582566156376177461

theorem tailTrace_1401703 : CollatzResearch.WordTrace tailWord_1401703 prefixEnd_1401703 479831582566156376177461 := by
  unfold tailWord_1401703
  simp only [CollatzResearch.WordTrace]
  refine ⟨51124308440876897658553763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34082872293917931772369175 51124308440876897658553763)
  ·
    refine ⟨76686462661315346487830645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51124308440876897658553763 76686462661315346487830645)
    ·
      refine ⟨7189355874498313733234123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76686462661315346487830645 7189355874498313733234123)
      ·
        refine ⟨10784033811747470599851185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189355874498313733234123 10784033811747470599851185)
        ·
          refine ⟨8088025358810602949888389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784033811747470599851185 8088025358810602949888389)
          ·
            refine ⟨1516504754776988053104073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8088025358810602949888389 1516504754776988053104073)
            ·
              refine ⟨1137378566082741039828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516504754776988053104073 1137378566082741039828055)
              ·
                refine ⟨1706067849124111559742083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137378566082741039828055 1706067849124111559742083)
                ·
                  refine ⟨2559101773686167339613125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706067849124111559742083 2559101773686167339613125)
                  ·
                    refine ⟨479831582566156376177461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559101773686167339613125 479831582566156376177461)
                    ·
                      rfl

theorem cell22_1401703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1401703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1401703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1401703 prefixEnd_1401703 := by exact prefixLift 1401703
  have htrace : WordTrace (prefixWord ++ tailWord_1401703) baseStart_1401703 baseEnd_1401703 := by
    simpa [prefixWord, tailWord_1401703, baseEnd_1401703] using wordTrace_append hprefix tailTrace_1401703
  have hstable : (prefixWord ++ tailWord_1401703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401703).length < 2 ^ (prefixWord ++ tailWord_1401703).sum := by decide
  have hdescent : baseEnd_1401703 < baseStart_1401703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
